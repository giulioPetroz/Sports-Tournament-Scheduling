#!/usr/bin/env python3
import os
import sys
import re
import time
import json
import argparse
import subprocess

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
sys.path.insert(0, ROOT)

import solution_checker

# ==== GLOBAL CONFIG ====
GLOBAL_TIMEOUT = 300.0  # overall timeout in seconds

SOLVERS = {
    "z3": {
        "cmd":     "z3",
        "timeout": lambda t: ["-T:" + str(int(t))],
        "model":   []
    },
    "cvc5": {
    "cmd":     "cvc5",
    "timeout": lambda t: ["--tlimit=" + str(int(t*1000))],
    "model":   ["--produce-models"]
    }   

}

def run_solver(name, smtfile, timeout_s):
    """Run solver `name` on `smtfile` with `timeout_s` seconds left."""
    s = SOLVERS[name]
    cmd = [s["cmd"]] + s["timeout"](timeout_s) + s["model"] + [smtfile]
    start = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.stdout, time.time() - start

def imbalance_of(S, t):
    """Compute |#home_t - #away_t| in solution S."""
    P, W = len(S), len(S[0])
    home = sum(1 for p in range(P) for w in range(W) if S[p][w][0] == t)
    away = sum(1 for p in range(P) for w in range(W) if S[p][w][1] == t)
    return abs(home - away)

# ==== PHASE 1 ====

def phase1_generate_smt2(n, fname):
    P, W = n // 2, n - 1

    # Berger pairs
    rb = []
    for p in range(P):
        week = []
        for w in range(W):
            if p == 0:
                pair = (n, w + 1)
            else:
                pair = (((p + w) % (n - 1)) + 1, ((n - p + w - 1) % (n - 1)) + 1)
            week.append(tuple(sorted(pair)))
        rb.append(week)

    # Path robusto: source/SMT/smt/
    THIS_DIR = os.path.dirname(__file__)
    smt_folder = os.path.join(THIS_DIR, "smt")
    os.makedirs(smt_folder, exist_ok=True)

    lines = [
        "; phase1: complete schedule",
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)"
    ]

    for p in range(P):
        for w in range(W):
            for t in range(P):
                lines.append(f"(declare-fun index_{p}_{w}_{t} () Bool)")
            lines.append(f"(declare-fun home_{p}_{w} () Int)")
            lines.append(f"(declare-fun away_{p}_{w} () Int)")

    for p in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for t in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")

    for t in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for p in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")

    for p in range(P):
        for w in range(W):
            ors = []
            for t in range(P):
                h, a = rb[t][w]
                ors.append(f"(and index_{p}_{w}_{t} (= home_{p}_{w} {h}) (= away_{p}_{w} {a}))")
            lines.append(f"(assert (or {' '.join(ors)}))")

    for t in range(1, n + 1):
        for p in range(P):
            terms = []
            for w in range(W):
                for i in range(P):
                    h, a = rb[i][w]
                    if h == t or a == t:
                        terms.append(f"(ite index_{p}_{w}_{i} 1 0)")
            if terms:
                lines.append(f"(assert (<= (+ {' '.join(terms)}) 2))")

    lines.append("(assert index_0_0_0)")
    lines += ["(check-sat)", "(get-model)"]

    smtpath = os.path.join(smt_folder, fname)
    with open(smtpath, "w") as f:
        f.write("\n".join(lines))


def phase1_run(n, solver, start_time):
    """
    Run phase1 with chosen solver; return (status, S0, t1).
    """
    fname = f"sts_phase1_{n}.smt2"
    phase1_generate_smt2(n, fname)

    THIS_DIR = os.path.dirname(__file__)
    smt_folder = os.path.join(THIS_DIR, "smt")
    smtpath = os.path.join(smt_folder, fname)

    timeout_left = GLOBAL_TIMEOUT - (time.time() - start_time)
    out, t1 = run_solver(solver, smtpath, timeout_left)
    lines = out.strip().splitlines()
    if not lines or lines[0] != "sat":
        return (lines[0] if lines else "timeout"), None, t1

    # collapse define-fun
    blocks, cur = [], ""
    for L in lines[1:]:
        L=L.strip()
        if L.startswith("(define-fun"):
            if cur: blocks.append(cur)
            cur = L
        else:
            cur += " " + L
    blocks.append(cur)

    pat = re.compile(r"\(define-fun\s+(\S+)\s*\(\)\s*Int\s+(-?\d+)\)")
    vals = {}
    for b in blocks:
        m = pat.match(b)
        if m:
            vals[m.group(1)] = int(m.group(2))

    P, W = n//2, n-1
    S0=[]
    for p in range(P):
        row=[]
        for w in range(W):
            h=vals[f"home_{p}_{w}"]
            a=vals[f"away_{p}_{w}"]
            row.append([h,a])
        S0.append(row)
    return "sat", S0, t1

# ==== PHASE 2 ====

def phase2_generate_smt2(n, S0, k, fname):
    P, W = len(S0), len(S0[0])

    # Path robusto: source/SMT/smt/
    THIS_DIR = os.path.dirname(__file__)
    smt_folder = os.path.join(THIS_DIR, "smt")
    os.makedirs(smt_folder, exist_ok=True)

    lines = [
        "; phase2: flip-only optimization",
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)"
    ]

    for p in range(P):
        for w in range(W):
            lines.append(f"(declare-fun flip_{p}_{w} () Bool)")

    for p in range(P):
        for w in range(W):
            h0, a0 = S0[p][w]
            lines.append(f"(define-fun home_eff_{p}_{w} () Int (ite flip_{p}_{w} {a0} {h0}))")
            lines.append(f"(define-fun away_eff_{p}_{w} () Int (ite flip_{p}_{w} {h0} {a0}))")

    for t in range(1, n + 1):
        H = " ".join(f"(ite (= home_eff_{p}_{w} {t}) 1 0)" for p in range(P) for w in range(W))
        A = " ".join(f"(ite (= away_eff_{p}_{w} {t}) 1 0)" for p in range(P) for w in range(W))
        lines.append(f"(assert (<= (- (+ {H}) (+ {A})) {k}))")
        lines.append(f"(assert (<= (- (+ {A}) (+ {H})) {k}))")

    lines += ["(check-sat)", "(get-model)"]

    smtpath = os.path.join(smt_folder, fname)
    with open(smtpath, "w") as f:
        f.write("\n".join(lines))


def phase2_run(n, S0, solver, start_time):
    """Binary search on k using only flips, with global timeout.
    Se trova k=1 valido si ferma subito.
    """
    k_hi = max(imbalance_of(S0, t) for t in range(1, n+1))
    best, best_k = S0, k_hi
    low, high = 1, k_hi  # Non ha senso testare k=0

    while low <= high and time.time() - start_time < GLOBAL_TIMEOUT:
        mid = (low + high) // 2
        timeout_left = GLOBAL_TIMEOUT - (time.time() - start_time)
        fname = f"sts_phase2_n{n}_k{mid}.smt2"
        phase2_generate_smt2(n, best, mid, fname)

        THIS_DIR = os.path.dirname(__file__)
        smt_folder = os.path.join(THIS_DIR, "smt")
        smtpath = os.path.join(smt_folder, fname)

        out, _ = run_solver(solver, smtpath, timeout_left)
        lines = out.strip().splitlines()

        if lines and lines[0] == "sat":
            # Decodifica i flip trovati
            flips = {}
            for L in lines[1:]:
                m = re.match(r"\(define-fun\s+flip_(\d+)_(\d+).* (true|false)\)", L)
                if m:
                    p, w, val = int(m.group(1)), int(m.group(2)), (m.group(3) == "true")
                    flips[(p, w)] = val

            # Costruisci la nuova soluzione flipata
            P_, W_ = len(best), len(best[0])
            new = []
            for p in range(P_):
                row = []
                for w in range(W_):
                    h0, a0 = best[p][w]
                    row.append([a0, h0] if flips.get((p, w), False) else [h0, a0])
                row = row
                new.append(row)

            best, best_k = new, mid

            # Se abbiamo raggiunto imbalance minimo teorico = 1 fermiamo subito
            if best_k == 1:
                break

            high = mid - 1
        else:
            low = mid + 1

    return best, best_k


# ==== MAIN ====

def solve_and_save(n, solver, start_time):
    elapsed = time.time() - start_time
    header = f"\n=== n = {n}, solver = {solver.upper()} ==="

    if elapsed >= GLOBAL_TIMEOUT:
        print(header)
        print(f"TIMEOUT in {elapsed:.2f}s (before Phase 1)")
        return

    print(header)
    # PHASE 1
    status, S0, t1 = phase1_run(n, solver, start_time)
    if status != "sat":
        if status == "timeout":
            print(f"TIMEOUT")
        else:
            print(f"{status.upper()}")
        return

    print(f"PHASE 1 COMPLETE: valid schedule in {t1:.2f}s")
    elapsed = time.time() - start_time
    if elapsed >= GLOBAL_TIMEOUT:
        print(f"TIMEOUT before Phase 2")
        # qui passa t1 sia come phase1 sia come solver (solo fase 1)
        save_json(n, solver, t1, S0, t1, S0, None, False)
        return

    # PHASE 2
    print(f"Starting Phase 2 (optimization)...")
    Sopt, k_opt = phase2_run(n, S0, solver, start_time)
    total = time.time() - start_time

    if total >= GLOBAL_TIMEOUT:
        print(f"TIMEOUT during Phase 2 after {total:.2f}s")
    else:
        print(f"PHASE 2 COMPLETE: best imbalance k* = {k_opt} in {total:.2f}s")

    # se fase 2 è partita, `total` include anche l'ottimizzazione
    save_json(n, solver, t1, S0, total, Sopt, k_opt, total < GLOBAL_TIMEOUT)



def save_json(n, solver, t1, S0, total, Sopt, k_opt, optimal):
    folder = os.path.join(ROOT, "res", "SMT")
    os.makedirs(folder, exist_ok=True)

    outpath = f"{folder}/{n}.json"

    # Se esiste, carica il JSON attuale
    if os.path.exists(outpath):
        with open(outpath, "r") as f:
            result = json.load(f)
    else:
        result = {}

    # Aggiorna o aggiungi la chiave di questo solver
    if Sopt is not None and k_opt is not None:
        final_sol = {
            "time": min(300, int(total)),
            "optimal": optimal,
            "obj": k_opt,
            "sol": Sopt
        }
    else:
        final_sol = {
            "time": min(300, int(total)),
            "optimal": False,
            "obj": None,
            "sol": S0
        }

    result[solver] = final_sol

    # Salva di nuovo l’intero file
    with open(outpath, "w") as f:
        json.dump(result, f, indent=2)

    print(f"Result saved: {outpath}")






if __name__=="__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--solver", choices=SOLVERS.keys(), default="z3",
                   help="Which SMT solver to use for both phases")
    p.add_argument("-n", type=int, nargs="+", default=[4,6,8,10,12,14,16,18,20,22,24],
                   help="List of n to solve")
    args = p.parse_args()

    start = time.time()
    for n in args.n:
        if time.time() - start >= GLOBAL_TIMEOUT:
            break
        solve_and_save(n, args.solver, start)
