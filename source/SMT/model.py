#!/usr/bin/env python3
import os
import re
import time
import json
import argparse
import subprocess
from solution_checker import check_solution

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
    P, W = n//2, n-1
    # Berger pairs
    rb = []
    for p in range(P):
        week = []
        for w in range(W):
            if p == 0:
                pair = (n, w+1)
            else:
                pair = (((p+w)%(n-1))+1, ((n-p+w-1)%(n-1))+1)
            week.append(tuple(sorted(pair)))
        rb.append(week)

    os.makedirs("smt", exist_ok=True)
    lines = [
        "; phase1: complete schedule",
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)"
    ]
    # declarations
    for p in range(P):
        for w in range(W):
            for t in range(P):
                lines.append(f"(declare-fun index_{p}_{w}_{t} () Bool)")
            lines.append(f"(declare-fun home_{p}_{w} () Int)")
            lines.append(f"(declare-fun away_{p}_{w} () Int)")
    # exactly-one t per slot
    for p in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for t in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")
    # each pair once per week
    for t in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for p in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")
    # bind home/away
    for p in range(P):
        for w in range(W):
            ors = []
            for t in range(P):
                h,a = rb[t][w]
                ors.append(f"(and index_{p}_{w}_{t} (= home_{p}_{w} {h}) (= away_{p}_{w} {a}))")
            lines.append(f"(assert (or {' '.join(ors)}))")
    # period-limit
    for t in range(1, n+1):
        for p in range(P):
            terms=[]
            for w in range(W):
                for i in range(P):
                    h,a = rb[i][w]
                    if h==t or a==t:
                        terms.append(f"(ite index_{p}_{w}_{i} 1 0)")
            if terms:
                lines.append(f"(assert (<= (+ {' '.join(terms)}) 2))")
    # symmetry-break
    lines.append("(assert index_0_0_0)")
    lines += ["(check-sat)", "(get-model)"]
    with open(f"smt/{fname}", "w") as f:
        f.write("\n".join(lines))

def phase1_run(n, solver, start_time):
    """
    Run phase1 with chosen solver; return (status, S0, t1).
    """
    fname = f"sts_phase1_{n}.smt2"
    phase1_generate_smt2(n, fname)
    smtpath = f"smt/{fname}"
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
    os.makedirs("smt", exist_ok=True)
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
            h0,a0 = S0[p][w]
            lines.append(f"(define-fun home_eff_{p}_{w} () Int (ite flip_{p}_{w} {a0} {h0}))")
            lines.append(f"(define-fun away_eff_{p}_{w} () Int (ite flip_{p}_{w} {h0} {a0}))")
    for t in range(1, n+1):
        H = " ".join(f"(ite (= home_eff_{p}_{w} {t}) 1 0)" for p in range(P) for w in range(W))
        A = " ".join(f"(ite (= away_eff_{p}_{w} {t}) 1 0)" for p in range(P) for w in range(W))
        lines.append(f"(assert (<= (- (+ {H}) (+ {A})) {k}))")
        lines.append(f"(assert (<= (- (+ {A}) (+ {H})) {k}))")
    lines += ["(check-sat)", "(get-model)"]
    with open(f"smt/{fname}", "w") as f:
        f.write("\n".join(lines))

def phase2_run(n, S0, solver, start_time):
    """Binary search on k using only flips, with global timeout."""
    k_hi = max(imbalance_of(S0,t) for t in range(1,n+1))
    best, best_k = S0, k_hi
    low, high = 0, k_hi

    while low <= high and time.time() - start_time < GLOBAL_TIMEOUT:
        mid = (low+high)//2
        fname = f"sts_phase2_{solver}_{n}_{mid}.smt2"
        phase2_generate_smt2(n, best, mid, fname)
        timeout_left = GLOBAL_TIMEOUT - (time.time()-start_time)
        out, _ = run_solver(solver, f"smt/{fname}", timeout_left)
        lines = out.strip().splitlines()

        if lines and lines[0]=="sat":
            flips = {}
            for L in lines[1:]:
                m = re.match(r"\(define-fun\s+flip_(\d+)_(\d+).* (true|false)\)", L)
                if m:
                    p,w,val = int(m.group(1)), int(m.group(2)), (m.group(3)=="true")
                    flips[(p,w)] = val
            P_,W_ = len(best), len(best[0])
            new = []
            for p in range(P_):
                row=[]
                for w in range(W_):
                    h0,a0 = best[p][w]
                    row.append([a0,h0] if flips.get((p,w),False) else [h0,a0])
                new.append(row)
            best, best_k = new, mid
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
        print(f"TIMEOUT in {elapsed:.2f}s")
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
    print(f"Valid solution found in {t1:.2f}s. Now optimizing...")

    # PHASE 2
    Sopt, k_opt = phase2_run(n, S0, solver, start_time)
    total = time.time() - start_time
    if total >= GLOBAL_TIMEOUT:
        print(f"TIMEOUT")
        return

    print(f"Optimal imbalance k* = {k_opt} at {total:.2f}s")

    # SAVE JSON
    out = {
        "phase1": {"time": round(t1,2), "sol": S0},
        solver:   {"time": round(total,2), "obj": k_opt, "sol": Sopt}
    }
    os.makedirs("res/SMT", exist_ok=True)
    with open(f"res/SMT/{n}_{solver}.json","w") as f:
        json.dump(out, f, indent=2)
    print(f"Result saved: res/SMT/{n}_{solver}.json")


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
