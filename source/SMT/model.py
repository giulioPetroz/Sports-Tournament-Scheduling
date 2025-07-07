import os
import sys
import re
import time
import json
import argparse
import subprocess

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
sys.path.insert(0, ROOT)

from solution_checker import check_solution

# ==== GLOBAL CONFIG ====
GLOBAL_TIMEOUT = 300.0 

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

def run_solver(name, smtfile, timeout_s = GLOBAL_TIMEOUT):

    s = SOLVERS[name]
    cmd = [s["cmd"]] + s["timeout"](timeout_s) + s["model"] + [smtfile]
    start = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.stdout, time.time() - start

def imbalance_of(S, t):

    P, W = len(S), len(S[0])
    home = sum(1 for p in range(P) for w in range(W) if S[p][w][0] == t)
    away = sum(1 for p in range(P) for w in range(W) if S[p][w][1] == t)
    return abs(home - away)

# ==== PHASE 1 ====

def phase1_generate_smt2(n, fname):

    THIS_DIR = os.path.dirname(__file__)
    smt_folder = os.path.join(THIS_DIR, "smt")
    os.makedirs(smt_folder, exist_ok=True)

    P, W = n // 2, n - 1
    rb = [] # rb[p][w] holds the (home, away) pair assigned to index t in slot (p,w)
    for p in range(P):
        week = []
        for w in range(W):
            if p == 0:
                pair = (n, w + 1)
            else:
                pair = (((p + w) % (n - 1)) + 1, ((n - p + w - 1) % (n - 1)) + 1)
            week.append(tuple(sorted(pair)))
        rb.append(week)

    # Initialize SMT-LIB script: set logic and model production
    lines = [
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)"
    ]

    # Declare decision variables:
    # For each slot: P periods x W weeks
    # - index_{p,w,t} : Boolean selector for pair t in slot (p,w)
    # - home_{p,w}, away_{p,w} : Integers for the assigned teams
    for p in range(P):
        for w in range(W):
            for t in range(P):
                lines.append(f"(declare-fun index_{p}_{w}_{t} () Bool)")
            lines.append(f"(declare-fun home_{p}_{w} () Int)")
            lines.append(f"(declare-fun away_{p}_{w} () Int)")

    # Each slot must select exactly one pair:
    # Sum over all index_{p,w,t} must be 1
    for p in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for t in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")

    # Each pair must be used exactly once per week:
    # Sum over all slots using pair t must be 1
    for t in range(P):
        for w in range(W):
            terms = " ".join(f"(ite index_{p}_{w}_{t} 1 0)" for p in range(P))
            lines.append(f"(assert (= (+ {terms}) 1))")

    # For each slot, if index_{p,w,t} is true, bind home/away to correct pair
    for p in range(P):
        for w in range(W):
            ors = []
            for t in range(P):
                h, a = rb[t][w]
                ors.append(f"(and index_{p}_{w}_{t} (= home_{p}_{w} {h}) (= away_{p}_{w} {a}))")
            lines.append(f"(assert (or {' '.join(ors)}))")

    # Limit: a team must not appear more than twice in the same period slot across all weeks
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

    # Symmetry breaking: fix the first pair in the first slot to reduce equivalent solutions
    lines.append("(assert index_0_0_0)")

    # Request feasibility and model
    lines += ["(check-sat)", "(get-model)"]

    smtpath = os.path.join(smt_folder, fname)
    with open(smtpath, "w") as f:
        f.write("\n".join(lines))



def phase1_run(n, solver, start_time):

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

    THIS_DIR = os.path.dirname(__file__)
    smt_folder = os.path.join(THIS_DIR, "smt")
    os.makedirs(smt_folder, exist_ok=True)

    # Initialize the SMT-LIB lines: set logic and request models
    lines = [
        "; phase2: flip-only optimization",
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)"
    ]

    # Declare Boolean flip variables for each slot (period p, week w)
    for p in range(P):
        for w in range(W):
            lines.append(f"(declare-fun flip_{p}_{w} () Bool)")

    # Define the effective home and away team for each slot,
    # using an 'ite' expression that swaps home and away if the flip is true
    for p in range(P):
        for w in range(W):
            h0, a0 = S0[p][w]
            lines.append(f"(define-fun home_eff_{p}_{w} () Int (ite flip_{p}_{w} {a0} {h0}))")
            lines.append(f"(define-fun away_eff_{p}_{w} () Int (ite flip_{p}_{w} {h0} {a0}))")

    # For each team t, impose the imbalance constraints:
    # The difference (home games - away games) must be <= k,
    # and the opposite difference (away games - home games) must be <= k.
    for t in range(1, n + 1):
        # Count of matches where team t plays at home or away (after flipping)
        H = " ".join(f"(ite (= home_eff_{p}_{w} {t}) 1 0)"
                     for p in range(P) for w in range(W))
        A = " ".join(f"(ite (= away_eff_{p}_{w} {t}) 1 0)"
                     for p in range(P) for w in range(W))
        # Impose |H - A| <= k
        lines.append(f"(assert (<= (- (+ {H}) (+ {A})) {k}))")
        lines.append(f"(assert (<= (- (+ {A}) (+ {H})) {k}))")

    # Request the solver to find a solution satisfying the constraints
    lines += ["(check-sat)", "(get-model)"]

    # Write the SMT-LIB code to the specified output file
    smtpath = os.path.join(smt_folder, fname)
    with open(smtpath, "w") as f:
        f.write("\n".join(lines))



def phase2_run(n, S0, solver, start_time):

    k_hi = max(imbalance_of(S0, t) for t in range(1, n+1))
    best, best_k = S0, k_hi
    low, high = 1, k_hi 

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
            flips = {}
            for L in lines[1:]:
                m = re.match(r"\(define-fun\s+flip_(\d+)_(\d+).* (true|false)\)", L)
                if m:
                    p, w, val = int(m.group(1)), int(m.group(2)), (m.group(3) == "true")
                    flips[(p, w)] = val

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

            if best_k == 1:
                break

            high = mid - 1
        else:
            low = mid + 1

    return best, best_k


# ==== MAIN ====

def solve_and_save(n, solver):
    start_time = time.time()
    header = f"\n=== n = {n}, solver = {solver.upper()} ==="
    print(header)

    # Phase 1
    status, S0, t1 = phase1_run(n, solver, start_time)
    if status != "sat":
        if status == "timeout":
            print(f"TIMEOUT")
            save_json(n, solver, 300, None, 300, None, None, False)
        else:
            print(f"{status.upper()}")
        return


    # Validate Phase 1
    result = check_solution(S0, None, t1, False)
    if result != 'Valid solution':
        print(f"Phase 1 checker FAILED: {result}")
        return

    elapsed = time.time() - start_time
    if elapsed >= GLOBAL_TIMEOUT:
        print(f"TIMEOUT")
        save_json(n, solver, t1, S0, t1, S0, None, False)
        return

    print(f"PHASE 1 COMPLETE: valid schedule in {t1:.2f}s")
    print(f"Starting Phase 2 (optimization)...")

    Sopt, k_opt = phase2_run(n, S0, solver, start_time)
    total = time.time() - start_time

    # Validate Phase 2
    if Sopt:
        result = check_solution(Sopt, k_opt, total, True)
        if result != 'Valid solution':
            print(f"Phase 2 checker FAILED: {result}")
            return

    if total >= GLOBAL_TIMEOUT:
        print(f"TIMEOUT during Phase 2 after {total:.2f}s")
    else:
        print(f"PHASE 2 COMPLETE: best imbalance k* = {k_opt} in {total:.2f}s")

    save_json(n, solver, t1, S0, total, Sopt, k_opt, total < GLOBAL_TIMEOUT)




def save_json(n, solver, t1, S0, total, Sopt, k_opt, optimal):

    folder = os.path.join(ROOT, "res", "SMT")
    os.makedirs(folder, exist_ok=True)
    outpath = f"{folder}/{n}.json"

    if os.path.exists(outpath):
        with open(outpath, "r") as f:
            result = json.load(f)
    else:
        result = {}

    if Sopt is not None and k_opt is not None:
        final_sol = {
            "time": min(300, int(total)),
            "optimal": optimal,
            "obj": k_opt,
            "sol": Sopt
        }
    else:
        final_sol = {
            "time": 300,
            "optimal": False,
            "obj": None,
            "sol": []
        }


    result[solver] = final_sol

    with open(outpath, "w") as f:
        json.dump(result, f, indent=2)

    print(f"Result saved: {outpath}")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--solver", choices=SOLVERS.keys(), default="z3",
                   help="Which SMT solver to use for both phases")
    p.add_argument("--teams", type=int, nargs="+", default=[4,6,8,10,12,14,16,18,20,22,24],
                   help="List of teams to solve")
    p.add_argument("--time-limit", type=float, default=300.0,
                   help="Global timeout in seconds for solving (default: 300)")

    args = p.parse_args()

    GLOBAL_TIMEOUT = args.time_limit

    start = time.time()
    for n in args.teams:
        solve_and_save(n, args.solver)

