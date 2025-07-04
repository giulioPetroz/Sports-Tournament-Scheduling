import subprocess
import json
import time
import os

# === SETTINGS ===

MODELS = [
    ("cp_baseline", "source/CP/cp_baseline.mzn"),
    ("cp_complete", "source/CP/cp_complete.mzn"),
    ("cp_noIMPL", "source/CP/cp_noIMPL.mzn"),
    ("cp_noSB", "source/CP/cp_noSB.mzn"),
    ("cp_baseline_basic", "source/CP/cp_baseline_basic.mzn"),
    ("cp_complete_basic", "source/CP/cp_complete_basic.mzn"),
    ("cp_noIMPL_basic", "source/CP/cp_noIMPL_basic.mzn"),
    ("cp_noSB_basic", "source/CP/cp_noSB_basic.mzn"),
    ("cp_baseline_no_relnrec", "source/CP/cp_baseline_norr.mzn"),
    ("cp_complete_no_relnrec", "source/CP/cp_complete_norr.mzn"),
    ("cp_noIMPL_no_relnrec", "source/CP/cp_noIMPL_norr.mzn"),
    ("cp_noSB_no_relnrec", "source/CP/cp_noSB_norr.mzn")
]

SOLVERS = ["gecode", "chuffed", "cp-sat"]
n_list = [6, 8, 10, 12, 14, 16, 18, 20, 22]

output_dir = "res/CP"
os.makedirs(output_dir, exist_ok=True)


# === HELPER FUNCTION ===

def generate_rb(n):
    """Generate the round-robin structure for n teams"""
    P = n // 2
    W = n - 1

    rb = []
    for p in range(P):
        period = []
        for w in range(W):
            if p == 0:
                team1 = n - 1
            else:
                team1 = (p + w) % (n - 1)

            if p == 0:
                team2 = w
            else:
                team2 = (n - p + w - 1) % (n - 1)

            period.append([team1, team2])
        rb.append(period)

    return rb


def parse_matrix(lines, keyword):
    """Extract a 2D matrix from the output given a keyword"""
    matrix = []
    reading = False

    for line in lines:
        line = line.strip()
        if line.startswith(f"{keyword} ="):
            reading = True
            continue
        if reading:
            if line.startswith("|"):
                row_content = line.split(":")[-1].strip()
                row_content = row_content.replace("|", "").replace("];", "").strip()
                if row_content:
                    row_values = [int(x.strip()) for x in row_content.split(",") if x.strip().isdigit()]
                    matrix.append(row_values)
            elif line.startswith("];"):
                break
    return matrix


# === MAIN LOOP ===

# Track which combos have failed
skipped_combos = set()

for n in n_list:
    combined_data = {}

    for model_name, model_path in MODELS:
        for solver in SOLVERS:

            combo_key = f"{model_name}_{solver}"

            if combo_key in skipped_combos:
                print(f"⚠️ Skipping {combo_key} for n={n} because it failed previously.")
                continue

            print(f"▶️ Running n={n}, model={model_name}, solver={solver}...")

            start = time.time()
            result = subprocess.run(
                ["minizinc", "--solver", solver, model_path, "--time-limit", "300000", "-D", f"N={n}"],
                capture_output=True, text=True
            )
            end = time.time()
            runtime = end - start
            floored_runtime = int(runtime)

            output = result.stdout
            lines = output.strip().split("\n")

            max_imbalance = None

            for line in lines:
                if "max_imbalance =" in line:
                    max_imbalance = int(line.split("=")[1].strip().replace(";", ""))

            matches_matrix = parse_matrix(lines, "matches")
            home_away_matrix = parse_matrix(lines, "home_away")

            if max_imbalance is None or not matches_matrix or not home_away_matrix:
                print(f"[n={n}] ❌ {combo_key} did not return valid output → Marking as failed for future.")
                entry = {
                    "time": 300,
                    "optimal": False,
                    "obj": "None",
                    "sol": []
                }
                skipped_combos.add(combo_key)
            else:
                rb = generate_rb(n)
                P = n // 2
                W = n - 1

                sol = []
                for p in range(P):
                    row = []
                    for w in range(W):
                        idx = matches_matrix[p][w]
                        ha = home_away_matrix[p][w]

                        team1, team2 = rb[idx][w][0], rb[idx][w][1]

                        if ha == 0:
                            home = team1
                            away = team2
                        else:
                            home = team2
                            away = team1

                        row.append([home + 1, away + 1])  # 1-indexed
                    sol.append(row)

                entry = {
                    "time": floored_runtime if max_imbalance == 1 else 300 if floored_runtime < 300 else floored_runtime,
                    "optimal": max_imbalance == 1,
                    "obj": max_imbalance,
                    "sol": sol
                }

            combined_data[combo_key] = entry

            print(f"[n={n}] ✅ {combo_key} Done. Time: {floored_runtime}s, Obj: {max_imbalance}, Optimal: {entry['optimal']}")

    json_path = os.path.join(output_dir, f"{n}.json")
    with open(json_path, "w") as f:
        json.dump(combined_data, f, indent=4)

    print(f"[n={n}] 📁 All results saved to {json_path} ✅")
