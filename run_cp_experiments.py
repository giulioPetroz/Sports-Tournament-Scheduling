import subprocess
import json
import time
import os

# === SETTINGS ===

MODELS = [
    ("cp_complete", "CP/cp_complete.mzn"),
    # ("cp_nosymmetry", "CP/cp_nosymmetry.mzn")
    # Add more models here if needed
]

SOLVERS = ["gecode", "chuffed"]
n_list = [6, 8, 10, 12, 14, 16, 18, 20]

output_dir = "res/CP"
os.makedirs(output_dir, exist_ok=True)

# === MAIN LOOP ===

for n in n_list:
    combined_data = {}

    for model_name, model_path in MODELS:
        for solver in SOLVERS:
            print(f"Running n={n}, model={model_name}, solver={solver}...")

            start = time.time()
            result = subprocess.run(
                ["minizinc", "--solver", solver, model_path, "--time-limit", "300000", "-D", f"n={n}"],
                capture_output=True, text=True
            )
            end = time.time()
            runtime = end - start
            floored_runtime = int(runtime)

            output = result.stdout
            lines = output.strip().split(";")

            max_imbalance = None
            matches_list = []
            home_away_list = []
            rb_list = []

            for line in lines:
                if "max_imbalance=" in line:
                    max_imbalance = int(line.strip().split("=")[1])
                elif "matches=" in line:
                    part = line.split("=")[1].strip().replace("[", "").replace("]", "")
                    matches_list = [int(x) for x in part.split(",") if x.strip()]
                elif "home_away=" in line:
                    part = line.split("=")[1].strip().replace("[", "").replace("]", "")
                    home_away_list = [int(x) for x in part.split(",") if x.strip()]
                elif "rb=" in line:
                    part = line.split("=")[1].strip().replace("[", "").replace("]", "")
                    rb_list = [int(x) for x in part.split(",") if x.strip()]

            # If no valid output, mark as timeout (time = 300, optimal = false)
            if max_imbalance is None or not matches_list or not home_away_list or not rb_list:
                print(f"[n={n}] WARNING: {model_name} with {solver} did not return valid output. Marking as timeout.")
                entry = {
                    "time": 300,
                    "optimal": False,
                    "obj": None,
                    "sol": []
                }
            else:
                P = n // 2
                W = n - 1

                sol = []
                for p in range(P):
                    row = []
                    for w in range(W):
                        idx = matches_list[p * W + w]
                        ha = home_away_list[p * W + w]

                        team1 = rb_list[idx * W * 2 + w * 2 + 0]
                        team2 = rb_list[idx * W * 2 + w * 2 + 1]

                        if ha == 0:
                            home = team1
                            away = team2
                        else:
                            home = team2
                            away = team1

                        row.append([home + 1, away + 1])
                    sol.append(row)

                entry = {
                    "time": floored_runtime if max_imbalance == 1 else 300 if floored_runtime < 300 else floored_runtime,
                    "optimal": max_imbalance == 1,
                    "obj": max_imbalance,
                    "sol": sol
                }

            key_name = f"{model_name}_{solver}"
            combined_data[key_name] = entry

            print(f"[n={n}] {key_name} Done. Time: {floored_runtime}s, Obj: {max_imbalance}, Optimal: {entry['optimal']}")

    # === SAVE JSON FILE FOR THIS n ===
    json_path = os.path.join(output_dir, f"{n}.json")
    with open(json_path, "w") as f:
        json.dump(combined_data, f, indent=4)

    print(f"[n={n}] All results saved to {json_path} ✅")
