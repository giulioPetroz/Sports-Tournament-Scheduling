import json
import os

# === CONFIG ===
N_LIST = [6, 8, 10, 12, 14, 16, 18, 20, 22]
JSON_DIR = "res/CP"

# Model groups
STRATEGIES = {
    "Complete Search": ["cp_baseline", "cp_complete", "cp_noIMPL", "cp_noSB"],
    "Basic Search": ["cp_baseline_basic", "cp_complete_basic", "cp_noIMPL_basic", "cp_noSB_basic"],
    "No Relax & Reconstruct": ["cp_baseline_no_relnrec", "cp_complete_no_relnrec", "cp_noIMPL_no_relnrec", "cp_noSB_no_relnrec"],
}

SOLVERS = ["gecode", "chuffed", "cp-sat"]
MODEL_SHORT = ["bs", "complete", "noIMPL", "noSB"]

# === Load all JSON ===
results = {n: {} for n in N_LIST}

for n in N_LIST:
    json_path = os.path.join(JSON_DIR, f"{n}.json")
    if not os.path.exists(json_path):
        continue

    with open(json_path, "r") as f:
        data = json.load(f)
        results[n] = data

# === Make grouped LaTeX table ===
def make_grouped_table(models, solvers, strategy_name):
    # Main header: n + 3 solver groups
    header_main = ["\\textbf{n}"] + [f"\\multicolumn{{4}}{{c|}}{{\\textbf{{{s.upper()}}}}}" if i < len(solvers)-1 else f"\\multicolumn{{4}}{{c}}{{\\textbf{{{s.upper()}}}}}" for i,s in enumerate(solvers)]
    header_sub = [" "] + MODEL_SHORT * len(solvers)

    rows = []

    for n in N_LIST:
        row = [str(n)]
        for solver in solvers:
            for model, short in zip(models, MODEL_SHORT):
                key = f"{model}_{solver}"
                entry = results[n].get(key)
                if entry and entry.get("optimal") and entry.get("sol"):
                    t = entry.get("time")
                    cell = str(t) if t is not None else "N/A"
                else:
                    cell = "N/A"
                row.append(cell)
        rows.append(row)

    num_cols = 1 + len(solvers) * len(MODEL_SHORT)

    # Start LaTeX table
    latex = "\\begin{table}[htbp]\n"
    latex += "\\centering\n"
    latex += "\\small\n"
    latex += "\\resizebox{\\textwidth}{!}{%\n"
    latex += "\\begin{tabular}{" + "c|" + "c"*4 + "|" + "c"*4 + "|" + "c"*4 + "}\n"
    latex += "\\toprule\n"

    # Main header
    latex += " & ".join(header_main) + " \\\\\n"

    # Cmidrule for each solver group
    idx = 2
    cmidrules = []
    for s in range(len(solvers)):
        a = idx
        b = idx + 3
        cmidrules.append(f"\\cmidrule(lr){{{a}-{b}}}")
        idx += 4
    latex += "".join(cmidrules) + "\n"

    # Sub header
    latex += " & ".join(header_sub) + " \\\\\n"
    latex += "\\midrule\n"

    # Rows
    for row in rows:
        latex += " & ".join(row) + " \\\\\n"

    latex += "\\bottomrule\n"
    latex += "\\end{tabular}%\n"
    latex += "}\n"
    latex += f"\\caption{{CPU time in seconds for \\textit{{{strategy_name}}}}}\n"
    latex += "\\end{table}\n"

    print(f"\n===== LaTeX Table for {strategy_name} =====\n")
    print(latex)
    print("\n===============================\n")

# === Generate tables ===
for strategy, models in STRATEGIES.items():
    make_grouped_table(models, SOLVERS, strategy)
