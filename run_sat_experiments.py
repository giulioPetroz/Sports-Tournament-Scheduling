import subprocess


def run_model(n_teams, solvers, timeout):
    """Runs the model.py script with the given parameters"""
    command = [
        "python",
        "source/SAT/model.py",
        "-n",
        str(n_teams),
        "--solvers",
        *solvers,
        "-t",
        str(timeout),
    ]

    result = subprocess.run(
        command,
        capture_output=True,
        text=True,
    )
    return result


min_n = 6
max_n = 22
solvers = [
    "z3",
    "minisat",
    "cadical",
]
timeout_seconds = 300
for n in range(min_n, max_n + 2, 2):
    print(f"\n--- Running for n = {n} ---")

    # Results saved in res/MIP/
    result = run_model(n, solvers, timeout_seconds)
    print(result.stdout)
