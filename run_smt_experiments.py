import subprocess

n_values = list(range(4, 25, 2))

solvers = ["z3", "cvc5"]

MAIN_SCRIPT = "source/SMT/model.py"

def run_all():
    for solver in solvers:
        for n in n_values:
            cmd = [
                "python",
                MAIN_SCRIPT,
                "--solver", solver,
                "--teams", str(n),
                "--time-limit", "300.0"
            ]
            try:
                subprocess.run(cmd, check=True)
            except subprocess.CalledProcessError as e:
                print(f"Run failed: {e}")

if __name__ == "__main__":
    run_all()
