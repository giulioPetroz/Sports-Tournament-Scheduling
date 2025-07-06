import argparse
from solve import solve_optimize, solve_satisfy
from utils import format_solution
import json
from multiprocessing import Pool
from multiprocessing.context import TimeoutError

# Command line parameters
parser = argparse.ArgumentParser(description="STS with SAT")
parser.add_argument("-n", "--teams", type=int, help="Number of teams", required=True)
parser.add_argument(
    "-t",
    "--timeout",
    type=int,
    default=300,
    help="Solver timeout in seconds",
)
parser.add_argument(
    "--solvers",
    nargs="+",
    type=str,
    choices=["z3", "minisat", "cadical"],
    help="Solvers chosen to solve instance",
    required=True,
)

args = parser.parse_args()


n = args.teams  # number of teams
timeout = args.timeout  # Solver timeout
solvers = args.solvers  # list of solvers

teams = range(n)  # Team identifiers
weeks = range(n - 1)  # Week identifiers
periods = range(n // 2)  # Period identifiers

results = {}  # solver (str) -> formatted solution stats

# Round robin tournament of sorted matches (t1,t2),
# where t1 < t2 and t1 plays at home, t2 plays away
rb = []
for p in periods:
    matches = []
    for w in weeks:
        if p == 0:
            matches.append((sorted([n - 1, w])))
        else:
            matches.append((sorted([(p + w) % (n - 1), (n - p + w - 1) % (n - 1)])))
    rb.append(matches)

"""
    Try all solvers passed as arguments.
    Every instance is solved by a subprocess in order to enforce
    the time limit on the process termination rather than the solver itself
    (see documentation for cvc5)
"""
for solver_name in solvers:
    match solver_name:
        case "z3":
            solver_mod_name = "z3"
            solver_params = {}
        case _:  # i.e. minisat, cadical, implemented by cvc5
            solver_mod_name = "cvc5.pythonic"
            solver_params = {
                "sat_backend": [  # set backend sat solver of cvc5
                    "sat-solver",
                    solver_name,
                ],
            }
    # Reset total runtime for solver_name
    total_runtime = 0

    # Find basic schedule without scheduling the slots by calling solve_satisfy
    # using a child process.
    # If the solution isn't found within the time limit, save empty results and
    # try the next solver_name
    with Pool(1) as pool:
        result = pool.apply_async(
            solve_satisfy,
            (rb, n, teams, weeks, periods, solver_mod_name, solver_params),
        )
        try:
            # Wait the child process
            solution = result.get(timeout=timeout)
        except TimeoutError:
            print(f"{solver_name}: Timeout for satisfiability")
            solution = None

    if solution:
        sat_schedule, sat_runtime = solution[0], solution[1]
        print(f"{solver_name}: solve_satisfy in {sat_runtime:.4f}s")

        # Balance the number of times each team plays at home and away starting from
        # the satisfying solution of solve_satisfy using a child process.
        # If the solution isn't found within the time limit, try the next solver_name
        with Pool(1) as pool:
            result = pool.apply_async(
                solve_optimize,
                (
                    sat_schedule,
                    n,
                    teams,
                    weeks,
                    periods,
                    solution,
                    solver_mod_name,
                    solver_params,
                ),
            )
            try:
                # Wait the child process, considering the time remaining
                # from solve_satisfy
                solution = result.get(timeout=timeout - sat_runtime)
            except TimeoutError:
                print(f"{solver_name}: Timeout for optimization")
            else:
                opt_runtime = solution[1]
                print(f"{solver_name}: solve_optimize in {opt_runtime:.4f}s")
                total_runtime += opt_runtime

        total_runtime += sat_runtime

        print(f"{solver_name}: total runtime {total_runtime:.4f}s", end="\n\n")

    # Save results for current solver
    results[solver_name] = format_solution(solution, total_runtime)

# Dump results to n.json, n being the number of teams
if results:
    with open(f"res/SAT/{n}.json", "w") as file:
        json.dump(results, file)
