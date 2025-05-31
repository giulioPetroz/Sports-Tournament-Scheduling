from pulp import *
import argparse
from timeit import default_timer as timer
import json

# Command line parameters
parser = argparse.ArgumentParser(description="STS with MIP")
parser.add_argument("-n", "--teams", type=int, help="Number of teams")
parser.add_argument(
    "--solvers",
    nargs="+",
    type=str,
    default=["cbc"],
    choices=["cbc"],
    help="Solvers chosen to solve instance",
)
parser.add_argument(
    "-t", "--timeout", type=int, default=300, help="Solver timeout in seconds"
)
parser.add_argument("--id", type=str, help="Instance id")

args = parser.parse_args()

n = args.teams  # number of teams
solvers = args.solvers  # List of solver ids
timeout = args.timeout  # Solver timeout
instance_id = args.id  # Instance id

teams = range(n)  # Both team and weekly slots identifiers
weeks = range(n - 1)  # Week identifiers
slots = range(n)  # Slots go from 0 to n - 1 (periods implied by slot ids)
periods = range(n // 2)  # Period identifiers

result = {}  # stores result for each solver

for solver_id in solvers:
    # Selecting solver
    match solver_id:
        case "cbc":
            solver = PULP_CBC_CMD(timeLimit=timeout)

    # Model
    prob = LpProblem("STS problem", LpMinimize)

    # Decision variables
    x = LpVariable.dicts(
        "X", indices=(teams, weeks, slots), cat="Binary"
    )  # x[i][j][k] = 1 if team i plays in slot k in week j, 0 otherwise

    # Auxiliary variables
    b = LpVariable.dicts(
        "B", indices=(teams, teams, weeks, periods), cat="Binary"
    )  # b[i][j][k][m] = 1 if i plays j in week k and period m, i at home while j away

    # Linking variables
    for t1 in teams:
        for t2 in teams:
            if t1 == t2:
                continue  # Skip constraint addition
            for w in weeks:
                for p in periods:
                    # b[t1, t2, w, p] iff x[t1, w, p*2] AND x[t2, w, p*2 + 1]
                    # Linearization: C = C1 /\ C2 becomes b <= b1, b <= b2, b1 + b2 <= b + 1
                    prob += x[t1][w][p * 2] + x[t2][w][p * 2 + 1] <= b[t1][t2][w][p] + 1
                    prob += b[t1][t2][w][p] <= x[t1][w][p * 2]
                    prob += b[t1][t2][w][p] <= x[t2][w][p * 2 + 1]

    # Every team plays once a week
    for t in teams:
        for w in weeks:
            prob += lpSum([x[t][w][s] for s in slots]) == 1

    # Every weekly slot is assigned to a single unique team
    for w in weeks:
        for s in slots:
            prob += lpSum([x[t][w][s] for t in teams]) == 1

    # Every team plays with every other team only once
    for t1 in teams:
        for t2 in range(t1 + 1, n):
            prob += (
                lpSum(
                    [b[t1][t2][w][p] for w in weeks for p in periods]
                    + [b[t2][t1][w][p] for w in weeks for p in periods]
                )
                == 1
            )

    # Every team plays at most twice in the same period over the tournament
    for t in teams:
        for p in periods:  # Periods
            prob += lpSum([x[t][w][s] for w in weeks for s in (p * 2, p * 2 + 1)]) <= 2

    # Team imbalance score
    team_imbalance = LpVariable.dicts(
        "Imbalance", teams, lowBound=1, upBound=n - 1, cat="Integer"
    )  # team_imbalance[t] > 0 if t plays more at home or more away, = 0 for balance

    team_home_games = {}  # team_home_games[t]: how many games t plays at home
    team_away_games = {}  # team_away_games[t]: how many games t plays away
    for t1 in teams:
        team_home_games[t1] = lpSum(
            [
                b[t1][t2][w][p]
                for t2 in teams
                if t2 != t1
                for w in weeks
                for p in periods
            ]
        )
        team_away_games[t1] = lpSum(
            [
                b[t2][t1][w][p]
                for t2 in teams
                if t2 != t1
                for w in weeks
                for p in periods
            ]
        )

    for t in teams:
        # Because the problem is a minimization problem imposing team_imbalance[t] >= max{-x, x} is equivalent to computing abs(x)
        prob += team_imbalance[t] >= team_home_games[t] - team_away_games[t]
        prob += team_imbalance[t] >= team_away_games[t] - team_home_games[t]

    # Objective function: sum of imbalance score of each team
    prob += lpSum([team_imbalance[t] for t in teams])

    # Solve problem
    start = timer()
    prob.solve(solver)
    end = timer()

    # Solution output
    match LpStatus[prob.status]:
        case "Optimal":  # Found optimal solution
            result[solver_id] = {
                "time": int(end - start),
                "optimal": True,
                "obj": value(prob.objective),
                "sol": b,
            }
        case "Not optimal":  # No optimality guarantee
            result[solver_id] = {
                "time": timeout,
                "optimal": False,
                "obj": value(prob.objective),
                "sol": b,
            }
        case "Not Solved":  # Timed out before finding a solution
            result[solver_id] = {
                "time": timeout,
                "optimal": False,
                "obj": None,
                "sol": None,
            }
        case "Infeasible":
            result[solver_id] = {
                "time": int(end - start),
                "optimal": False,
                "obj": None,
                "sol": None,
            }
        case "Unbounded":
            result[solver_id] = {
                "time": int(end - start),
                "optimal": False,
                "obj": "-inf",
                "sol": None,
            }

print(result)
# Storing result
with open("res/MIP/" + instance_id + ".json", "w") as file:
    json.dump(result, file)
