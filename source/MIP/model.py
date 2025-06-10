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
    default=["CBC"],
    choices=["CBC", "HiGHS", "gurobi", "CPLEX", "SCIP"],
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

teams = range(n)  # Team identifiers
weeks = range(n - 1)  # Week identifiers
periods = range(n // 2)  # Period identifiers


def format_schedule(x):
    schedule = []
    for p in periods:
        period_matchups = []
        for w in weeks:
            for i in teams:
                for j in teams:
                    if value(x[i][j][w][p]) > 0.5 and j != i:
                        period_matchups.append([i + 1, j + 1])
        schedule.append(period_matchups)

    return schedule


result = {}  # holds result for each solver

for solver_id in solvers:
    # Selecting solver
    match solver_id:
        case "CBC":
            solver = PULP_CBC_CMD(timeLimit=timeout)
        case "HiGHS":
            solver = HiGHS(timeLimit=timeout)
        case "gurobi":
            solver = GUROBI_CMD(timeLimit=timeout)
        case "CPLEX":
            solver = CPLEX_CMD(timeLimit=timeout)
        case "SCIP":
            solver = SCIP_CMD(timeLimit=timeout)

    # Model
    prob = LpProblem("STS problem", LpMinimize)

    # Decision variables
    x = LpVariable.dicts(
        "X", indices=(teams, teams, weeks, periods), cat="Binary"
    )  # x[i][j][k][m] = 1 if i plays j in week k and period m, i at home while j away

    # team cannot play itself
    for i in teams:
        for w in weeks:
            for p in periods:
                prob += x[i][i][w][p] == 0

    # Every period in every week has a single match
    for w in weeks:
        for p in periods:
            prob += lpSum([x[i][j][w][p] for i in teams for j in teams if j != i]) == 1

    # Every team plays once a week
    for w in weeks:
        for i in teams:
            prob += (
                lpSum(
                    [
                        x[i][j][w][p] + x[j][i][w][p]
                        for j in teams
                        if j != i
                        for p in periods
                    ]
                )
                == 1
            )

    # Every team plays against every other once
    for i in teams:
        for j in teams:
            if i != j:
                prob += (
                    lpSum(
                        [x[i][j][w][p] + x[j][i][w][p] for w in weeks for p in periods]
                    )
                    == 1
                )

    # Every team plays at most twice in the same period
    for i in teams:
        for p in periods:
            prob += (
                lpSum(
                    [
                        x[i][j][w][p] + x[j][i][w][p]
                        for j in teams
                        if j != i
                        for w in weeks
                    ]
                )
                <= 2
            )

    # Team imbalance score
    team_imbalance = LpVariable.dicts(
        "Imbalance", teams, lowBound=1, upBound=n - 1, cat="Integer"
    )  # team_imbalance[t] > 0 if t plays more at home or more away, = 0 for balance

    team_home_games = {}  # team_home_games[t]: how many games t plays at home
    team_away_games = {}  # team_away_games[t]: how many games t plays away
    for t1 in teams:
        team_home_games[t1] = lpSum(
            [
                x[t1][t2][w][p]
                for t2 in teams
                if t2 != t1
                for w in weeks
                for p in periods
            ]
        )
        team_away_games[t1] = lpSum(
            [
                x[t2][t1][w][p]
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
                "sol": format_schedule(x),
            }
        case "Not optimal":  # No optimality guarantee
            result[solver_id] = {
                "time": timeout,
                "optimal": False,
                "obj": value(prob.objective),
                "sol": format_schedule(x),
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
