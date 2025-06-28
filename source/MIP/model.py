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

# Round robin
week_matchups = []
for w in weeks:
    current_week_games = []
    current_week_games.append(tuple(sorted([n - 1, w])))

    for p in range(1, n // 2):
        team1 = (p + w) % (n - 1)
        team2 = (n - p + w - 1) % (n - 1)
        current_week_games.append(tuple(sorted([team1, team2])))
    week_matchups.append(current_week_games)


def format_schedule(period_assign, home_away_assign, week_matchups, n):
    schedule = []
    for p in range(n // 2):
        period_games = []
        for w in range(n - 1):
            week_game = None
            for g in range(n // 2):
                if value(period_assign[w][p][g]) > 0.5:
                    i, j = week_matchups[w][g]
                    if value(home_away_assign[w][g]) > 0.5:
                        week_game = [j + 1, i + 1]
                    else:
                        week_game = [i + 1, j + 1]

            period_games.append(week_game)

        schedule.append(period_games)
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
            solver = CPLEX_CMD(
                path="/opt/ibm/ILOG/CPLEX_Studio_Community2212/cplex/bin/x86-64_linux/cplex",
                timeLimit=timeout,
            )
        case "SCIP":
            solver = SCIP_CMD(timeLimit=timeout)

    # Model
    prob = LpProblem("STS problem", LpMinimize)

    # Decision variables
    period_assign = LpVariable.dicts(
        "PeriodAssignment", indices=(weeks, periods, periods), cat="Binary"
    )  # period_assign[i, j, k] == 1 if in week i period j the game in position k in week_matchups is played out

    home_away_assign = LpVariable.dicts(
        "HomeAwayAssignment", indices=(weeks, periods), cat="Binary"
    )  # For (i, j) in week_matchups[week, game_index], value 0 for i vs j and value 1 for j vs i

    # Constraints

    # Each period is assigned one game per week
    for w in weeks:
        for p in periods:
            prob += lpSum([period_assign[w][p][g] for g in periods]) == 1

    # Each game is assigned to one period
    for w in weeks:
        for g in periods:
            prob += lpSum([period_assign[w][p][g] for p in periods]) == 1

    # Auxiliary variables
    team_home_games = LpVariable.dicts(
        "HomeGamesCount", (teams), lowBound=0, upBound=n - 1, cat="Integer"
    )
    team_play_period = LpVariable.dicts(
        "TeamPlayerPeriod", indices=(teams, weeks, periods), cat="Binary"
    )  # team_play_period[i,j,k] == 1 if team i in week j plays in period k

    # Link team_play_period to period_assign and week_matchups
    for t in teams:
        for w in weeks:
            team_weekly_game = None  # Game team t plays in week w
            for game_idx in periods:
                team1, team2 = week_matchups[w][game_idx]
                if team1 == t or team2 == t:
                    team_weekly_game = game_idx
                    break

            for p in periods:
                # team_play_period[t][w][p] == 1 iff period-assign[w][p][game_idx] == 1
                prob += team_play_period[t][w][p] == period_assign[w][p][game_idx]

    # Each team plays at most twice in the same period
    for t in teams:
        for p_scheduled in periods:
            prob += lpSum([team_play_period[t][w][p_scheduled] for w in weeks]) <= 2

    # Objective variable
    max_imbalance = LpVariable("MaxImbalance", lowBound=1, upBound=n - 1, cat="Integer")

    # How much a team plays at home
    for t in teams:
        prob += team_home_games[t] == lpSum(
            [
                (1 - home_away_assign[w][p])
                for w in weeks
                for p in periods
                if week_matchups[w][p][0] == t
            ]
        ) + lpSum(
            home_away_assign[w][p]
            for w in weeks
            for p in periods
            if week_matchups[w][p][1] == t
        )

    for t in teams:
        # max_imbalance = max{|home_games - away_games|}
        prob += max_imbalance >= (2 * team_home_games[t] - (n - 1))
        prob += max_imbalance >= -(2 * team_home_games[t] - (n - 1))

    prob += max_imbalance

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
                "sol": format_schedule(
                    period_assign, home_away_assign, week_matchups, n
                ),
            }
        case "Not optimal":  # No optimality guarantee
            result[solver_id] = {
                "time": timeout,
                "optimal": False,
                "obj": value(prob.objective),
                "sol": format_schedule(
                    period_assign, home_away_assign, week_matchups, n
                ),
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
