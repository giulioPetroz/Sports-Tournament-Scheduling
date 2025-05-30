from pulp import *

n = 6  # Number of teams

teams = range(n)  # Both team and weekly slots identifiers
weeks = range(n - 1)  # Week identifiers
slots = range(n)  # Slots go from 0 to n - 1 (periods implied by slot ids)
periods = range(n // 2)

prob = LpProblem("STS problem")

x = LpVariable.dicts(
    "X", indices=(teams, weeks, slots), cat="Binary"
)  # x[i][j][k] = 1 if team i plays in slot k in week j, 0 otherwise

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


prob.solve()
print("Status:", LpStatus[prob.status])

for v in prob.variables():
    if v.varValue == 1:
        print(v.name)
