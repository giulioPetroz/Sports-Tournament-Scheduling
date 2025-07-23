import argparse

parser = argparse.ArgumentParser(
    prog="rb", description="Generates a round-robin tournament"
)

parser.add_argument("-t", "--teams", type=int, help="Number of teams", required=True)

args = parser.parse_args()
n = args.teams

assert n % 2 == 0 and n >= 6

teams = range(n)  # Team identifiers
weeks = range(n - 1)  # Week identifiers
periods = range(n // 2)  # Period identifiers

# Round robin schedule generation
rb = []
for p in periods:
    matches = []
    for w in weeks:
        if p == 0:
            matches.append([n - 1, w])
        else:
            matches.append([(p + w) % (n - 1), (n - p + w - 1) % (n - 1)])
    rb.append(matches)

for p in periods:
    for w in weeks:
        print(rb[p][w], end=" ")
    print()
