n = 6

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
