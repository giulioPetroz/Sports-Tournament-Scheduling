from utils import gen_var_id
from itertools import combinations

"""
    gen_id: used to generate unique literals across repeated calls
            to functions
"""
gen_id = gen_var_id()


def at_most_one(bool_vars, solver):
    """
    Vanilla AtMostOne encoding
    """
    return solver.And(
        [
            solver.Not(solver.And(pair[0], pair[1]))
            for pair in combinations(bool_vars, 2)
        ]
    )


def at_least_one(bool_vars, solver):
    """
    Vanilla AtLeastOne encoding
    """
    return solver.Or(bool_vars)


def at_most_one_he(bool_vars, solver, n=4):
    """
    Heule AtMostOne encoding
    """
    formula, sub_seq = [], [0] * n
    i, j, _len = 0, 0, len(bool_vars)
    id = next(gen_id)
    for k in range(_len):
        sub_seq[i] = bool_vars[k]
        if _len - k == 2:
            sub_seq[i + 1] = bool_vars[-1]
            formula.append(at_most_one(sub_seq[: i + 2], solver))
            break
        elif i == n - 2:
            sub_seq[-1] = solver.Bool(f"y_{j}__{id}")
            formula.append(at_most_one(sub_seq, solver))
            sub_seq[0] = solver.Not(sub_seq[-1])
            j += 1
            i = 0
        i += 1
    return solver.And(*formula)


def at_most_k_seq(x, k, solver):
    """
    Sequential AtMostK encoding
    """
    id = next(gen_id)
    n = len(x)
    if n <= k:
        return True
    s = [[solver.Bool(f"s_{i}_{j}__{id}") for j in range(k)] for i in range(n - 1)]
    return solver.And(
        solver.Implies(x[0], s[0][0]),
        solver.Implies(s[n - 2][k - 1], solver.Not(x[n - 1])),
        solver.And(*[solver.Not(s[0][j]) for j in range(1, k)]),
        solver.And(
            *[
                solver.And(
                    solver.Implies(solver.Or(x[i], s[i - 1][0]), s[i][0]),
                    solver.And(
                        *[
                            solver.Implies(
                                solver.Or(
                                    solver.And(x[i], s[i - 1][j - 1]), s[i - 1][j]
                                ),
                                s[i][j],
                            )
                            for j in range(1, k)
                        ]
                    ),
                    solver.Implies(s[i - 1][k - 1], solver.Not(x[i])),
                )
                for i in range(1, n - 1)
            ]
        ),
    )


def at_least_k_seq(x, k, solver):
    """
    Sequential AtLeastK encoding
    """
    id = next(gen_id)
    n = len(x)
    if n < k:
        return False
    s = [[solver.Bool(f"s_{i}_{j}__{id}") for j in range(k)] for i in range(n)]
    return solver.And(
        Iff(s[0][0], x[0], solver),
        solver.And(
            *[Iff(solver.Or(s[i - 1][0], x[i]), s[i][0], solver) for i in range(1, n)]
        ),
        solver.And(
            *[
                solver.And(
                    *[
                        Iff(
                            solver.Or(solver.And(s[i - 1][j - 1], x[i]), s[i - 1][j]),
                            s[i][j],
                            solver,
                        )
                        for i in range(1, n)
                    ]
                )
                for j in range(1, k)
            ]
        ),
        solver.And(*[s[n - 1][j] for j in range(k)]),
        solver.And(*[solver.Not(s[0][j]) for j in range(1, k)]),
    )


def exactly_one_he(bool_vars, solver):
    """
    ExactlyOne encoding using Heule
    """
    return solver.And(
        at_most_one_he(bool_vars, solver), at_least_one(bool_vars, solver)
    )


def Iff(A, B, solver):
    return solver.And(solver.Implies(A, B), solver.Implies(B, A))
