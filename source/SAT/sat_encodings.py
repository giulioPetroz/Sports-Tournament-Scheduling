from utils import gen_var_id
from z3 import *
from itertools import combinations

gen_id = gen_var_id()

def at_most_one_np(bool_vars, name = ""):
    return And([Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)])

def at_least_one_he(bool_vars):
    return Or(bool_vars)

def at_most_one_he(bool_vars, n = 4):
    formula, sub_seq = [], [0]*n
    i, j, _len = 0, 0, len(bool_vars)
    id = next(gen_id)
    for k in range(_len):
        sub_seq[i] = bool_vars[k]
        if _len - k == 2:
            sub_seq[i+1] = bool_vars[-1]
            formula.append(at_most_one_np(sub_seq[:i+2]))
            break
        elif i == n-2:
            sub_seq[-1] = Bool(f"y_{j}__{id}")
            formula.append(at_most_one_np(sub_seq))
            sub_seq[0] = Not(sub_seq[-1])
            j += 1
            i = 0
        i += 1
    return And(formula)

def at_most_k_seq(x, k):
    id = next(gen_id)
    n = len(x)
    if n <= k:
        return True
    s = [[Bool(f"s_{i}_{j}__{id}") for j in range(k)] for i in range(n-1)]
    return (
        And(
            Implies(x[0], s[0][0]),
            Implies(s[n-2][k-1], Not(x[n-1])),
            And([Not(s[0][j]) for j in range(1, k)]),
            And([ 
                And(
                    Implies(Or(x[i], s[i-1][0]), s[i][0]),
                    And([
                        Implies(Or(And(x[i], s[i-1][j-1]), s[i-1][j]), s[i][j])
                    for j in range(1, k)
                    ]),
                    Implies(s[i-1][k-1], Not(x[i]))
                )
            for i in range(1,n-1)
            ])
        )
    )

def at_least_k_seq(x, k):
    id = next(gen_id)
    n = len(x)
    if n < k:
        return False
    s = [[Bool(f"s_{i}_{j}__{id}") for j in range(k)] for i in range(n)]
    return (
        And(
            Iff(s[0][0], x[0]),
            And([Iff(Or(s[i-1][0], x[i]), s[i][0]) for i in range(1, n)]),
            And([
                And([
                    Iff(Or(And(s[i-1][j-1], x[i]),s[i-1][j]),s[i][j])
                for i in range(1,n)
                ])
            for j in range(1,k)
            ]),
            And([s[n-1][j] for j in range(k)]),
            And([Not(s[0][j]) for j in range(1,k)]),
        )
    )

def exactly_one_he(bool_vars, name = ""):
    return And(at_most_one_he(bool_vars), at_least_one_he(bool_vars))

def Iff(A, B):
    return And(Implies(A, B), Implies(B, A))