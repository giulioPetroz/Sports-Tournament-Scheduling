from sat_encodings import *
from utils import parse_matches_schedule, parse_slots_schedule, set_params
import time
import importlib


def solve_satisfy(rb, n, teams, weeks, periods, solver_mod_name, solver_params):
    """
    Solves STS satisfiability

    Parameters:
    -----------
    rb : list of lists of tuples
        The round-robin structure that maps [position][week] to a tuple of team indices,
        representing the match to be played (e.g., rb[t][w] = (team_i, team_j)).

    n : int
        number of teams

    teams : list of int
        List of teams indices (usually range(n), where n = number of weeks).

    weeks : list of int
        List of week indices (usually range(w), where w = number of weeks).

    periods : list of int
        List of period indices (usually range(p), where p = number of periods).

    solver_mod_name : str
        Solver module name (z3, cvc5.pythonic, ...).

    solver_params : dict
        Dictionary of solver specific parameters

    Returns: tuple
    --------
    If the solution in found within the time limit:
        - sat_schedule : list of lists
            Scheduled tournament

        - runtime : float
            Time elapsed during solving

        - None:
            Flag indicating that the problem was solved without optimization

    Otherwise:
        - None

    Model:
    ------
    Constraints :
        - every team plays at most once a week
        - every team plays between once and twice a week

    Variables :
        - matches_schedule[p][w][t] <-> teams rb[t][w][0], rb[t][w][1] play in period p of week w
            Used for the first constraint

        - matches_to_periods[ti][tj][p] <-> teams ti, tj play in period t.
            Used for the last constraint
    """

    # translate module name into module
    solver = importlib.import_module(solver_mod_name)

    # Variables
    matches_schedule = [
        [[solver.Bool(f"matches_schedule_{p}_{w}_{t}") for t in periods] for w in weeks]
        for p in periods
    ]
    matches_to_periods = [
        [
            [solver.Bool(f"matches_to_periods_{ti}_{tj}_{p}") for p in periods]
            for tj in teams
        ]
        for ti in teams
    ]

    # solver for satisfiability
    s_sat = solver.Solver()
    set_params(s_sat, solver_params)

    """
        Symmetry breaking: fix the first match as scheduled by the round robin tournament
    """

    # s_sat.add(
    #     solver.And(
    #         *(
    #             [matches_schedule[0][0][0]]
    #             + [solver.Not(matches_schedule[0][0][p]) for p in periods[1:]]
    #         )
    #     )
    # )

    """
        Every team plays at most once a week
    """
    # one-hot encoding of the index to select the match of the week (auxiliary constraint)
    for p in periods:
        for w in weeks:
            s_sat.add(
                exactly_one_he([matches_schedule[p][w][t] for t in periods], solver)
            )
    # for each week every match in rb[*][w] is scheduled once
    for w in weeks:
        for t in periods:
            s_sat.add(
                exactly_one_he([matches_schedule[p][w][t] for p in periods], solver)
            )

    """
        Every team plays between at most twice in the same period
    """
    # bind matches_schedule with matches_to_periods (auxiliary constraint)
    for p in periods:
        for w in weeks:
            for t in periods:
                s_sat.add(
                    Iff(
                        matches_schedule[p][w][t],
                        matches_to_periods[rb[t][w][0]][rb[t][w][1]][p],
                        solver,
                    )
                )
    # each team plays at most twice in the same period
    for bp in periods:
        # constraint for the first team
        s_sat.add(
            at_most_k_seq(
                [matches_to_periods[0][t2][bp] for t2 in range(1, n)], 2, solver
            )
        )
        # constraint for the last team
        s_sat.add(
            at_most_k_seq(
                [matches_to_periods[t2][-1][bp] for t2 in range(0, n - 1)], 2, solver
            )
        )
        # constraint for the teams between the first and the last teams
        for t1 in range(1, n - 1):
            s_sat.add(
                at_most_k_seq(
                    # matches where t1 is away, i.e. t1 > t2
                    [matches_to_periods[t2][t1][bp] for t2 in range(t1)] +
                    # matches where t1 is home, i.e. t1 < t2
                    [matches_to_periods[t1][t2][bp] for t2 in range(t1 + 1, n)],
                    2,
                    solver,
                )
            )

    start_time = time.time()
    if s_sat.check() == solver.sat:
        # Solution found
        runtime = time.time() - start_time
        model_sat = s_sat.model()
        sat_schedule = parse_matches_schedule(
            matches_schedule, rb, periods, weeks, model_sat
        )
        return (
            sat_schedule,
            runtime,
            None,
        )
    else:
        # Solution not found
        return None


def solve_optimize(
    sat_schedule, n, teams, weeks, periods, sat_solution, solver_mod_name, solver_params
):
    """
    Solves STS optimization

    Parameters:
    -----------
    sat_schedule : list of lists of tuples
        Scheduled tournament: Note the teams are numbered in [1,n]

    n : int
        number of teams

    teams : list of int
        List of teams indices (usually range(n), where n = number of weeks).

    weeks : list of int
        List of week indices (usually range(w), where w = number of weeks).

    periods : list of int
        List of period indices (usually range(p), where p = number of periods).

    sat_solution : tuple
        Solution returned by solve_satisfy:
        - sat_schedule : list of lists
            Scheduled tournament satisfying STS constraints
        - runtime : float
            Time elapsed during solve_satisfy
        - None:
            Flag indicating that the problem was solved without optimization

    solver_mod_name: str
        Solver module name (z3, cvc5.pythonic, ...).

    Return:
    -------
    If a better-than-sat solution is found within the time limit:

        opt_solution : tuple
            - opt_schedule : list of lists
                Optimized scheduled tournament

            - runtime : float
                Time elapsed during solving

            - mid : int
                the value of the optimizazion function

    Otherwise opt_solution == sat_solution

    Model:
    ------
    Variables :
        - slots_schedule[p][w]      iff team rb[t][w][0] plays away
        - matches_to_slots[ti][tj]  iff team ti plays away and tj plays at home

    Optimizazion function :
    -----------------------
        maximize the minimum number k of times every team plays at home
    """
    # translate module name into module
    solver = importlib.import_module(solver_mod_name)

    # Variables
    slots_schedule = [
        [solver.Bool(f"slots_schedule_{p}_{w}") for w in weeks] for p in periods
    ]
    matches_to_slots = [
        [solver.Bool(f"matches_to_slots_{ti}_{tj}") for tj in teams] for ti in teams
    ]

    # opt_solution is sat_solution if optimization fails
    opt_solution = sat_solution
    runtime = 0

    # Binary search optimization
    low, high = 1, (n - 1) // 2
    while low <= high:
        mid = (low + high) // 2

        s_opt = solver.Solver()  # solver for optimization
        set_params(s_opt, solver_params)

        # bind slots_schedule to matches_to_slots
        for p in periods:
            for w in weeks:
                s_opt.add(
                    Iff(
                        slots_schedule[p][w],
                        matches_to_slots[sat_schedule[p][w][0] - 1][
                            sat_schedule[p][w][1] - 1
                        ],
                        solver,
                    )
                )

        # optimization: constrain the minimum number of times each team plays at home
        # first team
        s_opt.add(
            at_least_k_seq([matches_to_slots[0][t2] for t2 in range(1, n)], mid, solver)
        )
        # last team
        s_opt.add(
            at_least_k_seq(
                [solver.Not(matches_to_slots[t2][-1]) for t2 in range(0, n - 1)],
                mid,
                solver,
            )
        )
        # teams between the first and the last teams
        for t1 in range(1, n - 1):
            s_opt.add(
                at_least_k_seq(
                    [solver.Not(matches_to_slots[t2][t1]) for t2 in range(t1)]
                    + [matches_to_slots[t1][t2] for t2 in range(t1 + 1, n)],
                    mid,
                    solver,
                )
            )

        start_time = time.time()
        if s_opt.check() == solver.sat:
            runtime += time.time() - start_time
            model_opt = s_opt.model()
            sat_schedule = sat_solution[0]
            opt_schedule = parse_slots_schedule(
                sat_schedule, slots_schedule, periods, weeks, model_opt
            )
            opt_solution = (  # update optimal solution
                opt_schedule,
                runtime,
                mid,
            )
            low = mid + 1  # increase optimization function
        else:
            runtime += time.time() - start_time
            high = mid - 1  # roll back

    return opt_solution
