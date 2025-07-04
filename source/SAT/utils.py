def gen_var_id():
    """
    Natural number generator (see sat_encodings.py)
    """
    i = 0
    while True:
        i += 1
        yield i


def set_params(solver, solver_params):
    for solver_param in solver_params.values():
        solver.set(solver_param[0], solver_param[1])


def parse_matches_schedule(matches_schedule, rb, periods, weeks, model):
    """
    Parses the SAT model solution into a human-readable match schedule.

    Parameters:
    -----------
    matches_schedule : list of lists of lists of z3.Bool
        A 3D structure where matches_schedule[p][w][bp] indicates whether the match
        at round-robin position `bp` in week `w` is scheduled for period `p`.
        It uses one-hot encoding (only one True per list).

    rb : list of lists of tuples
        The round-robin structure that maps [position][week] to a tuple of team indices,
        representing the match to be played (e.g., rb[t][w] = (team_i, team_j)).

    periods : list of int
        List of period indices (usually range(p), where p = number of periods).

    weeks : list of int
        List of week indices (usually range(w), where w = number of weeks).

    model :
        The solved model used to evaluate boolean expressions to their actual values (True/False).

    Returns:
    --------
    solution : list of lists of tuples
        A 2D list where solution[p] gives the list of matches scheduled in period `p`,
        and each entry solution[p][w] is a tuple of team indices (ti, tj) playing in that week.
    """
    solution = []
    for p in periods:
        matches = []
        for w in weeks:
            new_p = [
                model.evaluate(matches_schedule[p][w][bp]) for bp in periods
            ].index(
                True
            )  # one-hot encoding -> integer
            matches.append([rb[new_p][w][0] + 1, rb[new_p][w][1] + 1])
        solution.append(matches)
    return solution


def parse_slots_schedule(sat_schedule, slots_schedule, periods, weeks, model):
    """
    Parses the SAT model solution into a human-readable match schedule.

    Parameters:
    -----------
    sat_schedule : list of lists of tuples
        A 2D list where sat_solution[p] gives the list of matches scheduled in period `p`,
        and each entry sat_solution[p][w] is a tuple of team indices (ti, tj) playing in that week.
        It satisfies STS without optimization.

    slots_schedule: list of lists of z3.BoolRef
        A 2D list where slots_schedule[p][w] the slot assigned to the team sat_solution[p][w][0].

    periods : list of int
        List of period indices (usually range(p), where p = number of periods).

    weeks : list of int
        List of week indices (usually range(w), where w = number of weeks).

    model :
        The solved model used to evaluate boolean expressions to their actual values (True/False).

    Returns:
    --------
    solution : list of lists of tuples
        A 2D list where solution[p] gives the list of matches scheduled in period `p`,
        and each entry solution[p][w] is a tuple of team indices (ti, tj) playing in that week.
    """
    solution = []
    for p in periods:
        matches = []
        for w in weeks:
            new_r = bool(model.evaluate(slots_schedule[p][w]))
            matches.append([sat_schedule[p][w][new_r], sat_schedule[p][w][1 - new_r]])
        solution.append(matches)

    return solution


def format_solution(solution, total_runtime):
    """
    Formats the final solution

    Parameters:
    -----------
    solution : tuple | None
        If a solution is found:
            - {sat|opt}_schedule : list of lists
                schedule {satisfying|optimizing} STS problem
            - runtime : float
                runtime of {solve_satisfy|solve_optimize} solution (to be ignored)
            - obj : int|None
                value of objective function. None when the solution isn't optimized
        Otherwise None

    total_runtime : float
        - total runtime for solve_satisfy and solve_optimize

    Returns:
    --------
    dictionary containing the formatted results
    """

    if solution is None:
        return {"time": int(300), "optimal": False, "obj": None, "sol": []}

    schedule, _, obj = solution
    # If the value of the optimization is maximum,
    # set optimal to True
    if obj == len(schedule[0]) // 2:
        optimal = True
    else:
        optimal = False
        total_runtime = int(300)

    return {"time": int(total_runtime), "optimal": optimal, "obj": obj, "sol": schedule}
