from itertools import combinations

import os
import json
import argparse


def get_elements(solution, list_condition_funct, n=None):
    elements = []
    if list_condition_funct(solution, n):
        elements += solution
    else:
        for sol in solution:
            elements += get_elements(sol, list_condition_funct, n)
    return elements


def get_teams(solution):
    return get_elements(solution, lambda s,n: all([type(i) == int for i in s]))


def get_periods(solution, n):
    return get_elements(solution, lambda s,n: all([type(i) == list and len(i) == n for i in s]), n)


def get_matches(solution):
    return get_elements(solution, lambda s,n: all([type(i) == list and len(i) == 2 and all([type(ii) == int for ii in i]) for i in s]))


def get_weeks(periods, n):
    return [[p[i] for p in periods] for i in range(n-1)]


def fatal_errors(solution):
    fatal_errors = []

    if len(solution) == 0:
        fatal_errors.append('The solution cannot be empty')
        return fatal_errors

    teams = get_teams(solution)
    n = max(teams)

    if any([t not in set(teams) for t in range(1,n+1)]):
        fatal_errors.append(f'Missing team in the solution or team out of range!!!')

    if n%2 != 0:
        fatal_errors.append(f'"n" should be even!!!')

    if len(solution) != n//2:
        fatal_errors.append(f'the number of periods is not compliant!!!')

    if any([len(s) != n - 1 for s in solution]):
        fatal_errors.append(f'the number of weeks is not compliant!!!')


    return fatal_errors


def check_solution(solution: list):

    errors = fatal_errors(solution)

    if len(errors) == 0:

        teams = get_teams(solution)
        n = max(teams)

        teams_matches = combinations(set(teams),2)
        solution_matches = get_matches(solution)

        # every team plays with every other teams only once
        if any([solution_matches.count([h,a]) + solution_matches.count([a,h]) > 1 for h,a in teams_matches]):
            errors.append('There are duplicated matches!!!')

        # each team cannot play against itself
        if any([h==a for h,a in solution_matches]):
            errors.append('There are self-playing teams')

        periods = get_periods(solution, n - 1)
        weeks = get_weeks(periods, n)

        # every team plays once a week
        teams_per_week = [get_teams(i) for i in weeks]
        if any([len(tw) != len(set(tw)) for tw in teams_per_week]):
            errors.append('Some teams play multiple times in a week')

        teams_per_period = [get_teams(p) for p in periods]

        # every team plays at most twice during the period
        if any([teams_per_period.count(tp) > 2 for tp in teams_per_period]):
            errors.append('Some teams play more than twice in the period')

    return 'Valid solution' if len(errors) == 0 else errors


def load_json(path):
    try:
        with open(path, 'r') as f:
            return json.load(f)
    except Exception as e:
        print(f"Error reading {path}: {e}")
        sys.exit(1)


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description="Check the validity of a STS solution JSON file.")
    parser.add_argument("json_file_directory", help="Path to the directory containing .json solution files")
    args = parser.parse_args()

    directory = args.json_file_directory

    for f in filter(lambda x: x.endswith('.json'), os.listdir(directory)):
        json_data = load_json(f'{directory}/{f}')

        for approach, result in json_data.items():
            sol = result.get("sol")
            message = check_solution(sol)
            status = "VALID" if type(message) == str else "INVALID"
            print(f"Approach: {approach}\n  Status: {status}\n  Reason: {message if status == 'VALID' else ' \n\t  '.join(message)}\n")
