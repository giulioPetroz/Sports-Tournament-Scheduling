from itertools import combinations

import os
import json
import argparse
import sys

def get_elements(solution):

    periods = [s for s in solution]
    matches = [m for s in periods for m in s]
    teams = [t for m in matches for t in m]

    return periods, matches, teams


def get_weeks(periods, n):
    return [[p[i] for p in periods] for i in range(n-1)]


def fatal_errors(solution, obj, time, optimal, teams):
    fatal_errors = []

    if len(solution) == 0 and (not (time == 300 and not optimal) and not (time == 0 and optimal) and obj!='None'):
        fatal_errors.append('The solution cannot be empty!!!')
        return fatal_errors

    if type(solution) != list:
        fatal_errors.append('The solution should be a list!!!')
        return fatal_errors

    if len(solution) > 0:

        n = max(teams)

        if any([t not in set(teams) for t in range(1,n+1)]):
            fatal_errors.append(f'Missing team in the solution or team out of range!!!')

        if n%2 != 0:
            fatal_errors.append(f'"n" should be even!!!')

        if len(solution) != n//2:
            fatal_errors.append(f'the number of periods is not compliant!!!')

        if any([len(s) != n - 1 for s in solution]):
            fatal_errors.append(f'the number of weeks is not compliant!!!')

        if time > 300:
            fatal_errors.append(f'The running time exceeds the timeout!!!')

    return fatal_errors


def check_solution(solution: list, obj, time, optimal):

    periods, solution_matches, teams = get_elements(solution)

    errors = fatal_errors(solution, obj, time, optimal, teams)

    if len(errors) == 0 and len(solution) > 0:

        n = max(teams)

        teams_matches = combinations(set(teams),2)

        # every team plays with every other teams only once
        if any([solution_matches.count([h,a]) + solution_matches.count([a,h]) > 1 for h,a in teams_matches]):
            errors.append('There are duplicated matches')

        # each team cannot play against itself
        if any([h==a for h,a in solution_matches]):
            errors.append('There are self-playing teams')

        weeks = get_weeks(periods, n)

        # every team plays once a week
        teams_per_week = [[j for i in w for j in i] for w in weeks]
        if any([len(tw) != len(set(tw)) for tw in teams_per_week]):
            errors.append('Some teams play multiple times in a week')

        teams_per_period = [[j for i in p for j in i] for p in periods]

        # every team plays at most twice during the period
        if any([any([tp.count(elem) > 2 for elem in tp]) for tp in teams_per_period]):
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

        print(f'File: {f}\n')
        for approach, result in json_data.items():
            sol = result.get("sol")
            time = result.get("time")
            opt = result.get("optimal")
            obj = result.get("obj")

            message = check_solution(sol, obj, time, opt)
            status = "VALID" if type(message) == str else "INVALID"
            message_str = '\n\t  '.join(message)
            print(f"  Approach: {approach}\n    Status: {status}\n    Reason: {message if status == 'VALID' else message_str}\n")
