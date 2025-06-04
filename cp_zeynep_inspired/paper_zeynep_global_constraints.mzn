% ==============================================================================
% SPORTS SCHEDULING MODEL (Global Constraints Version)
% ==============================================================================

include "globals.mzn";

% ==============================================================================
% PARAMETERS
% ==============================================================================

int: n;
constraint n >= 4 /\ n mod 2 = 0;

% Derived parameters
int: n_weeks = n - 1;                    % Number of playing weeks
int: n_periods = n div 2;                % Number of periods per week
int: extended_weeks = n_weeks + 1;       % Including dummy week for modeling

% Domain definitions
set of int: Teams = 1..n;
set of int: Weeks = 1..n_weeks;         % Real playing weeks only
set of int: ExtendedWeeks = 1..extended_weeks; % Including dummy week
set of int: Periods = 1..n_periods;
set of int: Slots = 1..2;               % 1 = home, 2 = away

% ==============================================================================
% DECISION VARIABLES
% ==============================================================================

% teams[p,w,s]: Team playing in period p, week w, slot s (1=home, 2=away)
array[Periods, ExtendedWeeks, Slots] of var Teams: teams;

% games[p,w]: Unique game identifier for the match in period p, week w
array[Periods, Weeks] of var 1..(n*(n-1) div 2): games;

% ==============================================================================
% CORE CONSTRAINTS
% ==============================================================================

% C1: Team participation - Each team plays exactly once per week
% Uses global_cardinality_closed to ensure each team appears exactly once
constraint forall(w in Weeks)(
    global_cardinality_closed(
        [teams[p, w, s] | p in Periods, s in Slots],
        Teams,
        [1 | _ in Teams]  
    )
) :: "C1_team_participation_per_week";

% C2: Home/away ordering - Home team ID must be less than away team ID
constraint forall(p in Periods, w in ExtendedWeeks)(
    teams[p, w, 1] < teams[p, w, 2]
) :: "C2_home_away_ordering";

% C3: Period balance - Each team plays at most twice in any given period
constraint forall(p_outer in Periods)(
    global_cardinality_low_up(
        [teams[p_outer, w_inner, s_inner] | w_inner in ExtendedWeeks, s_inner in Slots], % Array of teams playing in period p_outer across all weeks/slots
        Teams,            % Values to count
        [1 | _ in Teams], % Lower bound for each team (0)
        [2 | _ in Teams]  % Upper bound for each team (2)
    )
) :: "C3_period_balance_gcc_low_up";

% C4: Game encoding - Maps each unique team pair to a unique game identifier
constraint forall(p in Periods, w in Weeks)(
    let {
        var Teams: home = teams[p, w, 1];
        var Teams: away = teams[p, w, 2]
    } in (
        games[p, w] = ((home - 1) * (2 * n - home)) div 2 + (away - home)
    )
) :: "C4_game_encoding";

% C5: Game uniqueness - All games must have different identifiers
constraint alldifferent([games[p, w] | p in Periods, w in Weeks])::on_domain
    :: "C5_game_uniqueness";

% C6: Complete round-robin - Every pair of teams plays exactly once
% MODIFIED: Replaced sum with count
constraint forall(t1, t2 in Teams where t1 < t2)(
    count([ (teams[p_idx, w_idx, 1] = t1 /\ teams[p_idx, w_idx, 2] = t2) | p_idx in Periods, w_idx in Weeks], true, 1)
) :: "C6_complete_round_robin_global_count";

% ==============================================================================
% SYMMETRY BREAKING CONSTRAINTS
% ==============================================================================

% SB1: Lexicographic ordering on periods
constraint forall(p1, p2 in Periods where p1 < p2)(
    lex_lesseq(
        [teams[p1, w, s] | w in ExtendedWeeks, s in Slots],
        [teams[p2, w, s] | w in ExtendedWeeks, s in Slots]
    )
) :: "SB1_period_lexicographic_ordering";

% SB2: Lexicographic ordering on weeks
constraint forall(w1, w2 in ExtendedWeeks where w1 < w2)(
    lex_lesseq(
        [teams[p, w1, s] | p in Periods, s in Slots],
        [teams[p, w2, s] | p in Periods, s in Slots]
    )
) :: "SB2_week_lexicographic_ordering";

% SB3: Fix first game
constraint teams[1, 1, 1] = 1 /\ teams[1, 1, 2] = 2
    :: "SB3_fix_first_game";

% ==============================================================================
% AUXILIARY CONSTRAINTS
% ==============================================================================

% AUX1: Dummy week structure
% This is already covered by C2 if ExtendedWeeks is used there, but kept for explicitness as in original.
constraint forall(p in Periods)(
    teams[p, extended_weeks, 1] < teams[p, extended_weeks, 2]
) :: "AUX1_dummy_week_structure";

% ==============================================================================
% IMPLIED CONSTRAINTS (Performance Enhancement)
% ==============================================================================

% IMP1: Game ordering between weeks
constraint forall(w1, w2 in Weeks where w1 < w2)(
    lex_less([games[p, w1] | p in Periods], [games[p, w2] | p in Periods])
) :: "IMP1_game_ordering_between_weeks";


% ==============================================================================
% REDUNDANT CONSTRAINTS (For Enhanced Propagation)
% ==============================================================================

% RED1: Alternative formulation of team participation (C1)
% MODIFIED: Replaced sum with count
constraint forall(w in Weeks, t in Teams)(
    sum(p in Periods, s in Slots)(bool2int(teams[p, w, s] = t)) = 1
) :: "RED1_team_participation_alternative";

% ==============================================================================
% SOLVE STATEMENT
% ==============================================================================

solve satisfy;

% ==============================================================================
% OUTPUT
% ==============================================================================

output [
    "=== ROUND ROBIN TOURNAMENT SCHEDULE (Global Constraints Version) ===\n",
    "Teams: " ++ show(n) ++ " | Weeks: " ++ show(n_weeks) ++ 
    " | Periods per week: " ++ show(n_periods) ++ "\n\n"
] ++ [
    "WEEK " ++ show(w) ++ ":\n" ++
    concat([
        "  Period " ++ show(p) ++ ": Team " ++ 
        show(teams[p, w, 1]) ++ " (home) vs Team " ++ 
        show(teams[p, w, 2]) ++ " (away)\n"
        | p in Periods
    ]) ++ "\n"
    | w in Weeks
] ++ [
    "=== END SCHEDULE ===\n"
];