% ==============================================================================
% SPORTS SCHEDULING MODEL
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
% 1) A team cannot play against itself (home != away)
% 2) Ensures unique representation of each match, a team between 3 and 4 will alway be (3,4) and never (4,3)
constraint forall(p in Periods, w in ExtendedWeeks)(
    teams[p, w, 1] < teams[p, w, 2]
) :: "C2_home_away_ordering";

% C3: Period balance - Each team plays at most twice in any given period
constraint forall(t in Teams, p in Periods)(
    sum(w in ExtendedWeeks, s in Slots)(bool2int(teams[p, w, s] = t)) <= 2
) :: "C3_period_balance";

% C4: Game encoding - Maps each unique team pair to a unique game identifier
% Formula: ((home-1) * (2*n - home)) / 2 + (away - home)
constraint forall(p in Periods, w in Weeks)(
    let {
        var Teams: home = teams[p, w, 1];
        var Teams: away = teams[p, w, 2]
    } in (
        games[p, w] = ((home - 1) * (2 * n - home)) div 2 + (away - home)
    )
) :: "C4_game_encoding";

% C5: Game uniqueness - All games must have different identifiers
% Ensures no duplicate matches throughout the tournament
constraint alldifferent([games[p, w] | p in Periods, w in Weeks])
    :: "C5_game_uniqueness";

% C6: Complete round-robin - Every pair of teams plays exactly once
% Core requirement: each team must play against every other team exactly once
constraint forall(t1, t2 in Teams where t1 < t2)(
    sum(p in Periods, w in Weeks)(
        bool2int(teams[p, w, 1] = t1 /\ teams[p, w, 2] = t2)
    ) = 1
) :: "C6_complete_round_robin";

% ==============================================================================
% SYMMETRY BREAKING CONSTRAINTS
% ==============================================================================

% SB1: Lexicographic ordering on periods
% Breaks symmetry between identical periods by imposing lexicographic order
constraint forall(p1, p2 in Periods where p1 < p2)(
    lex_lesseq(
        [teams[p1, w, s] | w in ExtendedWeeks, s in Slots],
        [teams[p2, w, s] | w in ExtendedWeeks, s in Slots]
    )
) :: "SB1_period_lexicographic_ordering";

% SB2: Lexicographic ordering on weeks
% Breaks symmetry between weeks by imposing lexicographic order
constraint forall(w1, w2 in ExtendedWeeks where w1 < w2)(
    lex_lesseq(
        [teams[p, w1, s] | p in Periods, s in Slots],
        [teams[p, w2, s] | p in Periods, s in Slots]
    )
) :: "SB2_week_lexicographic_ordering";

constraint forall(w1, w2 in Weeks where w1 < w2)(
    lex_less([games[p, w1] | p in Periods], [games[p, w2] | p in Periods])
) :: "SB3_game_ordering_between_weeks";


% SB3: Fix first game
% Strong symmetry breaking: fix the first game to be teams 1 vs 2
constraint teams[1, 1, 1] = 1 /\ teams[1, 1, 2] = 2
    :: "SB3_fix_first_game";

% ==============================================================================
% AUXILIARY CONSTRAINTS
% ==============================================================================

% AUX1: Dummy week structure
% Ensures dummy week follows the same home/away ordering as real weeks
constraint forall(p in Periods)(
    teams[p, extended_weeks, 1] < teams[p, extended_weeks, 2]
) :: "AUX1_dummy_week_structure";



% ==============================================================================
% REDUNDANT CONSTRAINTS (For Enhanced Propagation)
% ==============================================================================

% RED1: Alternative formulation of team participation (C1)
% Redundant with C1 but  provide additional propagation
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
    "=== ROUND ROBIN TOURNAMENT SCHEDULE ===\n",
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