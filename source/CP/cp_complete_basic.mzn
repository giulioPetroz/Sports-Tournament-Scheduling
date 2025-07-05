include "globals.mzn";

% Parameters and Sets
int: N;               % Number of teams 
set of int: T = 0..N-1;   % Set of teams 
set of int: S = 0..1;     % Set of slots in a match (0=first team, 1=second team)
set of int: W = 0..N-2;   % Set of weeks/rounds (N-1 weeks for round-robin)
set of int: P = 0..N div 2 - 1; % Set of periods within each week

% Ensure tournament feasibility
constraint assert (N mod 2 == 0, "N must be even");

% Round-Robin Structure Generator
% 
% Generates the canonical round-robin structure using the circle method.
% For each period p and week w, rb[p,w,s] gives the team at slot s.
% 
% The algorithm works by:
% - Fixing one team (N-1) in period 0
% - Rotating other teams around a circle for subsequent periods
array [P, W, S] of T: rb = array3d(P, W, S, 
    [
        if s == 0 then
            % First slot assignment
            if p == 0 then
                N-1  % Team N-1 always in period 0, slot 0
            else
                (p + w) mod (N-1)  % Rotate teams for other periods
            endif
        else
            % Second slot assignment
            if p == 0 then
                w  % Opponent for fixed team N-1
            else
                (N - p + w - 1) mod (N-1)  % Corresponding opponent
            endif
        endif
        | p in P, w in W, s in S
    ]
);

% Decision Variables
% Which period is scheduled in each week-period slot
array [P, W] of var P: matches;

% Home/away assignment for each match
% 0: first team (rb[matches[p,w],w,0]) plays at home
% 1: second team (rb[matches[p,w],w,1]) plays at home
array [P, W] of var 0..1: home_away;

% Objective: minimize maximum imbalance in home games
var 1..N div 2 : max_imbalance;

% Number of home games for each team
array [T] of var 1..N-1: home_games;

% Core Tournament Constraints

% Constraint 1: Each period must be used exactly once per week
% Ensures all matches from the round-robin structure are scheduled
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);

% Constraint 2: Each team plays at most twice per period
constraint forall(p in P)(
    global_cardinality([rb[matches[p, w], w, s] | w in W, s in S], 
                      [t | t in 0..N-1],        % teams
                      [0| _ in 0..N-1],         % minimum occurrences
                      [2 | _ in 0..N-1])        % maximum occurrences (at most 2)
);

% Constraint 3: Calculate home games for each team
% A team plays at home if it's the first team and home_away=0, or second team and home_away=1
constraint forall(t in T)(
    home_games[t] = sum(p in P, w in W)(
        bool2int(
            (rb[matches[p, w], w, 0] = t /\ home_away[p, w] = 0) \/
            (rb[matches[p, w], w, 1] = t /\ home_away[p, w] = 1)
        )
    )
); 

% Constraint 4: Fairness - balance home and away games
% Each team should play approximately (N-1)/2 home games
constraint forall(t in T)(
    abs(2 * home_games[t] - (N-1)) <= max_imbalance
);

% Symmetry Breaking Constraints

% Break period assignment symmetry using lexicographic ordering
constraint symmetry_breaking_constraint(
    lex_greater([matches[p, w] | w in W, p in P], 
               [matches[p, w] | w in W, p in reverse(P)])
);

% Fix first match home assignment to break home/away symmetry
constraint home_away[0, 0] = 0;

% Balance the home/away assignments within each week.
% ---------------------------------------------------
% This constraint ensures that, in every week (round), 
% the number of matches where the first team plays at home (home_away = 0)
% and the second team plays at home (home_away = 1) is roughly equal.
constraint forall(w in W)(
    abs(sum(p in P)(home_away[p, w]) - card(P) div 2) <= 1
);

% Implied Constraint ->  Ensure each team appears exactly once per week
constraint forall(w in W)(
    global_cardinality([rb[matches[p, w], w, s] | p in P, s in S], 
                      [t | t in T],             % teams
                      [1 | t in T],             % minimum: each team once
                      [1 | t in T])             % maximum: each team once
);

% Search Strategy and Optimization
solve minimize max_imbalance;