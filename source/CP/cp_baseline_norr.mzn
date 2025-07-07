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
array [P, W] of var P: matches;
array [P, W] of var 0..1: home_away;
var 1..N -1 : max_imbalance;
array [T] of var 1..N-1: home_games;

% Essential Constraints Only

% Constraint 1: Each period must be used exactly once per week
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
constraint forall(t in T)(
    home_games[t] = sum(p in P, w in W)(
        bool2int(
            (rb[matches[p, w], w, 0] = t /\ home_away[p, w] = 0) \/
            (rb[matches[p, w], w, 1] = t /\ home_away[p, w] = 1)
        )
    )
); 

% Constraint 4: Fairness - balance home and away games
constraint forall(t in T)(
    abs(2 * home_games[t] - (N-1)) <= max_imbalance
);

solve ::
    restart_luby(100) ::
    seq_search([
        int_search([matches[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p, w] | p in P, w in W], first_fail, indomain_min, complete)
    ]) minimize max_imbalance;