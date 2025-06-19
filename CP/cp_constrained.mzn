include "globals.mzn";

int: n;
int: N = n;
set of int: T = 0..N-1;
set of int: S = 0..1;
set of int: W = 0..N-2;
set of int: P = 0..N div 2 - 1;

constraint assert (N mod 2 == 0, "N must be even");

% Round-robin structure
array [P, W, S] of T: rb = array3d(P, W, S, 
    [
        if s == 0 then
            if p == 0 then
                N-1
            else
                (p + w) mod (N-1)
            endif
        else
            if p == 0 then
                w
            else
                (N - p + w - 1) mod (N-1)
            endif
        endif
        | p in P, w in W, s in S
    ]
);

% Decision variables
array [P, W] of var P: matches;
array [P, W] of var 0..1: home_away;
var 1..N - 1: max_imbalance; 

% Auxiliary variables
array [T] of var 1..N-1: team_home_games;

% Core constraints
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);

constraint forall(p in P)(
    global_cardinality([rb[matches[p, w], w, s] | w in W, s in S], 
                      [t | t in 0..N-1], [0 | _ in 0..N-1], [2 | _ in 0..N-1])
);

% Define auxiliary variables
constraint forall(t in T)(
    team_home_games[t] = sum(p in P, w in W)(
        (rb[matches[p, w], w, 0] = t /\ home_away[p, w] = 0) +
        (rb[matches[p, w], w, 1] = t /\ home_away[p, w] = 1)
    )
);

% Fairness constraints using auxiliary variables
constraint forall(t in T)(
    abs(2 * team_home_games[t] - (N-1)) <= max_imbalance
);

% Implied constraints
constraint sum(t in T)(team_home_games[t]) = (N * (N-1)) div 2;
constraint max(team_home_games) - min(team_home_games) <= max_imbalance;

% Enhanced symmetry breaking
constraint symmetry_breaking_constraint(
    lex_greater([matches[p, w] | w in W, p in P], 
               [matches[p, w] | w in W, p in reverse(P)])
);

constraint lex_lesseq([home_away[p, w] | p in P, w in W], 
                      [1 - home_away[p, w] | p in P, w in W]);

constraint lex_lesseq(
    [rb[matches[p, 0], 0, s] | p in P, s in S],
    [rb[matches[p, 1], 1, s] | p in P, s in S]
);
constraint home_away[0, 0] = 0;


solve :: if N >= 20 then
    % Strategy 1: Very aggressive for N≥20
    restart_geometric(2.0, 500) ::
    relax_and_reconstruct([matches[p,w] | p in P, w in W], 90) ::
    int_search([matches[p,w] | p in P, w in W] ++ [home_away[p,w] | p in P, w in W], 
               first_fail, indomain_split, complete)
elseif N >= 18 then
    % Strategy 2: Two-stage search for N≥18
    seq_search([
        restart_luby(1500) ::
        relax_and_reconstruct([matches[p,w] | p in P, w in W], 80) ::
        int_search([matches[p,w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p,w] | p in P, w in W], first_fail, indomain_random, complete)
    ])
elseif N >= 16 then
    % Strategy 3: Conservative restart for N≥16
    restart_luby(800) ::
    int_search([matches[p,w] | p in P, w in W] ++ [home_away[p,w] | p in P, w in W], 
               dom_w_deg, indomain_median, complete)
elseif N >= 14 then
    % Your proven strategy for N≥14
    restart_luby(1000) ::
    relax_and_reconstruct([matches[p,w] | p in P, w in W], 85) ::
    int_search([matches[p,w] | p in P, w in W] ++ [home_away[p,w] | p in P, w in W], 
               input_order, indomain_min, complete)
else
    % Small instances
    seq_search([
        int_search([matches[p,w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p,w] | p in P, w in W], first_fail, indomain_min, complete)
    ])
endif minimize max_imbalance;

