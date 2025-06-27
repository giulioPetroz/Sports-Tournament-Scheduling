include "globals.mzn";

int: n;
int: N = n;
set of int: T = 0..N-1;
set of int: S = 0..1;
set of int: W = 0..N-2;
set of int: P = 0..N div 2 - 1;

constraint assert (N mod 2 == 0, "N must be even");

% Fixed round-robin structure
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
array [T] of var 0..N: home_games;
var 1..N-1: max_imbalance;

% Each team plays once per week
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);

% Each team plays at most twice per period over the tournament
constraint forall(t in T, p in P)(
    sum(w in W, s in S)(
        bool2int(rb[matches[p, w], w, s] = t)
    ) <= 2
);

% Compute home games
constraint forall(t in T)(
    home_games[t] = sum(p in P, w in W)(
        bool2int(
            (rb[matches[p, w], w, 0] = t /\ home_away[p, w] = 0) \/
            (rb[matches[p, w], w, 1] = t /\ home_away[p, w] = 1)
        )
    )
);

% Fairness constraint: balance home and away games
constraint forall(t in T)(
    abs(home_games[t] - (N - 1) div 2) <= max_imbalance
);


% Fix the first week matches
constraint forall(p in P)(
    matches[p, 0] = p
);

% Symmetry breaking: ensure the first match of the first week is home
constraint home_away[0, 0] = 0;


% Solve with Luby restart, relax+reconstruct, smart search
solve ::
    restart_luby(1000) ::
    relax_and_reconstruct([matches[p, w] | p in P, w in W], 90) ::
    seq_search([
        int_search([matches[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p, w] | p in P, w in W], first_fail, indomain_min, complete)
    ])
    minimize max_imbalance;
