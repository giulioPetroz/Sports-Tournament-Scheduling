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

% Decision variables with tighter domains
array [P, W] of var P: matches;
array [P, W] of var 0..1: home_away; % if home_away[p,w] = 0 then the team in rb[p,w,0] plays at home against the team in rb[p,w,1], otherwise the opposite
var 1..N div 2 : max_imbalance;
array [T] of var 1..N-1: home_games;



% Core constraints
% All periods computed in the round-robin structure must be used only once
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);

% Each team plays at most twice in each period 
constraint forall(p in P)(
    global_cardinality([rb[matches[p, w], w, s] | w in W, s in S], 
                      [t | t in 0..N-1], [0| _ in 0..N-1], [2 | _ in 0..N-1])
);

% A team plays at home iff it is the first team in the pair in the round-robin structure and home_away[p, w] = 0 or if it is the second team in the pair and home_away[p, w] = 1
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
    abs(2 * home_games[t] - (N-1)) <= max_imbalance
);


% Symmetry breaking constraints
% Ensure that the matches are ordered lexicographically to break symmetry

constraint symmetry_breaking_constraint(
    lex_greater([matches[p, w] | w in W, p in P], 
               [matches[p, w] | w in W, p in reverse(P)])
);

constraint home_away[0, 0] = 0; % first match is home for team 0


constraint forall(w in W)(
    abs(sum(p in P)(home_away[p, w]) - card(P) div 2) <= 1
);

constraint forall(w in W)(
    global_cardinality([rb[matches[p, w], w, s] | p in P, s in S], 
                      [t | t in T], [1 | t in T], [1 | t in T])
);


solve ::
    restart_luby(100) :: % restart strategy, restart after 250 time units (in gecode a time unit represents a failure)
    relax_and_reconstruct([matches[p, w] | p in P, w in W], 60) :: % when a solution is found it keeps 85% of the matches variables fixed and relaxes the others (LNS)
    seq_search([
        % dom_w_deg -> focus on the most constrained variables first, and prioritize those involved in difficult constraints
        % first_fail -> variables with the smallest domain are selected first since they are more likely to lead to a failure
        % indomain_min -> select the smallest value in the domain of the variable and proced in ascending order
        % complete -> complete search, no partial solutions. Ensures optimality
        int_search([matches[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p, w] | p in P, w in W], first_fail, indomain_min, complete)
    ])
    minimize max_imbalance;
