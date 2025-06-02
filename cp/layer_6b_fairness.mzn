include "globals.mzn";

int: n;  % number of teams
int: w = n - 1; % number of weeks
int: p = n div 2; % number of periods per week

set of int: Teams = 1..n; % Teams = {1, 2, ..., n} 
set of int: Weeks = 1..w; % Weeks = {1, 2, ..., w}
set of int: ActualPeriods = 0..(p-1); 
set of int: Positions = 0..1; % Positions = {0, 1} (0 for home, 1 for away)

% T[i,j] = team i plays in week j in period T[i,j] // 2 in position T[i,j]%2
array[Teams, Weeks] of var 0..(2*p-1): T;

% Derived views of T for convenience in some global constraints
array[Teams, Weeks] of var ActualPeriods: T_period = 
    array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks]);

array[Teams, Weeks] of var Positions: T_position = 
    array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks]);

% CORE CONSTRAINTS

% Each team plays with every other team exactly once
constraint forall(i, j in Teams where i < j)(
    sum(wk_idx in Weeks)(
        (T_period[i, wk_idx] = T_period[j, wk_idx]) /\ 
        (T_position[i, wk_idx] != T_position[j, wk_idx])
    ) = 1
);  

% Each team plays in each period between 1 and 2 times (CORRECTED)
constraint forall(i in Teams)(
    global_cardinality_low_up(
        [T_period[i, wk_idx] | wk_idx in Weeks],
        ActualPeriods,
        [1 | _ in ActualPeriods],  % CHANGED from 0 to 1
        [2 | _ in ActualPeriods]
    )
);

% Every slot can be occupied by a single team in a given week
constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

% IMPLIED CONSTRAINTS

% Each period in each week has exactly two teams
constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_period[t, wk_idx] | t in Teams],
        ActualPeriods,
        [2 | _ in ActualPeriods]
    )
);

% Every week has p teams playing at home and p teams playing away
constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_position[t, wk_idx] | t in Teams],
        Positions,
        [p, p]
    )
);

% SYMMETRY BREAKING CONSTRAINTS

% Lexicographic order on weeks
constraint forall(j in Weeks, j_prime in Weeks where j < j_prime)(
    lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
);

% First match constraint
constraint T[1,1] = 0; 
constraint T[2,1] = 1;

% Team lexicographic ordering
constraint forall(i in 1..(n-1))(
    lex_lesseq([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
);

% FAIRNESS CONSTRAINTS

% Balanced home/away games for each team
constraint forall(i in Teams)(
    let { var int: home_games = sum(wk in Weeks)(T_position[i,wk] = 0) } in
    home_games >= (w div 2) /\ home_games <= ((w div 2) + 1)
);

solve satisfy;

output [
    "Layer 6B - Fairness Ready (n=\(n))\n",
    "Schedule Matrix:\n"
] ++
[
    "Team \(i): " ++ show([T[i,j] | j in Weeks]) ++ 
    " | Home games: " ++ show(sum(wk in Weeks)(T_position[i,wk] = 0)) ++ "\n"
    | i in Teams
];