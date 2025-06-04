include "globals.mzn";

int: n;
int: w = n - 1;
int: p = n div 2;

set of int: Teams = 1..n;
set of int: Weeks = 1..w;
set of int: ActualPeriods = 0..(p-1);
set of int: Positions = 0..1;

% CORE VARIABLES
array[Teams, Weeks] of var 0..(2*p-1): T;

% DERIVED VIEWS (always computed)
array[Teams, Weeks] of var ActualPeriods: T_period = 
    array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks]);

array[Teams, Weeks] of var Positions: T_position = 
    array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks]);

% CORE CONSTRAINTS (mandatory for valid solution)
% Each pair of teams plays exactly once
constraint forall(i, j in Teams where i < j)(
    sum(wk_idx in Weeks)(
        (T_period[i, wk_idx] = T_period[j, wk_idx]) /\ 
        (T_position[i, wk_idx] != T_position[j, wk_idx])
    ) = 1
);

% Each team plays 1-2 times per period
constraint forall(i in Teams)(
    global_cardinality_low_up(
        [T_period[i, wk_idx] | wk_idx in Weeks],
        ActualPeriods,
        [1 | _ in ActualPeriods],
        [2 | _ in ActualPeriods]
    )
);

% All teams have different schedules in each week
constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

% IMPLIED CONSTRAINTS (help with performance)
% Exactly 2 teams per period per week
constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_period[t, wk_idx] | t in Teams],
        ActualPeriods,
        [2 | _ in ActualPeriods]
    )
);

% Exactly p teams per position per week (n/2 teams home, n/2 away)
constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_position[t, wk_idx] | t in Teams],
        Positions,
        [p, p]
    )
);

% SYMMETRY BREAKING
% Week symmetry: weeks are ordered lexicographically
constraint forall(j in Weeks, j_prime in Weeks where j < j_prime)(
    lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
);

% First match constraint: fix teams 1 and 2 in week 1
constraint T[1,1] = 0 /\ T[2,1] = 1;

% Team symmetry: teams are ordered lexicographically by their schedules
constraint forall(i in 1..(n-1))(
    lex_lesseq([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
);

% DIVERSITY CONSTRAINT
% No team plays in the same period for more than 2 consecutive weeks
constraint forall(i in Teams, p_val in ActualPeriods, wk in 1..(w-2))(
    (T_period[i,wk] = p_val /\ T_period[i,wk+1] = p_val) ->
    T_period[i,wk+2] != p_val
);

solve  satisfy;

output [
    "Schedule Matrix T:\n"
] ++ [
    show(T[i,j]) ++ (if j = w then "\n" else " " endif)
    | i in Teams, j in Weeks
] ++ [
    "\nPeriods:\n"
] ++ [
    show(T_period[i,j]) ++ (if j = w then "\n" else " " endif)
    | i in Teams, j in Weeks
] ++ [
    "\nPositions:\n"
] ++ [
    show(T_position[i,j]) ++ (if j = w then "\n" else " " endif)
    | i in Teams, j in Weeks
];