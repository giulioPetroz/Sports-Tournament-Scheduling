include "globals.mzn";
int: n; int: w = n - 1; int: p = n div 2;
set of int: Teams = 1..n; set of int: Weeks = 1..w;
set of int: ActualPeriods = 0..(p-1);
set of int: Positions = 0..1;

array[Teams, Weeks] of var 0..(2*p-1): T;

array[Teams, Weeks] of var ActualPeriods: T_period = 
    array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks]);
array[Teams, Weeks] of var Positions: T_position = 
    array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks]);

% All previous constraints
constraint forall(i, j in Teams where i < j)(
    sum(wk_idx in Weeks)(
        (T_period[i, wk_idx] = T_period[j, wk_idx]) /\ 
        (T_position[i, wk_idx] != T_position[j, wk_idx])
    ) = 1
);

constraint forall(i in Teams)(
    global_cardinality_low_up(
        [T_period[i, wk_idx] | wk_idx in Weeks],
        ActualPeriods,
        [0 | _ in ActualPeriods],
        [2 | _ in ActualPeriods]
    )
);

constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_period[t, wk_idx] | t in Teams],
        ActualPeriods,
        [2 | _ in ActualPeriods]
    )
);

constraint forall(wk_idx in Weeks)(
    global_cardinality_closed(
        [T_position[t, wk_idx] | t in Teams],
        Positions,
        [p, p]
    )
);


constraint forall(j in Weeks, j_prime in Weeks where j < j_prime)(
    lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
);

constraint T[1,1] = 0;
constraint T[2,1] = 1;

% Add team lexicographic ordering
constraint forall(i in 1..(n-1))(
    lex_lesseq([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
);

solve satisfy;
output ["Layer 5 - With Team Lexicographic Ordering - n=\(n)\n"];