include "globals.mzn";
int: n; int: w = n - 1; int: p = n div 2;
set of int: Teams = 1..n; set of int: Weeks = 1..w;
set of int: ActualPeriods = 0..(p-1);
set of int: Positions = 0..1;

array[Teams, Weeks] of var 0..(2*p-1): T;

% Add derived views
array[Teams, Weeks] of var ActualPeriods: T_period = 
    array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks]);
array[Teams, Weeks] of var Positions: T_position = 
    array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks]);

% Core constraints using derived views
constraint forall(i, j in Teams where i < j)(
    sum(wk_idx in Weeks)(
        (T_period[i, wk_idx] = T_period[j, wk_idx]) /\ 
        (T_position[i, wk_idx] != T_position[j, wk_idx])
    ) = 1
);

constraint forall(i in Teams, period in 0..(p-1))(
    sum(wk in Weeks)(T_period[i, wk] = period) <= 2
);

constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

solve satisfy;
output ["Layer 1 - With Derived Views - n=\(n)\n"];