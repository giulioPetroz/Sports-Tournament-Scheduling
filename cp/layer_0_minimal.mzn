include "globals.mzn";
int: n; 
int: w = n - 1; 
int: p = n div 2;
set of int: Teams = 1..n; set of int: Weeks = 1..w;

array[Teams, Weeks] of var 0..(2*p-1): T;


constraint forall(i, j in Teams where i < j)(
    sum(wk in Weeks)(
        (T[i, wk] div 2 = T[j, wk] div 2) /\ (T[i, wk] mod 2 != T[j, wk] mod 2)
    ) = 1
);

constraint forall(i in Teams, period in 0..(p-1))(
    sum(wk in Weeks)(T[i, wk] div 2 = period) <= 2
);

constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

solve satisfy;

output ["Layer 0 - Minimal Core - n=\(n)\n"];