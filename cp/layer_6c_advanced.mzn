include "globals.mzn";

int: n;  % number of teams
int: w = n - 1; % number of weeks
int: p = n div 2; % number of periods per week

% Parameters for enabling/disabling constraints
bool: use_carry_over = true;
bool: use_diversity = true;
bool: use_strong_symmetry = false;

set of int: Teams = 1..n; 
set of int: Weeks = 1..w; 
set of int: ActualPeriods = 0..(p-1); 
set of int: Positions = 0..1;

array[Teams, Weeks] of var 0..(2*p-1): T;

array[Teams, Weeks] of var ActualPeriods: T_period = 
    array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks]);

array[Teams, Weeks] of var Positions: T_position = 
    array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks]);

% CORE CONSTRAINTS
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
        [1 | _ in ActualPeriods],
        [2 | _ in ActualPeriods]
    )
);

constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

% IMPLIED CONSTRAINTS
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

% ADVANCED CONSTRAINTS

% Carry-over effect: avoid same period/position in consecutive weeks
constraint if use_carry_over then
    forall(i in Teams, wk in 1..(w-1))(
        T_period[i,wk] != T_period[i,wk+1] \/
        T_position[i,wk] != T_position[i,wk+1]
    )
else true endif;

% Temporal diversity: limit consecutive periods
constraint if use_diversity then
    forall(i in Teams, p_val in ActualPeriods, wk in 1..(w-1))(
        (T_period[i,wk] = p_val /\ T_period[i,wk+1] = p_val) ->
        (if wk < w-1 then T_period[i,wk+2] != p_val else true endif)
    )
else true endif;

% SYMMETRY BREAKING
constraint forall(j in Weeks, j_prime in Weeks where j < j_prime)(
    lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
);

constraint T[1,1] = 0; 
constraint T[2,1] = 1;

constraint if use_strong_symmetry then
    forall(i in 1..(n-1))(
        lex_less([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
    )
else
    forall(i in 1..(n-1))(
        lex_lesseq([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
    )
endif;

% FAIRNESS
constraint forall(i in Teams)(
    let { var int: home_games = sum(wk in Weeks)(T_position[i,wk] = 0) } in
    home_games >= (w div 2) /\ home_games <= ((w div 2) + 1)
);

solve satisfy;

output [
    "Layer 6C - Advanced Tournament Schedule\n",
    "n=\(n) teams, w=\(w) weeks, p=\(p) periods\n",
    "Features: carry_over=\(use_carry_over), diversity=\(use_diversity), strong_symmetry=\(use_strong_symmetry)\n",
    "\n--- SCHEDULE MATRIX ---\n"
] ++
[
    "Team \(i): " ++ show([fix(T[i,j]) | j in Weeks]) ++ "\n"
    | i in Teams
] ++
[
    "\n--- WEEKLY BREAKDOWN ---\n"
] ++
[
    "Week \(wk): " ++ 
    concat(["P\(p_val)(" ++ 
           concat([show(t) ++ (if fix(T_position[t,wk])=0 then "H" else "A" endif) ++ " " 
                  | t in Teams where fix(T_period[t,wk])=p_val]) ++ ") "
           | p_val in ActualPeriods]) ++ "\n"
    | wk in Weeks
] ++
[
    "\n--- FAIRNESS REPORT ---\n"
] ++
[
    "Team \(i): \(fix(sum(wk in Weeks)(T_position[i,wk] = 0)))H/" ++
    "\(fix(sum(wk in Weeks)(T_position[i,wk] = 1)))A " ++
    "(balance: \(fix(abs(sum(wk in Weeks)(T_position[i,wk] = 0) - sum(wk in Weeks)(T_position[i,wk] = 1)))))\n"
    | i in Teams
];