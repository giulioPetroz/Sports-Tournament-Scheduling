include "globals.mzn";

int: n;
int: w = n - 1;
int: p = n div 2;

% CONFIGURATION PARAMETERS
bool: use_derived_views = true;
bool: use_implied_periods = true;
bool: use_implied_positions = true;
bool: use_week_symmetry = true;
bool: use_first_match = true;
bool: use_team_symmetry = true;
bool: use_strong_team_symmetry = false;
bool: use_carry_over = false;
bool: use_diversity = false;
bool: use_fairness = false;
bool: use_explicit_channeling = false;

set of int: Teams = 1..n;
set of int: Weeks = 1..w;
set of int: ActualPeriods = 0..(p-1);
set of int: Positions = 0..1;

% CORE VARIABLES (always present)
array[Teams, Weeks] of var 0..(2*p-1): T;



% DERIVED VIEWS (conditional)
array[Teams, Weeks] of var ActualPeriods: T_period = 
    if use_explicit_channeling then
        array2d(Teams, Weeks, [let { var ActualPeriods: p } in p | i in Teams, j in Weeks])
    else
        array2d(Teams, Weeks, [T[i,j] div 2 | i in Teams, j in Weeks])
    endif;

array[Teams, Weeks] of var Positions: T_position = 
    if use_explicit_channeling then
        array2d(Teams, Weeks, [let { var Positions: pos } in pos | i in Teams, j in Weeks])
    else
        array2d(Teams, Weeks, [T[i,j] mod 2 | i in Teams, j in Weeks])
    endif;

% EXPLICIT CHANNELING (conditional)
constraint if use_explicit_channeling then
    forall(i in Teams, j in Weeks)(
        T[i,j] = T_period[i,j] * 2 + T_position[i,j]
    )
else true endif;

% CORE CONSTRAINTS (always active - these are MANDATORY)
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

% IMPLIED CONSTRAINTS (conditional)
constraint if use_implied_periods then
    forall(wk_idx in Weeks)(
        global_cardinality_closed(
            [T_period[t, wk_idx] | t in Teams],
            ActualPeriods,
            [2 | _ in ActualPeriods]
        )
    )
else true endif;

constraint if use_implied_positions then
    forall(wk_idx in Weeks)(
        global_cardinality_closed(
            [T_position[t, wk_idx] | t in Teams],
            Positions,
            [p, p]
        )
    )
else true endif;

% SYMMETRY BREAKING (conditional)
constraint if use_week_symmetry then
    forall(j in Weeks, j_prime in Weeks where j < j_prime)(
        lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
    )
else true endif;

constraint if use_first_match then
    T[1,1] = 0 /\ T[2,1] = 1
else true endif;

constraint if use_team_symmetry then
    if use_strong_team_symmetry then
        forall(i in 1..(n-1))(
            lex_less([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
        )
    else
        forall(i in 1..(n-1))(
            lex_lesseq([T[i,j_idx] | j_idx in Weeks], [T[i+1,j_idx] | j_idx in Weeks])
        )
    endif
else true endif;

% ADVANCED CONSTRAINTS (conditional)
constraint if use_carry_over then
    forall(i in Teams, wk in 1..(w-1))(
        T_period[i,wk] != T_period[i,wk+1] \/
        T_position[i,wk] != T_position[i,wk+1]
    )
else true endif;

constraint if use_diversity then
    forall(i in Teams, p_val in ActualPeriods, wk in 1..(w-1))(
        (T_period[i,wk] = p_val /\ T_period[i,wk+1] = p_val) ->
        (if wk < w-1 then T_period[i,wk+2] != p_val else true endif)
    )
else true endif;

constraint if use_fairness then
    forall(i in Teams)(
        let { var int: home_games = sum(wk in Weeks)(T_position[i,wk] = 0) } in
        home_games >= (w div 2) /\ home_games <= ((w div 2) + 1)
    )
else true endif;

solve satisfy;

output [
    "Configuration: ",
    "implied_periods=", show(use_implied_periods), " ",
    "implied_positions=", show(use_implied_positions), " ",
    "week_symmetry=", show(use_week_symmetry), " ",
    "first_match=", show(use_first_match), " ",
    "team_symmetry=", show(use_team_symmetry), " ",
    "strong_team_symmetry=", show(use_strong_team_symmetry), " ",
    "carry_over=", show(use_carry_over), " ",
    "diversity=", show(use_diversity), " ",
    "fairness=", show(use_fairness), "\n"
];