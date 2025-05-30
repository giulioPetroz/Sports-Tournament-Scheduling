include "globals.mzn";
int: n; % number of teams
int: w = n -1; %number of weeks
int: p = n div 2; %number of periods per week

set of int: Teams = 1..n;
set of int: Weeks = 1..w;
set of int: Periods = 1..p;

% Variables
% T[i,j] = team i plays in week j in period T[i,j] // 2 in position T[i,j]%2
array[Teams, Weeks] of var 0..(2*p-1): T;

% Constraints

% Each team plays with every other team exactly once
constraint forall(i, j in Teams where i < j)(
    sum(w in Weeks)(
        % Teams i and j play against each other in week w if:
        % 1. They are in the same period: T[i, w] div 2 = T[j, w] div 2
        % 2. They are in different positions: T[i, w] mod 2 != T[j, w] mod 2
        (T[i, w] div 2 = T[j, w] div 2) /\ (T[i,w] mod 2 != T[j,w] mod 2) 
    ) = 1
);

% Each team plays in each period at most twice
constraint forall(i in Teams, period in 0..(p-1))(
    sum(w in Weeks)(
        (T[i, w] div 2 = period)
    ) <= 2
);

% Every slot can be occupied by a single team
constraint forall(j in Weeks)(
    alldifferent([T[i,j] | i in Teams])
);

% Symmetry breaking constraints
constraint forall(j in Weeks, j_prime in Weeks where j < j_prime)(
    lex_lesseq([T[i,j] | i in Teams], [T[i,j_prime] | i in Teams])
);


solve satisfy;
output [
  "Balanced Sports Tournament Schedule for \(n) teams over \(w) weeks\n"
] ++
[
  "Week \(wk):\n" ++
  concat([
    "  Period \(period): " ++
    let {
      % Find the two teams in this period
      set of int: teams_in_period = {i | i in Teams where fix(T[i, wk] div 2) == period};
      int: t1 = min(teams_in_period);
      int: t2 = max(teams_in_period);
      bool: t1_home = fix(T[t1, wk] mod 2) == 0;
    } in
      (if t1_home then
        show(t1) ++ " (H) vs " ++ show(t2) ++ " (A)"
      else
        show(t2) ++ " (H) vs " ++ show(t1) ++ " (A)"
      endif) ++ "\n"
    | period in 0..p-1
  ])
  ++ "\n"
  | wk in Weeks
];

