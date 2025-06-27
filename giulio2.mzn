include "globals.mzn";

int: N = 6;

set of int: T = 0..N-1;
set of int: S = 0..1;
set of int: W = 0..N-2;
set of int: P = 0..N div 2 - 1;

int: digs = ceil(log(10.0, int2float(N)));

% Round robin matches matrix
% array [P, W] of tuple(int, int): rb = array2d(P, W, 
%     [
%         if p == 0 then
%             (N-1, w)
%         else
%             ((p + w) mod (N-1), (N - p + w - 1) mod (N-1))
%         endif
%         | p in 0..N div 2 - 1, w in 0..N-2
%     ]
% );

constraint assert (N mod 2 == 0, "N must be even");
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


array [P, W] of var P: matches;

% Every team play once every week
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);

% Every team plays at most twice in the same period
constraint forall(p in P)(
    global_cardinality([rb[matches[p, w], w, s] | w in W, s in S], [t | t in 0..N-1], [0 | _ in 0..N-1], [2 | _ in 0..N-1])
);


constraint symmetry_breaking_constraint(
    lex_greater([matches[p, w] | w in W, p in P], [matches[p, w] | w in W, p in reverse(P)])
);

output [
    concat([
        "("++show_int(digs, rb[matches[p, w],w,0] + 1)++", "++show_int(digs, rb[matches[p, w],w,1] + 1)++")  "
        | w in W
    ])
    ++
    "\n"
    | p in P
] ++ ["\n"];

output [
    concat([
        "("++show_int(digs, rb[p,w,0] + 1)++", "++show_int(digs, rb[p,w,1] + 1)++")  "
        | w in W
    ])
    ++
    "\n"
    | p in P
] ++ ["\n"];

output [
    concat([

        "\(matches[p, w])\t"

        | w in W
    ])
    ++
    "\n"

    | p in P
];

% output show(matches);
