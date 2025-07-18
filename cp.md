
# Explanation of the CP code

## 1. Decision Variables

```minizinc
array [P, W] of var P: matches;
array [P, W] of var 0..1: home_away;
var 1..N -1 : max_imbalance;
array [T] of var 0..N-1: home_games;
```

- `matches[p, w]`: Which match (from the round-robin table `rb`) is played in each period of a given week.
- `home_away[p, w]`: Whether the first or second team plays at home.
- `home_games[t]`: Number of home games team `t` has.
- `max_imbalance`: Objective variable to minimize.

Anyway I think this part is well explained in the report.

---

## 2. Core Constraints

### Each Period is Used Exactly Once per Week

```minizinc
constraint forall(w in W)(
    all_different([matches[p, w] | p in P])
);
```

For a fixed week `w`, it creates an array of the values assigned to `matches[p, w]` for all periods `p`, and checks that all these values are different.

**Example:**

If in week 0 we have:

```minizinc
matches[0,0] = 0
matches[1,0] = 1
matches[2,0] = 2
```

→ The array is `[0, 1, 2]` → valid.  
If instead we had `[1, 1, 2]`, the match `1` appears twice → invalid.

### Each Team Plays at Most Twice per Period

```minizinc
constraint forall(p in P)(
    global_cardinality([rb[matches[p, w], w, s] | w in W, s in S], 
                       [t | t in 0..N-1],        
                       [0 | _ in 0..N-1],        
                       [2 | _ in 0..N-1])
);
```
Ensures that, for each period `p`, no team appears more than twice across all weeks.

We collect, for a fixed period `p`, the list of all teams that play in that period across all weeks and both slots. Notice that in the expression `rb[matches[p, w], w, s]`, we don’t use p directly as the period index. Instead, we use the actual period assigned to the match via the `matches` matrix.   
Then we apply `global_cardinality` to count how many times each team appears.
- `[t | t in 0..N-1]`: We count occurrences for all teams.
- `[0 | _ in 0..N-1]`: Each team must appear **at least 0 times** (no strict lower bound).
- `[2 | _ in 0..N-1]`: Each team can appear **at most 2 times** in a given period.

> A tighter lower bound like `1` might seem more accurate, but in practice it worsened performance, so a lower bound of 0 was kept. 

## 3. Channelling Constraint

### Count Home Games per Team

```minizinc
constraint forall(t in T)(
    home_games[t] = sum(p in P, w in W)(
        bool2int(
            (rb[matches[p, w], w, 0] = t /\ home_away[p, w] = 0) \/
            (rb[matches[p, w], w, 1] = t /\ home_away[p, w] = 1)
        )
    )
);
```
I think this is well explained in the report. 
How it works: The condition inside `bool2int(...)` returns 1 when team `t` plays at home in that match, and 0 otherwise.  The `sum(...)` adds up these values across all periods and weeks.

---

# 4. Optimization Constraint 

### Balance Home and Away Games

```minizinc
constraint forall(t in T)(
    abs(2 * home_games[t] - (N-1)) <= max_imbalance
);
```

Ensures each team has approximately half of its games at home.


### Weekly Home/Away Balance

```minizinc
constraint forall(w in W)(
    abs(sum(p in P)(home_away[p, w]) - card(P) div 2) <= 1
);
```
Explained in the report.
> Note: This constraint is not strictly necessary to obtain an optimal solution. In fact, removing it still leads to a valid and optimized schedule. However, including it  improves search efficiency, helping the solver converge faster to a good solution.

---

## 5. Symmetry Breaking

### Period Assignment Symmetry

```minizinc
constraint symmetry_breaking_constraint(
    lex_greater([matches[p, w] | w in W, p in P], 
                [matches[p, w] | w in W, p in reverse(P)])
);
```

The `matches` matrix permutes the order of periods within each week.  
If a valid schedule has `matches[0,w] = X` and `matches[1,w] = Y`, then swapping them to `X` ↔ `Y` results in an equivalent schedule from a high-level point of view.  
To avoid exploring both, we enforce a fixed ordering.

####  How it works:
- `lex_greater(A, B)` forces array `A` to be lexicographically greater than array `B`.
- `A = [matches[p, w] | w in W, p in P]`: flattens the matrix row by row.
- `B = [matches[p, w] | w in W, p in reverse(P)]`: does the same, but reverses the period order.

#### Example:

Imagine a schedule with 2 periods and 2 weeks:

```
matches[0,0] = 0   matches[1,0] = 1
matches[0,1] = 0   matches[1,1] = 1
```

- Flattened forward: `[0,1,0,1]`
- Flattened reversed: `[1,0,1,0]`

Since `[0,1,0,1] < [1,0,1,0]` lexicographically → this solution is rejected. 

The accepted one would be: 
```
matches[0,0] = 1   matches[1,0] = 0
matches[0,1] = 0   matches[1,1] = 1
```

Since `[1,0,1,0] > [0,1,0,1]`.
This avoids generating both versions, keeping only one and making the solver faster.

> **Note:** This constraint is essentially equivalent to `matches[0,0] > matches[1,0]`, but using lexicographic ordering tends to propagate better due to global constraint handling and partial assignments.  
> Plus, it might make Zeynep happy :) 

---

### Fix First Home Assignment

```minizinc
constraint home_away[0, 0] = 0;
```

Removes symmetry in the `home_away` assignments.

Without it, the model could find two equivalent solutions where all home/away values are flipped. To avoid exploring both, we fix the first value `home_away[0, 0]` to `0`  forcing the first team in the first match to play at home.

---


## 6. Implied Constraint
### Each Team Plays Exactly Once per Week

```minizinc
constraint forall(w in W)(
    global_cardinality([rb[matches[p, w], w, s] | p in P, s in S], 
                       [t | t in T],             
                       [1 | t in T],             
                       [1 | t in T])
);
```


It works like the previous `global_cardinality`: for a fixed week `w`, we collect all teams playing (in both slots of every match), and enforce that each team appears **exactly once**, using `[1 | t in T]` for both the minimum and maximum counts.

> Alternative implementations using `count` and `sum` were tested, but this version with `global_cardinality` proved to be much more efficient in practice.

---

## 7. Search Strategy and Optimization

```minizinc
solve ::
    restart_luby(100) ::
    relax_and_reconstruct([matches[p, w] | p in P, w in W], 60) ::
    seq_search([
        int_search([matches[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete),
        int_search([home_away[p, w] | p in P, w in W], first_fail, indomain_min, complete)
    ]) minimize max_imbalance;
```

This defines the complete search strategy used to solve and optimize the model.

#### `restart_luby(100)`

- **Purpose**: Periodically restarts the search to avoid getting stuck in unproductive parts of the search tree.
- **How it works**: Follows the *Luby sequence* (1,1,2,1,1,2,4,...), scaled by 100. This means restarts happen after 100, 100, 200, 100... failures.

#### `relax_and_reconstruct([...], 60)`

- **Purpose**: Implements **Large Neighborhood Search (LNS)** to iteratively improve solutions.
- **How it works**:
  - At each iteration, 60% of the `matches` variables are kept fixed.
  - The remaining 40% are relaxed (unassigned) and re-optimized.

- **Why it is applied on matches**: Although the optimization is on `home_away`, the bottleneck is often in finding feasible values for `matches`. In fact, once a feasible `matches` matrix is found, optimizing `home_away` is fast. After setting a new upper bound on `max_imbalance`, the solver adds a constraint like `max_imbalance < previous_best`, if the search fails to find a valid assignment to `home_away`  under this new constraint, it backtracks and tries to reconstruct a new `matches` matrix solwing down everything. The idea is to preserve a good matches matrix once found, so that when the search restarts due to a failure, it can immediately build upon a valid structure and focus on optimizing the home_away assignments.

- **Why 60%**: This value gave the best trade-off in experiments. Even using 100% (fully fixed `matches`) yielded similar results, but 60% allows slightly more flexibility without hurting performance.


#### `seq_search([...])`

- Applies search strategies sequentially:
  1. First on `matches` ,
  2. Then on `home_away`.
- **Benefit**: Clear priority in variable exploration: first feasibility of schedule, then optimization.

---

#### `int_search` on `matches`

```minizinc
int_search([matches[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete)
```

- **Variable selection**: `dom_w_deg` (Domain over Weighted Degree)
  - Prioritizes variables with small domains and high failure counts in constraints.
- **Value selection**: `indomain_min` (smallest possible value first).
- **complete**: This specifies that the search should be exhaustive. The solver will explore the entire search space defined by these variables and heuristics until an optimal solution is found and proven, or it exhausts resources.
---

#### `int_search` on `home_away`

```minizinc
int_search([home_away[p, w] | p in P, w in W], first_fail, indomain_min, complete)
```

- **Variable selection**: `first_fail`
  - Picks variables with the smallest domain first.
- **Value selection**: `indomain_min`.

All search parameters including: the restart interval in `restart_luby`, the percentage used in `relax_and_reconstruct` and the variable/value selection heuristics  were chosen empirically. I tested multiple combinations of variable and value strategies and selected the ones that consistently produced the best results.
The combination of `dom_w_deg` (for variable selection) and `restart_luby` is particularly effective and is also recommended in the  slides.
It is also suggested to pair `restart_luby` with a random value selection strategy like `indomain_random`. But in this case it did not yield good performance.


