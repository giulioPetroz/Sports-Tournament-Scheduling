
## Current Results

### CP Model Performance (`cp_small`)
- **N ≤ 16**: Successfully finds **optimal solutions** (max_imbalance = 1) within time limit
- **N = 18**: Currently **fails to find any solution** within 5-minute time limit
- **N ≥ 20**: Not yet tested

### Model Features
- Round-robin tournament structure with proper constraints
- Home/away fairness optimization (minimize maximum imbalance across teams)
- Advanced search strategies including:
  - Luby restart sequences
  - Relax-and-reconstruct techniques
- Symmetry breaking constraints
- Auxiliary variables for improved constraint propagation

## Running the Model

To run the CP model with Gecode solver:

```bash

# Run for specific instance size (e.g., N=14)
minizinc --solver gecode -a --time-limit 300000 -D "n=14;" CP/cp_small.mzn

# Run with different instance sizes
minizinc --solver gecode -a --time-limit 300000 -D "n=16;" CP/cp_small.mzn
minizinc --solver gecode -a --time-limit 300000 -D "n=18;" CP/cp_small.mzn
