# Docker Instructions

## 1. Build the Docker image

If you are building on an **ARM-based machine** (e.g., Apple Silicon Mac), you **must** specify the target architecture to ensure compatibility with `x86_64` (AMD64).
Use `--platform linux/amd64` to replicate an `x86_64` environment.

```bash
# If you are on an x86_64 machine:
docker build -t cdmo .

# Build with x86_64 emulation (for ARM hosts)
docker build --platform linux/amd64 -t cdmo .
```

---

## 2. Run the container

Again, if you’re on ARM, specify `--platform`:

```bash
# Or, on native x86_64:
docker run -it cdmo

# Run with x86_64 emulation (for ARM hosts)
docker run --platform linux/amd64 -it cdmo
```

To close the container:

```bash
exit
```

---

## 3. Run the container with the CPLEX solver

* Make sure **CPLEX 22.1.1** is installed on your device with a valid license.
* The local CPLEX directory will be mounted into the container at runtime.
* You may need `sudo` to allow Docker to access the mounted folder.

Example usage:

```bash
sudo docker run -v /user/path/to/cplex:/opt/ibm/ILOG/ -it cdmo
```

Example with default install path:

```bash
sudo docker run -v /opt/ibm/ILOG/:/opt/ibm/ILOG/ -it cdmo
```

Example usage ARM:

```bash
sudo docker run --platform linux/amd64 -v /user/path/to/cplex:/opt/ibm/ILOG/ -it cdmo
```

Example with default install path ARM:

```bash
sudo docker run --platform linux/amd64 -v /opt/ibm/ILOG/:/opt/ibm/ILOG/ -it cdmo
```

---

# CP 
# Constraint Programming (CP)

## Model Variants

The `source/CP/` directory contains different model implementations with varying constraint sets:

### Core Models
- **`cp_baseline`**: Contains only the essential constraints required to generate a valid tournament schedule
- **`cp_noIMPL`**: Baseline model enhanced with symmetry breaking constraints
- **`cp_noSB`**: Baseline model enhanced with implied constraints for improved propagation
- **`cp_complete`**: Full model incorporating symmetry breaking constraints and implied constraints

### Search Strategy Variants
Each core model has three search strategy implementations:

- **`{model_name}_basic`**: Uses the solver's default search strategy
- **`{model_name}_norr`**: Implements sequential variable ordering with Luby restart sequences (without relax-and-reconstruct)
- **`{model_name}`**: Advanced search strategy with sequential ordering, Luby restarts, and relax-and-reconstruct techniques


## Running the Models

### Complete Experimental Replication
To reproduce all experiments presented in the report:

```bash
python3 run_cp_experiment.py
```
### Indivdual Model Execution: 
To run a specific model configuration: 
```bash 
# General syntax
minizinc --solver {SOLVER} --time-limit {TIME_MS} -D "N={TEAMS};" source/CP/{MODEL_FILE}.mzn

# Available solvers: gecode, chuffed, cp-sat
# Examples:
minizinc --solver gecode --time-limit 300000 -D "N=16;" source/CP/cp_complete.mzn
minizinc --solver cp-sat --time-limit 300000 -D "N=14;" source/CP/cp_baseline_basic.mzn
minizinc --solver chuffed --time-limit 300000 -D "N=18;" source/CP/cp_noSB_norr.mzn
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| `--solver` | Solver to use (`gecode`, `chuffed`, or `cp-sat`) |
| `--time-limit` | Time limit in milliseconds (e.g., `300000` = 5 minutes) |
| `-D "N=X"` | Number of teams in the tournament (must be even) |

_(Example: `-D "N=8"`)_
