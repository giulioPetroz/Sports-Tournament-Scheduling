echo "[1/4] Running CP experiments..."
python3 run_cp_experiments.py

echo "[2/4] Running SAT experiments..."
python3 run_sat_experiments.py

echo "[3/4] Running SMT experiments..."
python3 run_smt_experiments.py

echo "[4/4] Running MIP experiments..."
python3 run_mip_experiments.py

echo "All experiments completed successfully."
