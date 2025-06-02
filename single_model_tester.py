import minizinc
import time
import json
from datetime import datetime, timedelta
import os

def run_benchmark():
    model_file = "cp/best_model.mzn"
    solvers = ["gecode", "chuffed", "or-tools"] 
    instances = [4, 6, 8, 10, 12, 14, 16]  
    time_limit = 300
    
    results = []
    status = "UNKNOWN"  # Track status across runs
    
    # Create comprehensive benchmark info structure
    benchmark_info = {
        "model_file": model_file,
        "solvers": solvers,
        "instances": instances,
        "time_limit": time_limit,
        "start_time": datetime.now().isoformat(),
        "results": [],
        "summary": {}
    }

    try:
        model = minizinc.Model(model_file)
    except Exception as e:
        print(f"Error loading model: {e}")
        return
    
    for solver_name in solvers:
        try:
            solver = minizinc.Solver.lookup(solver_name)
            print(f"\n=== Testing with {solver_name} ===")

            for n in instances:
                print(f"Running n={n}...")
                
                if solver_name == "gecode" and n > 12:
                    print(f"  {solver_name}, n={n}: Skipping due to Gecode's instance limit.")
                    continue
                
                if solver_name == "chuffed" and n > 14:
                    print(f'Skip chuffed for n={n} due to known performance issues.')
                    continue

                if status == "TIMEOUT":
                    print(f"  {solver_name}, n={n}: Skipping due to previous timeout.")
                    continue
                # Create instance
                instance = minizinc.Instance(solver, model)
                instance["n"] = n
                
                # Run with time limit
                start_time = time.time()
                try:
                    # Convert timeout to timedelta
                    timeout = timedelta(seconds=time_limit)
                    result = instance.solve(timeout=timeout)
                    end_time = time.time()
                    
                    solve_time = end_time - start_time
                    
                    # Check if solution was found
                    if result.solution is not None:
                        status = "SATISFIED"
                    elif result.status == minizinc.Status.UNSATISFIABLE:
                        status = "UNSATISFIABLE"
                    elif result.status == minizinc.Status.UNKNOWN:
                        status = "TIMEOUT"
                    else:
                        status = "UNKNOWN"
                    
                    print(f"  {solver_name}, n={n}: {status} in {solve_time:.2f}s")
                    
                    result_entry = {
                        "solver": solver_name,
                        "n": n,
                        "status": status,
                        "solve_time": solve_time,
                        "timeout": solve_time >= time_limit,
                        "timestamp": datetime.now().isoformat()
                    }
                    results.append(result_entry)
                    
                except Exception as e:
                    end_time = time.time()
                    solve_time = end_time - start_time
                    print(f"  {solver_name}, n={n}: ERROR - {str(e)}")
                    result_entry = {
                        "solver": solver_name,
                        "n": n,
                        "status": "ERROR",
                        "solve_time": solve_time,
                        "error": str(e),
                        "timestamp": datetime.now().isoformat()
                    }
                    results.append(result_entry)
                    continue
                # Check if we hit the time limit
            status = "UNKNOWN"

        except Exception as e:
            print(f"Solver {solver_name} not available: {e}")
    
    # Add results to benchmark info
    benchmark_info["results"] = results
    benchmark_info["end_time"] = datetime.now().isoformat()
    
    # Create comprehensive summary
    benchmark_info["summary"] = create_summary_data(results, benchmark_info)
    
    # Save everything in one comprehensive file
    output_file = f"complete_benchmark_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(output_file, 'w') as f:
        json.dump(benchmark_info, f, indent=2)
    
    print(f"\nComplete benchmark data saved to {output_file}")
    
    # Print summary to console
    print_console_summary(benchmark_info["summary"])

def create_summary_data(results, benchmark_info):
    """Create comprehensive summary data structure"""
    summary = {
        "total_runs": len(results),
        "by_status": {},
        "by_solver": {},
        "by_instance": {},
        "status_table": {},
        "time_table": {}
    }
    
    # Count by status
    for status in ["SATISFIED", "UNSATISFIABLE", "TIMEOUT", "ERROR", "UNKNOWN"]:
        summary["by_status"][status] = len([r for r in results if r["status"] == status])
    
    # Group by solver
    for solver in benchmark_info["solvers"]:
        solver_results = [r for r in results if r["solver"] == solver]
        summary["by_solver"][solver] = {
            "total": len(solver_results),
            "satisfied": len([r for r in solver_results if r["status"] == "SATISFIED"]),
            "avg_solve_time": sum([r["solve_time"] for r in solver_results if r["solve_time"] is not None]) / max(1, len([r for r in solver_results if r["solve_time"] is not None]))
        }
    
    # Group by instance
    for n in benchmark_info["instances"]:
        instance_results = [r for r in results if r["n"] == n]
        summary["by_instance"][str(n)] = {
            "solved_by": [r["solver"] for r in instance_results if r["status"] == "SATISFIED"],
            "results": {r["solver"]: {"status": r["status"], "time": r["solve_time"]} for r in instance_results}
        }
    
    # Create pivot tables
    for n in benchmark_info["instances"]:
        summary["status_table"][str(n)] = {}
        summary["time_table"][str(n)] = {}
        for solver in benchmark_info["solvers"]:
            result = next((r for r in results if r["n"] == n and r["solver"] == solver), None)
            if result:
                summary["status_table"][str(n)][solver] = result["status"]
                summary["time_table"][str(n)][solver] = result["solve_time"]
            else:
                summary["status_table"][str(n)][solver] = "NOT_RUN"
                summary["time_table"][str(n)][solver] = None
    
    return summary

def print_console_summary(summary):
    """Print formatted summary to console"""
    print("\n" + "="*60)
    print("BENCHMARK SUMMARY")
    print("="*60)
    
    print(f"Total runs: {summary['total_runs']}")
    for status, count in summary["by_status"].items():
        if count > 0:
            print(f"{status}: {count}")
    
    print("\nBy Solver:")
    for solver, stats in summary["by_solver"].items():
        print(f"  {solver}: {stats['satisfied']}/{stats['total']} satisfied, avg time: {stats['avg_solve_time']:.2f}s")
    
    print("\nStatus Table:")
    if summary["status_table"]:
        solvers = list(summary["status_table"][list(summary["status_table"].keys())[0]].keys())
        print("n\t" + "\t".join(solvers))
        for n, solver_results in summary["status_table"].items():
            print(f"{n}\t" + "\t".join([solver_results[s] for s in solvers]))
    
    print("\nTime Table (seconds):")
    if summary["time_table"]:
        solvers = list(summary["time_table"][list(summary["time_table"].keys())[0]].keys())
        print("n\t" + "\t".join(solvers))
        for n, solver_times in summary["time_table"].items():
            times_str = []
            for solver in solvers:
                time_val = solver_times[solver]
                if time_val is None:
                    times_str.append("N/A")
                else:
                    times_str.append(f"{time_val:.2f}")
            print(f"{n}\t" + "\t".join(times_str))

if __name__ == "__main__":
    run_benchmark()