# benchmark_layers.py (modified with early timeout detection)
import minizinc
import time
import json
import os
from datetime import datetime, timedelta

def run_minizinc_python(model_file, solver_name, n_value, timeout=300):
    """Run MiniZinc using Python library"""
    try:
        # Load model and solver
        model = minizinc.Model(model_file)
        solver = minizinc.Solver.lookup(solver_name)
        instance = minizinc.Instance(solver, model)
        instance["n"] = n_value
        
        # Run with timeout
        start_time = time.time()
        timeout_delta = timedelta(seconds=timeout)
        result = instance.solve(timeout=timeout_delta)
        end_time = time.time()
        
        solve_time = end_time - start_time
        
        # Check result status
        if result.solution is not None:
            return solve_time
        elif result.status == minizinc.Status.UNSATISFIABLE:
            return "UNSAT"
        elif result.status == minizinc.Status.UNKNOWN:
            return None  # Timeout
        else:
            return None
            
    except Exception as e:
        print(f"Error running {model_file} with {solver_name} n={n_value}: {e}")
        return None

def benchmark_all_layers():
    """Benchmark all layer models using Python MiniZinc library with early timeout detection"""
    
    # Configuration
    models = [
      #  "cp/layer_0_minimal.mzn",
      #  "cp/layer_1_derived_views.mzn", 
      #  "cp/layer_2_global_constraints.mzn",
      #  "cp/layer_3_implied_constraints.mzn",
      #  "cp/layer_4_basic_symmetry.mzn",
      #  "cp/layer_5_team_ordering.mzn",
        "cp/layer_6_complete.mzn",
        "cp/layer_6b_fairness.mzn",
        "cp/laber_6c_advanced.mzn"
    ]
    
    solvers = ["gecode", "chuffed"]
    n_values = [4, 6, 8, 10, 12, 14, 16]
    timeout = 300  # 5 minutes
    
    results = {}
    timeout_tracker = {}  # Track which model+solver combinations have timed out
    
    print("Starting layer benchmark with Python MiniZinc library...")
    print("(Using early timeout detection - stopping larger n after timeout)")
    print(f"Models: {len(models)}")
    print(f"Solvers: {solvers}")
    print(f"N values: {n_values}")
    print(f"Timeout: {timeout}s per run")
    print("-" * 50)
    
    total_runs = len(models) * len(solvers) * len(n_values)
    current_run = 0
    
    for model in models:
        if not os.path.exists(model):
            print(f"WARNING: Model file {model} not found, skipping...")
            continue
            
        model_name = os.path.basename(model).replace(".mzn", "")
        results[model_name] = {}
        timeout_tracker[model_name] = {}
        
        for solver_name in solvers:
            timeout_tracker[model_name][solver_name] = False  # Track timeout status
        
        for n in n_values:
            results[model_name][str(n)] = {}
            
            for solver_name in solvers:
                current_run += 1
                print(f"[{current_run}/{total_runs}] Running {model_name} n={n} {solver_name}...", end=" ")
                
                # Check if this model+solver combination has already timed out for smaller n
                if timeout_tracker[model_name][solver_name]:
                    print("SKIP (Previous timeout)")
                    results[model_name][str(n)][solver_name] = "TIMEOUT_SKIP"
                    continue
                
                # Apply smart skipping based on your experience
                if solver_name == "gecode" and n > 12:
                    print("SKIP (Gecode limit)")
                    results[model_name][str(n)][solver_name] = "SKIP"
                    continue
                    
                if solver_name == "chuffed" and n > 16:
                    print("SKIP (Chuffed limit)")
                    results[model_name][str(n)][solver_name] = "SKIP"
                    continue
                
                try:
                    solve_time = run_minizinc_python(model, solver_name, n, timeout)
                    results[model_name][str(n)][solver_name] = solve_time
                    
                    if solve_time is None:
                        print("TIMEOUT")
                        # Mark this model+solver combination as having timed out
                        timeout_tracker[model_name][solver_name] = True
                    elif solve_time == "UNSAT":
                        print("UNSAT")
                    else:
                        print(f"{solve_time:.2f}s")
                        
                except Exception as e:
                    print(f"ERROR: {e}")
                    results[model_name][str(n)][solver_name] = "ERROR"
    
    return results

def create_layer_comparison_report(results):
    """Create a detailed layer comparison report"""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Save JSON results
    json_filename = f"layer_comparison_{timestamp}.json"
    with open(json_filename, 'w') as f:
        json.dump({
            "timestamp": timestamp,
            "results": results,
            "analysis": analyze_layer_performance(results)
        }, f, indent=2)
    
    # Generate HTML report
    html_filename = f"layer_comparison_{timestamp}.html"
    generate_html_report(results, html_filename, timestamp)
    
    return json_filename, html_filename

def analyze_layer_performance(results):
    """Analyze which layers help vs hurt performance"""
    analysis = {
        "layer_impact": {},
        "solver_comparison": {},
        "scalability": {},
        "timeout_patterns": {}
    }
    
    # Analyze timeout patterns
    for layer_name, layer_results in results.items():
        analysis["timeout_patterns"][layer_name] = {}
        for solver in ["gecode", "chuffed"]:
            first_timeout_n = None
            for n_str in sorted(layer_results.keys(), key=int):
                result = layer_results[n_str].get(solver)
                if result is None or result == "TIMEOUT_SKIP":
                    if first_timeout_n is None:
                        first_timeout_n = int(n_str)
                    break
            analysis["timeout_patterns"][layer_name][solver] = first_timeout_n
    
    # Compare each layer to the baseline (layer_0)
    baseline_key = "layer_0_minimal"
    if baseline_key in results:
        for layer_name, layer_results in results.items():
            if layer_name == baseline_key:
                continue
                
            analysis["layer_impact"][layer_name] = {}
            
            for n_str, n_results in layer_results.items():
                analysis["layer_impact"][layer_name][n_str] = {}
                
                for solver, time_result in n_results.items():
                    baseline_time = results[baseline_key].get(n_str, {}).get(solver)
                    
                    if (isinstance(time_result, (int, float)) and 
                        isinstance(baseline_time, (int, float))):
                        # Calculate speedup/slowdown
                        ratio = time_result / baseline_time
                        if ratio < 1:
                            impact = f"FASTER ({1/ratio:.1f}x)"
                        else:
                            impact = f"SLOWER ({ratio:.1f}x)"
                    else:
                        impact = "INCONCLUSIVE"
                    
                    analysis["layer_impact"][layer_name][n_str][solver] = {
                        "baseline": baseline_time,
                        "current": time_result,
                        "impact": impact
                    }
    
    return analysis

def generate_html_report(results, filename, timestamp):
    """Generate comprehensive HTML report"""
    
    html_content = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <title>Layer Performance Analysis - {timestamp}</title>
        <style>
            body {{ font-family: Arial, sans-serif; margin: 20px; }}
            table {{ border-collapse: collapse; margin: 20px 0; width: 100%; }}
            th, td {{ border: 1px solid #ddd; padding: 8px; text-align: center; }}
            th {{ background-color: #f2f2f2; font-weight: bold; }}
            .timeout {{ background-color: #ffcccc; }}
            .timeout_skip {{ background-color: #ff9999; }}
            .unsat {{ background-color: #ffffcc; }}
            .fast {{ background-color: #ccffcc; }}
            .medium {{ background-color: #fff2cc; }}
            .slow {{ background-color: #ffddcc; }}
            .skip {{ background-color: #e6e6e6; }}
            .error {{ background-color: #ff9999; }}
            .layer-name {{ font-weight: bold; text-align: left; }}
            h2 {{ color: #333; border-bottom: 2px solid #333; }}
        </style>
    </head>
    <body>
        <h1>Layer Performance Analysis Report</h1>
        <p>Generated: {timestamp}</p>
        <p><strong>Note:</strong> Early timeout detection enabled - larger n values skipped after timeout</p>
        
        <h2>Performance Comparison by Solver</h2>
    """
    
    # Generate tables for each solver
    for solver in ["gecode", "chuffed"]:
        html_content += f"<h3>{solver.upper()}</h3>\n<table>\n"
        
        # Header
        html_content += "<tr><th>Layer</th>"
        if results:
            n_values = sorted([int(n) for n in list(results.values())[0].keys()])
            for n in n_values:
                html_content += f"<th>n={n}</th>"
        html_content += "</tr>\n"
        
        # Data rows
        for layer_name, layer_results in results.items():
            html_content += f"<tr><td class='layer-name'>{layer_name}</td>"
            
            for n in n_values:
                n_str = str(n)
                if n_str in layer_results and solver in layer_results[n_str]:
                    time_result = layer_results[n_str][solver]
                    cell_class, cell_text = format_result_cell(time_result)
                else:
                    cell_class = ""
                    cell_text = "N/A"
                
                html_content += f"<td class='{cell_class}'>{cell_text}</td>"
            
            html_content += "</tr>\n"
        
        html_content += "</table>\n"
    
    # Add insights section
    html_content += """
        <h2>Key Insights</h2>
        <h3>Legend:</h3>
        <ul>
            <li><span class="fast" style="padding: 2px 5px;">Green</span>: Fast (&lt; 1s)</li>
            <li><span class="medium" style="padding: 2px 5px;">Yellow</span>: Medium (1-30s)</li>
            <li><span class="slow" style="padding: 2px 5px;">Orange</span>: Slow (&gt; 30s)</li>
            <li><span class="timeout" style="padding: 2px 5px;">Red</span>: Timeout (&gt; 300s)</li>
            <li><span class="timeout_skip" style="padding: 2px 5px;">Dark Red</span>: Skipped after previous timeout</li>
            <li><span class="unsat" style="padding: 2px 5px;">Light Yellow</span>: Unsatisfiable</li>
            <li><span class="skip" style="padding: 2px 5px;">Gray</span>: Skipped (solver limits)</li>
        </ul>
        
        <h3>Analysis Questions:</h3>
        <ol>
            <li><strong>Layer 0 vs Layer 1:</strong> Do derived views add overhead?</li>
            <li><strong>Layer 1 vs Layer 2:</strong> Do global constraints help?</li>
            <li><strong>Layer 2 vs Layer 3:</strong> Are implied constraints worth it?</li>
            <li><strong>Layer 3 vs Layer 4:</strong> How much do basic symmetry breaking constraints help?</li>
            <li><strong>Layer 4 vs Layer 5:</strong> Is team lexicographic ordering too expensive?</li>
            <li><strong>Layer 5 vs Layer 6:</strong> Does home/away symmetry breaking provide additional benefit?</li>
        </ol>
        
        <h3>Performance Trends:</h3>
        <ul>
            <li>Look for consistent patterns across n values</li>
            <li>Identify which layers cause performance cliffs</li>
            <li>Compare solver preferences for different constraint types</li>
            <li>Find the optimal layer for your target problem sizes</li>
            <li>Notice timeout thresholds - where each layer starts failing</li>
        </ul>
    </body>
    </html>
    """
    
    with open(filename, 'w') as f:
        f.write(html_content)

def format_result_cell(time_result):
    """Format result for HTML table"""
    if time_result is None:
        return "timeout", "TIMEOUT"
    elif time_result == "TIMEOUT_SKIP":
        return "timeout_skip", "SKIP(TO)"
    elif time_result == "UNSAT":
        return "unsat", "UNSAT"
    elif time_result == "SKIP":
        return "skip", "SKIP"
    elif time_result == "ERROR":
        return "error", "ERROR"
    elif isinstance(time_result, (int, float)):
        if time_result < 1:
            return "fast", f"{time_result:.2f}s"
        elif time_result < 30:
            return "medium", f"{time_result:.2f}s"
        else:
            return "slow", f"{time_result:.2f}s"
    else:
        return "", str(time_result)

def print_layer_summary(results):
    """Print quick summary to console"""
    print("\n" + "="*70)
    print("LAYER PERFORMANCE SUMMARY")
    print("="*70)
    
    if not results:
        print("No results to display")
        return
    
    n_values = sorted([int(n) for n in list(results.values())[0].keys()])
    
    for solver in ["gecode", "chuffed"]:
        print(f"\n{solver.upper()}:")
        print("-" * 50)
        
        # Header
        print(f"{'Layer':<25}", end="")
        for n in n_values:
            print(f"n={n}".rjust(10), end="")
        print()
        
        # Data
        for layer_name, layer_results in results.items():
            print(f"{layer_name:<25}", end="")
            
            for n in n_values:
                n_str = str(n)
                if n_str in layer_results and solver in layer_results[n_str]:
                    time_result = layer_results[n_str][solver]
                    
                    if time_result is None:
                        print("TIMEOUT".rjust(10), end="")
                    elif time_result == "TIMEOUT_SKIP":
                        print("SKIP(TO)".rjust(10), end="")
                    elif time_result == "UNSAT":
                        print("UNSAT".rjust(10), end="")
                    elif time_result == "SKIP":
                        print("SKIP".rjust(10), end="")
                    elif time_result == "ERROR":
                        print("ERROR".rjust(10), end="")
                    elif isinstance(time_result, (int, float)):
                        print(f"{time_result:.2f}s".rjust(10), end="")
                    else:
                        print(str(time_result)[:8].rjust(10), end="")
                else:
                    print("N/A".rjust(10), end="")
            print()

if __name__ == "__main__":
    print("Layer Decomposition Benchmark (Python MiniZinc Library)")
    print("=" * 60)
    
    # Check if minizinc library is available
    try:
        import minizinc
        print("✓ MiniZinc Python library found")
    except ImportError:
        print("✗ MiniZinc Python library not found")
        print("Install with: pip install minizinc")
        exit(1)
    
    # Run benchmark
    results = benchmark_all_layers()
    
    if results:
        # Print summary
        print_layer_summary(results)
        
        # Generate reports
        json_file, html_file = create_layer_comparison_report(results)
        
        print(f"\nReports generated:")
        print(f"  JSON: {json_file}")
        print(f"  HTML: {html_file}")
        print(f"\nOpen {html_file} in your browser for detailed analysis.")
    else:
        print("No results generated.")