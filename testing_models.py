#!/usr/bin/env python3
"""
Local Constraint Ablation Study Framework
Run: python main.py
"""

import minizinc
import time
import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from datetime import datetime, timedelta
import numpy as np
import os
import shutil
from pathlib import Path

class LocalConstraintAblationStudy:
    def __init__(self, template_file="./template_model_test.mzn", output_dir="results"):
        self.template_file = Path(template_file)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.results = {}
        self.skip_config_after_timeout = True
        
        # Verify template exists
        if not self.template_file.exists():
            raise FileNotFoundError(f"Template file not found: {self.template_file}")
    
    def create_model_with_config(self, config, output_file):
        """Create model file with specific configuration"""
        with open(self.template_file, 'r') as f:
            content = f.read()
        
        # Replace parameter defaults with config values
        for param, value in config.items():
            if param.startswith('use_'):
                import re
                pattern = f"{param} = (true|false);"
                replacement = f"{param} = {str(value).lower()};"
                content = re.sub(pattern, replacement, content)
        
        with open(output_file, 'w') as f:
            f.write(content)
    
    def should_skip_config(self, config_name, n_value):
        """Determine if we should skip this config/n combination"""
        if not self.skip_config_after_timeout:
            return False
            
        if config_name in self.results:
            for prev_n in sorted([int(k) for k in self.results[config_name].keys()]):
                if prev_n < n_value:
                    if self.results[config_name][str(prev_n)] == "TIMEOUT":
                        return True
        return False
    
    def run_single_config(self, config, n_value, timeout=120, solver="chuffed"):
        """Run single configuration"""
        config_hash = abs(hash(str(sorted(config.items()))))
        model_file = self.output_dir / f"temp_model_{config_hash}.mzn"
        
        try:
            self.create_model_with_config(config, model_file)
            
            model = minizinc.Model(str(model_file))
            solver_obj = minizinc.Solver.lookup(solver)
            instance = minizinc.Instance(solver_obj, model)
            
            instance["n"] = n_value
            
            start_time = time.time()
            result = instance.solve(timeout=timedelta(seconds=timeout))
            solve_time = time.time() - start_time
            
            if result.solution is not None:
                return solve_time
            elif result.status == minizinc.Status.UNSATISFIABLE:
                return "UNSAT"
            else:
                return "TIMEOUT"
                
        except Exception as e:
            return f"ERROR: {str(e)[:50]}"
        finally:
            if model_file.exists():
                model_file.unlink()
    
    def define_test_configurations(self):
        """Define systematic test configurations"""
        base_config = {
            "use_implied_periods": False,
            "use_implied_positions": False,
            "use_week_symmetry": False,
            "use_first_match": False,
            "use_team_symmetry": False,
            "use_strong_team_symmetry": False,
            "use_carry_over": False,
            "use_diversity": False,
            "use_fairness": False,
            "use_explicit_channeling": False,
        }
        
        configurations = {}
        
        # 0. Baseline
       #configurations["00_baseline"] = base_config.copy()
        
        """
        # 1-3. Implied constraints
        config = base_config.copy()
        config["use_implied_periods"] = True
        configurations["01_implied_periods"] = config
        
        config = base_config.copy()
        config["use_implied_positions"] = True
        configurations["02_implied_positions"] = config
        
        config = base_config.copy()
        config["use_implied_periods"] = True
        config["use_implied_positions"] = True
        configurations["03_both_implied"] = config
        
        config = base_config.copy()
        config["use_explicit_channeling"] = True
        configurations["0n_explicit_channelling"] = config
        """
        # 4-6. Symmetry breaking
        # config = configurations["03_both_implied"].copy()
        """
        config = base_config.copy()
        config["use_first_match"] = True
        config["use_implied_periods"] = True
        config["use_implied_positions"] = True
        configurations["04_first_match"] = config
        
        config = configurations["04_first_match"].copy()
        config["use_week_symmetry"] = True
        configurations["05_week_symmetry"] = config
        
        config = configurations["05_week_symmetry"].copy()
        config["use_team_symmetry"] = True
        configurations["06_team_symmetry"] = config
        
        # 7. Strong team symmetry
        config = configurations["05_week_symmetry"].copy()
        config["use_team_symmetry"] = True
        config["use_strong_team_symmetry"] = True
        configurations["07_strong_team_symmetry"] = config
        
        # 8. With fairness
        config = configurations["06_team_symmetry"].copy()
        config["use_fairness"] = True
        configurations["08_with_fairness"] = config
        
        # 9-11. Advanced constraints
        config = configurations["06_team_symmetry"].copy()
        config["use_carry_over"] = True
        configurations["09_carry_over"] = config
        
        config = configurations["06_team_symmetry"].copy()
        config["use_diversity"] = True
        configurations["10_diversity"] = config
        
        config = configurations["06_team_symmetry"].copy()
        config["use_carry_over"] = True
        config["use_diversity"] = True
        configurations["11_both_advanced"] = config
        """
        # 12. Everything
        config = base_config.copy()
        for key in config:
            config[key] = True
            config["use_carry_over"] = False
            config["use_explicit_channeling"] = False
            config["use_fairness"] = False
        configurations["12_everything"] = config
        
        return configurations
    
    def run_full_study(self, n_values=[6, 8, 10, 12], solvers=["chuffed"], timeout=300):
        """Run complete ablation study"""
        configurations = self.define_test_configurations()
        
        print(f"🔬 LOCAL CONSTRAINT ABLATION STUDY")
        print(f"Template: {self.template_file}")
        print(f"Output directory: {self.output_dir}")
        print(f"Configurations: {len(configurations)}")
        print(f"N values: {n_values}")
        print(f"Solvers: {solvers}")
        print(f"Timeout: {timeout}s per test")
        print(f"Skip logic: {self.skip_config_after_timeout}")
        print(f"Total tests: {len(configurations) * len(n_values) * len(solvers)}")
        print("=" * 80)
        
        all_results = {}
        
        for solver in solvers:
            print(f"\n🔧 TESTING WITH {solver.upper()}")
            solver_results = {}
            
            # Test template first
            """"
            print("🧪 Testing template with minimal config...")
            test_result = self.run_single_config(configurations["00_baseline"], 6, 30, solver)
            if test_result == "UNSAT":
                print("❌ Template produces UNSAT even for baseline!")
                continue
            elif isinstance(test_result, str) and test_result.startswith("ERROR"):
                print(f"❌ Template has error: {test_result}")
                continue
            else:
                print(f"✅ Template works! Baseline n=6: {test_result}")
            """
            total_tests = len(configurations) * len(n_values)
            current_test = 0
            
            for config_name, config in configurations.items():
                solver_results[config_name] = {}
                
                for n in n_values:
                    current_test += 1
                    
                    # Check skip logic
                    if self.should_skip_config(config_name, n):
                        result = "SKIP"
                        print(f"[{current_test:3d}/{total_tests}] {config_name:25s} n={n:2d} {solver:8s}: SKIP")
                    else:
                        print(f"[{current_test:3d}/{total_tests}] {config_name:25s} n={n:2d} {solver:8s}...", 
                              end=" ", flush=True)
                        
                        result = self.run_single_config(config, n, timeout, solver)
                        
                        if isinstance(result, float):
                            print(f"{result:8.3f}s")
                        else:
                            print(f"{result:>8s}")
                    
                    solver_results[config_name][str(n)] = result
                    
                    # Update results for skip logic
                    if config_name not in self.results:
                        self.results[config_name] = {}
                    self.results[config_name][str(n)] = result
            
            all_results[solver] = solver_results
            
            # Save solver-specific results
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = self.output_dir / f"ablation_{solver}_{timestamp}.json"
            
            with open(filename, 'w') as f:
                json.dump({
                    'timestamp': timestamp,
                    'solver': solver,
                    'n_values': n_values,
                    'timeout': timeout,
                    'template_file': str(self.template_file),
                    'results': solver_results
                }, f, indent=2)
            
            print(f"💾 {solver} results saved to: {filename}")
        
        return all_results

class LocalResultAnalyzer:
    def __init__(self, results_file=None, results_dict=None):
        if results_file:
            with open(results_file, 'r') as f:
                data = json.load(f)
                self.results = data['results']
                self.metadata = {k: v for k, v in data.items() if k != 'results'}
        elif results_dict:
            self.results = results_dict
            self.metadata = {}
        else:
            raise ValueError("Provide either results_file or results_dict")
        
        self.df = self.results_to_dataframe()
    
    def results_to_dataframe(self):
        """Convert results to pandas DataFrame"""
        data = []
        for config, config_results in self.results.items():
            for n_str, time_result in config_results.items():
                parts = config.split('_', 1)
                order = int(parts[0]) if parts[0].isdigit() else 99
                name = parts[1] if len(parts) > 1 else config
                
                if isinstance(time_result, (int, float)):
                    status = 'SOLVED'
                    time_val = time_result
                elif time_result == "TIMEOUT":
                    status = 'TIMEOUT'
                    time_val = np.nan
                elif time_result == "UNSAT":
                    status = 'UNSAT'
                    time_val = np.nan
                elif time_result == "SKIP":
                    status = 'SKIP'
                    time_val = np.nan
                else:
                    status = 'ERROR'
                    time_val = np.nan
                
                data.append({
                    'config': config,
                    'config_name': name,
                    'order': order,
                    'n': int(n_str),
                    'time': time_val,
                    'status': status
                })
        
        return pd.DataFrame(data)
    
    def generate_summary_report(self):
        """Generate comprehensive summary"""
        print("📊 LOCAL CONSTRAINT ABLATION ANALYSIS")
        print("=" * 60)
        
        total_tests = len(self.df)
        solved_tests = self.df[self.df['status'] == 'SOLVED']
        solve_rate = len(solved_tests) / total_tests * 100 if total_tests > 0 else 0
        
        print(f"Total tests: {total_tests}")
        print(f"Solved: {len(solved_tests)} ({solve_rate:.1f}%)")
        print(f"Timeouts: {len(self.df[self.df['status'] == 'TIMEOUT'])}")
        print(f"UNSAT: {len(self.df[self.df['status'] == 'UNSAT'])}")
        print(f"Skipped: {len(self.df[self.df['status'] == 'SKIP'])}")
        
        # Best configurations by n
        print(f"\n🏆 BEST CONFIGURATIONS BY N:")
        for n in sorted(self.df['n'].unique()):
            n_data = solved_tests[solved_tests['n'] == n]
            if not n_data.empty:
                best = n_data.loc[n_data['time'].idxmin()]
                print(f"n={n}: {best['time']:.3f}s - {best['config_name']}")
        
        # Baseline comparison
        print(f"\n📊 BASELINE PERFORMANCE:")
        baseline_times = {}
        for n in sorted(self.df['n'].unique()):
            baseline = self.df[(self.df['config'] == '00_baseline') & (self.df['n'] == n)]
            if not baseline.empty and baseline.iloc[0]['status'] == 'SOLVED':
                baseline_times[n] = baseline.iloc[0]['time']
                print(f"n={n}: {baseline_times[n]:.3f}s (baseline)")
        
        # Technique impact vs baseline
        print(f"\n⚡ TECHNIQUE IMPACT VS BASELINE:")
        technique_configs = [
            ('01_implied_periods', 'implied_periods'),
            ('02_implied_positions', 'implied_positions'),
            ('03_both_implied', 'both_implied'),
            ('04_first_match', 'first_match'),
            ('05_week_symmetry', 'week_symmetry'),
            ('06_team_symmetry', 'team_symmetry'),
            ('08_with_fairness', 'fairness')
        ]
        
        for config_name, tech_name in technique_configs:
            improvements = []
            for n in baseline_times.keys():
                tech_data = self.df[(self.df['config'] == config_name) & 
                                   (self.df['n'] == n) & 
                                   (self.df['status'] == 'SOLVED')]
                if not tech_data.empty:
                    speedup = baseline_times[n] / tech_data.iloc[0]['time']
                    improvements.append(speedup)
            
            if improvements:
                avg_improvement = np.mean(improvements)
                print(f"{tech_name:20s}: {avg_improvement:.2f}x speedup (avg)")
        
        return solved_tests
    
    def save_plots(self, output_dir="results"):
        """Save analysis plots"""
        output_dir = Path(output_dir)
        solved_df = self.df[self.df['status'] == 'SOLVED']
        
        if solved_df.empty:
            print("No solved instances to plot")
            return
        
        # Performance heatmap
        plt.figure(figsize=(12, 8))
        pivot_data = solved_df.pivot(index='config_name', columns='n', values='time')
        sns.heatmap(pivot_data, annot=True, fmt='.3f', cmap='RdYlGn_r',
                   cbar_kws={'label': 'Time (seconds)'})
        plt.title('Configuration Performance Heatmap')
        plt.xlabel('Number of Teams (n)')
        plt.ylabel('Configuration')
        plt.tight_layout()
        plt.savefig(output_dir / 'performance_heatmap.png', dpi=300, bbox_inches='tight')
        plt.close()
        
        # Scaling curves
        plt.figure(figsize=(12, 8))
        top_configs = solved_df.groupby('config')['time'].mean().sort_values().head(6).index
        for config in top_configs:
            config_data = solved_df[solved_df['config'] == config].sort_values('n')
            if len(config_data) > 1:
                config_name = config.split('_', 1)[1] if '_' in config else config
                plt.plot(config_data['n'], config_data['time'], 
                        marker='o', label=config_name, linewidth=2)
        
        plt.xlabel('Number of Teams (n)')
        plt.ylabel('Solve Time (seconds)')
        plt.title('Scaling Behavior (Top 6 Configurations)')
        plt.yscale('log')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.savefig(output_dir / 'scaling_curves.png', dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"📊 Plots saved to {output_dir}/")

def main():
    """Main execution function"""
    print("🚀 Starting Local Constraint Ablation Study")
    
    # Configuration
    template_file = "./template_model_test.mzn"
    output_dir = "results"
    n_values = [6, 8, 10, 12, 14]
    solvers = ["gecode", "chuffed"]  # Add "gecode" if available
    timeout = 300  # 5 minutes
    
    # Create study instance
    study = LocalConstraintAblationStudy(template_file, output_dir)
    
    # Run study
    try:
        results = study.run_full_study(
            n_values=n_values,
            solvers=solvers,
            timeout=timeout
        )
        
        print("\n✅ Study completed successfully!")
        
        # Analyze results
        for solver, solver_results in results.items():
            print(f"\n📊 Analyzing {solver} results...")
            analyzer = LocalResultAnalyzer(results_dict=solver_results)
            analyzer.generate_summary_report()
            analyzer.save_plots(Path(output_dir) / solver)
            
    except Exception as e:
        print(f"❌ Study failed: {e}")
        return 1
    
    return 0

if __name__ == "__main__":
   main()