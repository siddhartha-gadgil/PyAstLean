import os
import sys
import json
import subprocess
import argparse
from pathlib import Path
from datasets import load_dataset
import concurrent.futures

# Language mapping for CodeContests (verified by sampling)
# 2: CPP, 3: PYTHON3, 4: JAVA
PYTHON3_LANG_ID = 3

class DatasetEvaluator:
    def __init__(self, root_dir="dataset", timeout=2):
        self.root_dir = Path(root_dir)
        self.timeout = timeout
        self.root_dir.mkdir(exist_ok=True)

    def download_data(self, num_problems=5, problem_ids=None):
        """Downloads problem statements, tests, and solutions."""
        print(f"[*] Loading CodeContests dataset (streaming)...")
        ds = load_dataset('deepmind/code_contests', split='test', streaming=True)
        
        count = 0
        for item in ds:
            prob_name = item['name'].replace('/', '_').replace(' ', '_')
            
            # Filter by specific ID if provided
            if problem_ids and item['name'] not in problem_ids:
                continue

            # Check for Python 3 solutions
            py_indices = [i for i, lang in enumerate(item['solutions']['language']) if lang == PYTHON3_LANG_ID]
            if not py_indices:
                continue

            prob_dir = self.root_dir / prob_name
            if prob_dir.exists():
                print(f"[-] {prob_name} already exists, skipping download.")
            else:
                print(f"[+] Downloading {prob_name}...")
                prob_dir.mkdir(parents=True, exist_ok=True)
                
                # Save problem description
                with open(prob_dir / "problem.txt", "w") as f:
                    f.write(item['description'])

                # Save original solutions
                sols_dir = prob_dir / "solutions"
                sols_dir.mkdir(exist_ok=True)
                for i, idx in enumerate(py_indices[:5]): # Limit to first 5
                    with open(sols_dir / f"original_sol_{i}.py", "w") as f:
                        f.write(item['solutions']['solution'][idx])

                # Save all tests (Public + Private + Generated)
                tests_dir = prob_dir / "tests"
                tests_dir.mkdir(exist_ok=True)
                all_inputs = item['public_tests']['input'] + item['private_tests']['input'] + item['generated_tests']['input']
                all_outputs = item['public_tests']['output'] + item['private_tests']['output'] + item['generated_tests']['output']
                
                for i, (inp, outp) in enumerate(zip(all_inputs, all_outputs)):
                    with open(tests_dir / f"test_{i}.in", "w") as f:
                        f.write(inp)
                    with open(tests_dir / f"test_{i}.out", "w") as f:
                        f.write(outp)

            count += 1
            if not problem_ids and count >= num_problems:
                break

    def run_test(self, script_path, input_file, output_file):
        """Runs a single test case and returns True if passed."""
        try:
            with open(input_file, 'r') as f_in:
                res = subprocess.run(
                    [sys.executable, str(script_path)],
                    stdin=f_in,
                    capture_output=True,
                    text=True,
                    timeout=self.timeout
                )
            
            if res.returncode != 0:
                return False

            with open(output_file, 'r') as f_out:
                expected = f_out.read().strip()
            
            # Normalizing output
            actual = "\n".join(line.rstrip() for line in res.stdout.strip().splitlines()).strip()
            expected_norm = "\n".join(line.rstrip() for line in expected.splitlines()).strip()
            
            return actual == expected_norm
        except Exception:
            return False

    def evaluate_script(self, script_path, tests_dir):
        """Evaluates a single script against all tests in a directory."""
        test_inputs = sorted(list(tests_dir.glob("*.in")))
        if not test_inputs:
            return 0, 0

        passed = 0
        for inp_path in test_inputs:
            out_path = inp_path.with_suffix(".out")
            if out_path.exists():
                if self.run_test(script_path, inp_path, out_path):
                    passed += 1
        
        return passed, len(test_inputs)

    def run_evaluation(self):
        """Evaluates all problems in the root directory."""
        summary = {}
        
        problems = [d for d in self.root_dir.iterdir() if d.is_dir()]
        
        for prob_dir in problems:
            print(f"\n[*] Evaluating {prob_dir.name}...")
            tests_dir = prob_dir / "tests"
            sols_dir = prob_dir / "solutions"
            
            results = {"original": [], "lean": []}
            
            # Evaluate original solutions
            for sol in sols_dir.glob("original_sol_*.py"):
                p, t = self.evaluate_script(sol, tests_dir)
                results["original"].append(p/t if t > 0 else 0)

            # Evaluate lean solutions (user generated)
            for sol in prob_dir.glob("lean_sol_*.py"):
                p, t = self.evaluate_script(sol, tests_dir)
                results["lean"].append(p/t if t > 0 else 0)
            
            avg_original = sum(results["original"]) / len(results["original"]) if results["original"] else 0
            avg_lean = sum(results["lean"]) / len(results["lean"]) if results["lean"] else 0
            
            print(f"    - Original Pass Rate: {avg_original:.2%}")
            print(f"    - Lean Sol Pass Rate: {avg_lean:.2%}")
            
            summary[prob_dir.name] = {
                "original_score": avg_original,
                "lean_score": avg_lean,
                "improvement": avg_lean - avg_original
            }

        return summary

def main():
    parser = argparse.ArgumentParser(description="CodeContests Dataset Evaluator")
    parser.add_argument("--download", action="store_true", help="Download the dataset")
    parser.add_argument("--num", type=int, default=5, help="Number of problems to download")
    parser.add_argument("--dir", type=str, default="dataset_eval", help="Directory to store dataset")
    parser.add_argument("--evaluate", action="store_true", help="Evaluate solutions")
    parser.add_argument("--timeout", type=int, default=2, help="Execution timeout in seconds")
    
    args = parser.parse_args()
    
    evaluator = DatasetEvaluator(root_dir=args.dir, timeout=args.timeout)
    
    if args.download:
        evaluator.download_data(num_problems=args.num)
        
    if args.evaluate:
        summary = evaluator.run_evaluation()
        print("\n" + "="*40)
        print("FINAL EVALUATION SUMMARY")
        print("="*40)
        for prob, scores in summary.items():
            print(f"{prob}: Lean={scores['lean_score']:.2%}, Orig={scores['original_score']:.2%}")

if __name__ == "__main__":
    main()
