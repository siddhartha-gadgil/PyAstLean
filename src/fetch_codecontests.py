from datasets import load_dataset
import json
import os

N = 10

def save_codecontests_subset(n=N):
    print(f"Loading CodeContests (test split)...")
    ds = load_dataset('deepmind/code_contests', split='test', streaming=True)
    
    count = 0
    for item in ds:
        name = item['name']
        description = item['description']
        
        # Filter for Python 3 solutions
        python_solutions = []
        for i, lang in enumerate(item['solutions']['language']):
            if lang == 3: # Python 3
                python_solutions.append(item['solutions']['solution'][i])
        
        if not python_solutions:
            continue
            
        # Combine all tests
        all_inputs = item['public_tests']['input'] + item['private_tests']['input'] + item['generated_tests']['input']
        all_outputs = item['public_tests']['output'] + item['private_tests']['output'] + item['generated_tests']['output']
        
        if not all_inputs:
            continue
            
        print(f"Found problem: {name} with {len(python_solutions)} solutions and {len(all_inputs)} tests")
        
        # Save to directory
        problem_dir = f"dataset_codecontests/{name.replace('/', '_')}"
        os.makedirs(problem_dir, exist_ok=True)
        
        with open(f"{problem_dir}/problem.txt", "w") as f:
            f.write(description)
            
        os.makedirs(f"{problem_dir}/solutions", exist_ok=True)
        for i, sol in enumerate(python_solutions[:5]):
            with open(f"{problem_dir}/solutions/sol_{i}.py", "w") as f:
                f.write(sol)
                
        os.makedirs(f"{problem_dir}/tests", exist_ok=True)
        for i, (inp, outp) in enumerate(zip(all_inputs, all_outputs)):
            with open(f"{problem_dir}/tests/test_{i}.in", "w") as f:
                f.write(inp)
            with open(f"{problem_dir}/tests/test_{i}.out", "w") as f:
                f.write(outp)
        
        count += 1
        if count >= n:
            break

if __name__ == "__main__":
    save_codecontests_subset(5)
