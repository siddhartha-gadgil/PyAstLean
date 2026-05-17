"""
cp_dataset_builder.py

Builds a local dataset of Codeforces problems + accepted Python solutions,
then evaluates them on public tests and gives correctness scores.

FEATURES
--------
- Fetches Codeforces problems:
    contests [1..10]
    problems A..F

- Downloads:
    - sample tests
    - accepted Python submissions

- Stores everything in directories

- Verifies all solutions locally

- Produces correctness scores

REQUIREMENTS
------------
pip install requests beautifulsoup4 lxml
sudo apt install online-judge-tools

USAGE
-----
python3 cp_dataset_builder.py

OUTPUT STRUCTURE
----------------
dataset/
    1A/
        tests/
        solutions/
        results.json

    1B/
    1C/
    ...

SCORING
-------
score = passed_tests / total_tests

This only measures correctness on PUBLIC tests.
"""

import json
import os
import shutil
import subprocess
import time
import ast
import concurrent.futures
from pathlib import Path

import requests
from bs4 import BeautifulSoup

# ============================================================
# CONFIG
# ============================================================

CONTEST_START = 500
CONTEST_END = 510

PROBLEMS = ["A", "B", "C", "D", "E", "F"]

MAX_SOLUTIONS = 5
TIME_LIMIT = 2
MAX_THREADS = 4

ROOT = Path("dataset")

# Use a common browser user agent
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

# Standard library modules (common ones + built-ins)
STD_LIBS = {
    "sys", "os", "math", "collections", "itertools", "heapq", "bisect",
    "functools", "re", "json", "random", "time", "datetime", "array",
    "copy", "decimal", "fractions", "io", "struct", "abc", "typing",
    "operator", "string", "types", "dataclasses", "enum", "pathlib"
}

session = requests.Session()
session.headers.update({"User-Agent": USER_AGENT})

# ============================================================
# UTILS
# ============================================================

def run(cmd, cwd=None):
    res = subprocess.run(
        cmd,
        shell=True,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    return res


def normalize(s):
    return "\n".join(
        line.rstrip()
        for line in s.strip().splitlines()
    ).strip()


def ensure_dir(p):
    p.mkdir(parents=True, exist_ok=True)


def is_standard_code(code):
    try:
        tree = ast.parse(code)
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    base_module = alias.name.split('.')[0]
                    if base_module not in STD_LIBS:
                        return False
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    base_module = node.module.split('.')[0]
                    if base_module not in STD_LIBS:
                        return False
        return True
    except Exception:
        return False


# ============================================================
# TEST DOWNLOAD
# ============================================================

def download_tests(problem_url, dest):
    ensure_dir(dest)

    # Try regular samples first
    cmd = f"oj download -d . {problem_url}"
    res = run(cmd, cwd=dest)

    # Try system tests as well
    cmd_sys = f"oj download --system -d . {problem_url}"
    run(cmd_sys, cwd=dest)
    
    return res.returncode == 0


# ============================================================
# FETCH SUBMISSIONS
# ============================================================

def get_python_submissions(contest_id, problem_index):
    url = f"https://codeforces.com/api/contest.status?contestId={contest_id}&from=1&count=1000"

    try:
        r = session.get(url, timeout=20)

        if r.status_code != 200:
            return []

        data = r.json()
        if data["status"] != "OK":
            return []

        submissions = []

        for sub in data["result"]:
            if sub["problem"]["index"] != problem_index:
                continue

            language = sub.get("programmingLanguage", "")
            verdict = sub.get("verdict", "")

            if "Python" not in language:
                continue

            if verdict != "OK":
                continue

            submissions.append(sub["id"])

            if len(submissions) >= MAX_SOLUTIONS * 5: # Get more to allow filtering
                break

        return submissions

    except Exception as e:
        print(f"Error fetching submissions for {contest_id}{problem_index}: {e}")
        return []


# ============================================================
# FETCH SOURCE CODE
# ============================================================

def fetch_submission(contest_id, submission_id):
    url = (
        f"https://codeforces.com/contest/"
        f"{contest_id}/submission/{submission_id}"
    )

    try:
        r = session.get(url, timeout=20)
        
        # If we get a 403 or redirect to login, scraping failed
        if r.status_code != 200 or "log in" in r.text.lower() or "enter" in r.url:
            return None

        soup = BeautifulSoup(r.text, "lxml")
        pre = soup.find("pre", id="program-source-text")

        if pre is None:
            return None

        return pre.get_text()

    except Exception:
        return None


# ============================================================
# SAVE SOLUTIONS
# ============================================================

def save_solutions(contest_id, solution_ids, outdir):
    ensure_dir(outdir)

    saved = []

    for sid in solution_ids:
        code = fetch_submission(contest_id, sid)

        if not code:
            continue
        
        if not is_standard_code(code):
            continue

        path = outdir / f"{sid}.py"

        with open(path, "w") as f:
            f.write(code)

        saved.append(path)

        if len(saved) >= MAX_SOLUTIONS:
            break

        time.sleep(0.2)

    return saved


# ============================================================
# TEST COLLECTION
# ============================================================

def collect_tests(test_dir):
    tests = []

    if not test_dir.exists():
        return tests

    for f in sorted(os.listdir(test_dir)):
        if f.endswith(".in"):
            out = f.replace(".in", ".out")

            inp_path = test_dir / f
            out_path = test_dir / out

            if out_path.exists():
                tests.append((inp_path, out_path))

    return tests


# ============================================================
# RUN SOLUTION
# ============================================================

def run_solution(solution_path, input_file):
    with open(input_file, "r") as f:
        try:
            res = subprocess.run(
                ["python3", str(solution_path)],
                stdin=f,
                capture_output=True,
                text=True,
                timeout=TIME_LIMIT
            )

            return (
                res.stdout,
                res.stderr,
                res.returncode
            )

        except subprocess.TimeoutExpired:
            return None, "TLE", -1
        except Exception as e:
            return None, str(e), -1


# ============================================================
# VERIFY SOLUTION
# ============================================================

def verify_solution(solution_path, tests):
    passed = 0

    for inp, outp in tests:
        with open(outp, "r") as f:
            expected = normalize(f.read())

        stdout, stderr, rc = run_solution(
            solution_path,
            inp
        )

        if rc != 0:
            continue

        got = normalize(stdout)

        if got == expected:
            passed += 1

    total = len(tests)

    score = 0.0

    if total > 0:
        score = passed / total

    return {
        "passed": passed,
        "total": total,
        "score": score
    }


# ============================================================
# PROCESS ONE PROBLEM
# ============================================================

def process_problem(contest_id, problem_index):
    tag = f"{contest_id}{problem_index}"
    base = ROOT / tag
    tests_dir = base / "tests"
    sols_dir = base / "solutions"

    if base.exists():
        shutil.rmtree(base)
    
    ensure_dir(base)

    problem_url = (
        f"https://codeforces.com/contest/"
        f"{contest_id}/problem/{problem_index}"
    )

    print(f"[{tag}] Downloading tests...")
    ok = download_tests(problem_url, tests_dir)
    tests = collect_tests(tests_dir)

    if not tests:
        # Try problemset URL as fallback
        problem_url = f"https://codeforces.com/problemset/problem/{contest_id}/{problem_index}"
        ok = download_tests(problem_url, tests_dir)
        tests = collect_tests(tests_dir)

    if not tests:
        # print(f"[{tag}] Skipping: no tests.")
        shutil.rmtree(base, ignore_errors=True)
        return

    # print(f"[{tag}] Fetching submissions...")
    subs = get_python_submissions(
        contest_id,
        problem_index
    )

    if not subs:
        # print(f"[{tag}] Skipping: no submissions.")
        shutil.rmtree(base, ignore_errors=True)
        return

    # print(f"[{tag}] Downloading and filtering {len(subs)} candidate solutions...")
    paths = save_solutions(
        contest_id,
        subs,
        sols_dir
    )

    if not paths:
        # print(f"[{tag}] Skipping: no suitable solutions.")
        shutil.rmtree(base, ignore_errors=True)
        return

    results = []
    for path in paths:
        res = verify_solution(path, tests)
        results.append({
            "file": path.name,
            **res
        })

    with open(base / "results.json", "w") as f:
        json.dump(results, f, indent=2)

    print(f"[{tag}] DONE: {len(tests)} tests, {len(paths)} solutions.")


# ============================================================
# MAIN
# ============================================================

def main():
    if ROOT.exists():
        shutil.rmtree(ROOT)

    ensure_dir(ROOT)

    tasks = []
    for contest_id in range(CONTEST_START, CONTEST_END + 1):
        for problem_index in PROBLEMS:
            tasks.append((contest_id, problem_index))

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
        futures = {executor.submit(process_problem, cid, pidx): (cid, pidx) for cid, pidx in tasks}
        
        for future in concurrent.futures.as_completed(futures):
            cid, pidx = futures[future]
            try:
                future.result()
            except Exception as e:
                print(f"ERROR processing {cid}{pidx}: {e}")


if __name__ == "__main__":
    main()
