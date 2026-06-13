"""Ad-hoc CP compile-rate measurement. Run from cp_harness/ with venv active.
Does NOT run the slow convert.py pipeline: it wraps each solution with
convert.wrap_for_main, runs src/py2lean.py to produce Lean, then `lake env lean`.
Prints OK count and per-solution failure category.
"""
import os, sys, glob, subprocess, tempfile, json

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = os.path.join(ROOT, ".venv/bin/python")
sys.path.insert(0, os.path.join(ROOT, "cp_harness"))
from convert import wrap_for_main

sols = sorted(glob.glob(os.path.join(ROOT, "cp_harness/dataset/*/solutions/sol_*.py")))
ok = 0
results = []
for src in sols:
    name = os.path.relpath(src, os.path.join(ROOT, "cp_harness/dataset"))
    try:
        wrapped = wrap_for_main(open(src).read())
    except Exception as e:
        results.append((name, "WRAP_FAIL", str(e)[:120])); continue
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, dir="/tmp") as f:
        f.write(wrapped); pyf = f.name
    leanf = pyf[:-3] + ".lean"
    conv = subprocess.run([PY, os.path.join(ROOT, "src/py2lean.py"), pyf,
                           "--target", "command", "--strict"], capture_output=True, text=True, cwd=ROOT)
    if conv.returncode != 0:
        results.append((name, "CONV_FAIL", conv.stderr.strip().splitlines()[-1][:140] if conv.stderr.strip() else "")); continue
    open(leanf, "w").write(conv.stdout)
    comp = subprocess.run(["lake", "env", "lean", leanf], capture_output=True, text=True, cwd=ROOT)
    if comp.returncode == 0:
        ok += 1; results.append((name, "OK", ""))
    else:
        errln = ""
        for ln in comp.stderr.splitlines() + comp.stdout.splitlines():
            if "error:" in ln:
                errln = ln.strip(); break
        results.append((name, "COMPILE_FAIL", errln[:160]))

print(f"\n=== OK: {ok} / {len(sols)} ===\n")
for n, cat, msg in results:
    if cat != "OK":
        print(f"[{cat}] {n}: {msg}")
