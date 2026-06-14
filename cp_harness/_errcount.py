import os, sys, glob, subprocess, tempfile, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = os.path.join(ROOT, ".venv/bin/python")
sys.path.insert(0, os.path.join(ROOT, "cp_harness"))
from convert import wrap_for_main
for src in sorted(glob.glob(os.path.join(ROOT, "cp_harness/dataset/*/solutions/sol_*.py"))):
    name = os.path.relpath(src, os.path.join(ROOT, "cp_harness/dataset"))
    try:
        wrapped = wrap_for_main(open(src).read())
    except Exception as e:
        print(f"WRAP {name}: {e}"); continue
    pyf = tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, dir="/tmp"); pyf.write(wrapped); pyf.close()
    leanf = pyf.name[:-3] + ".lean"
    conv = subprocess.run([PY, os.path.join(ROOT, "src/py2lean.py"), pyf.name, "--target", "command", "--strict"],
                          capture_output=True, text=True, cwd=ROOT)
    if conv.returncode != 0:
        print(f"CONV {name}"); continue
    open(leanf, "w").write(conv.stdout)
    comp = subprocess.run(["lake", "env", "lean", leanf], capture_output=True, text=True, cwd=ROOT)
    if comp.returncode == 0:
        continue
    out = comp.stderr + comp.stdout
    errs = [l for l in out.splitlines() if re.search(r"error", l)]
    firsts = [l.split("error")[-1].strip()[:55] for l in errs]
    print(f"[{len(errs)}err] {name}: {firsts[0] if firsts else ''}")
