#!/usr/bin/env python3
"""Convert fetched CP Python solutions to Lean and compile-check them.

For each `<problem>/solutions/sol_<i>.py` we:
  1. Wrap bare top-level code under `if __name__ == "__main__":` if it has no `main`
     entry point already, so py2lean emits a runnable `def main : IO Unit`.
  2. Translate to Lean with `src/py2lean.py --target command`.
  3. Compile-check the generated Lean (it must elaborate before we can run it).

Results are written next to each solution:
  <problem>/lean/sol_<i>.lean        the generated Lean (only if conversion succeeded)
  <problem>/lean/sol_<i>.status      one of: ok | convert_fail | compile_fail
  <problem>/lean/sol_<i>.log         stderr from the failing stage (for diagnosis)

A `convert_summary.json` at the dataset root tallies the three buckets so conversion
coverage is visible at a glance.

Usage:
    python3 cp_harness/convert.py --dataset cp_harness/dataset
"""

import argparse
import ast
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PY2LEAN = REPO_ROOT / "src" / "py2lean.py"


def has_main_entry(source):
    """True if the solution already defines `main`/uses a `__main__` guard, so we should
    not double-wrap it."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "main":
            return True
        if isinstance(node, ast.If):
            # crude `if __name__ == "__main__":` detection
            test = node.test
            if (
                isinstance(test, ast.Compare)
                and isinstance(test.left, ast.Name)
                and test.left.id == "__name__"
            ):
                return True
    return False


def split_imports_and_body(source):
    """Separate leading top-level imports from the rest, so wrapping keeps imports at
    module scope (Python requires `import` at top level, and Lean wants them too)."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None, None
    import_lines = set()
    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for lineno in range(node.lineno, (node.end_lineno or node.lineno) + 1):
                import_lines.add(lineno)
    lines = source.splitlines()
    imports = []
    body = []
    for i, line in enumerate(lines, start=1):
        (imports if i in import_lines else body).append(line)
    return "\n".join(imports), "\n".join(body)


def wrap_for_main(source):
    """Wrap bare top-level code under an `if __name__ == "__main__":` guard so py2lean
    produces a runnable `def main`. Imports stay at module scope. No-op if the solution
    already has a `main` entry point."""
    if has_main_entry(source):
        return source
    imports, body = split_imports_and_body(source)
    if body is None:
        return source
    indented = "\n".join(("    " + ln) if ln.strip() else ln for ln in body.splitlines())
    parts = []
    if imports.strip():
        parts.append(imports)
    parts.append('if __name__ == "__main__":')
    parts.append(indented)
    return "\n".join(parts) + "\n"


def translate(py_path):
    """Run py2lean on a file; return (ok, lean_code_or_error)."""
    proc = subprocess.run(
        ["python3", str(PY2LEAN), str(py_path), "--target", "command", "--strict"],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        return False, proc.stderr or proc.stdout or "empty output"
    return True, proc.stdout


def compile_check(lean_path):
    """Elaborate the generated Lean file; return (ok, error)."""
    proc = subprocess.run(
        ["lake", "env", "lean", str(lean_path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return False, proc.stderr or proc.stdout
    return True, ""


def summarize_error(status, log_text):
    """Extract a concise one-line reason from a failing stage's output.

    - convert_fail: the py2lean traceback ends in `NotImplementedError: ...` (or another
      exception); we surface that final line.
    - compile_fail: the Lean output's first `error:` line (often `Unknown identifier ...`
      or an unsupported-operator message) is the most actionable.
    Falls back to the last non-empty line so nothing is ever silently dropped.
    """
    lines = [ln.rstrip() for ln in (log_text or "").splitlines() if ln.strip()]
    if not lines:
        return "(no error output)"

    if status == "convert_fail":
        # The translator surfaces its own message as "Error generating code: ..." or, for
        # the AST front-end, a Python traceback whose final line is the exception.
        for ln in reversed(lines):
            if "Error generating code:" in ln:
                return ln.split("Error generating code:", 1)[1].strip()
        # Final traceback line, e.g. "NotImplementedError: Translation for Starred ..."
        return lines[-1].strip()

    # compile_fail: first Lean diagnostic that mentions an error.
    for ln in lines:
        low = ln.lower()
        if "error" in low and ":" in ln:
            # Keep the part after the "...:NN:CC: error(...):" prefix when present.
            marker = "error"
            idx = low.find(marker)
            tail = ln[idx:]
            # Drop a leading "error(kind):" or "error:" label for readability.
            for sep in ("): ", "error: "):
                if sep in tail:
                    return tail.split(sep, 1)[1].strip()
            return tail.strip()
    return lines[0].strip()


def convert_solution(sol_path, lean_dir, tmp_dir):
    name = sol_path.stem
    source = sol_path.read_text()
    wrapped = wrap_for_main(source)

    wrapped_path = tmp_dir / f"{name}_wrapped.py"
    wrapped_path.write_text(wrapped)

    ok, result = translate(wrapped_path)
    status_path = lean_dir / f"{name}.status"
    log_path = lean_dir / f"{name}.log"
    if not ok:
        status_path.write_text("convert_fail")
        log_path.write_text(result)
        return "convert_fail", summarize_error("convert_fail", result)

    lean_path = lean_dir / f"{name}.lean"
    lean_path.write_text(result)

    ok, err = compile_check(lean_path)
    if not ok:
        status_path.write_text("compile_fail")
        log_path.write_text(err)
        return "compile_fail", summarize_error("compile_fail", err)

    status_path.write_text("ok")
    if log_path.exists():
        log_path.unlink()
    return "ok", None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", default="cp_harness/dataset", help="Dataset directory")
    args = parser.parse_args()

    dataset = Path(args.dataset)
    if not dataset.is_dir():
        print(f"ERROR: dataset dir not found: {dataset}", file=sys.stderr)
        return 1

    tmp_dir = dataset / ".tmp"
    tmp_dir.mkdir(exist_ok=True)

    problems = {}
    totals = {"ok": 0, "convert_fail": 0, "compile_fail": 0}
    error_histogram = {}  # concise error reason -> count

    for prob_dir in sorted(p for p in dataset.iterdir() if p.is_dir() and not p.name.startswith(".")):
        sols_dir = prob_dir / "solutions"
        if not sols_dir.is_dir():
            continue
        lean_dir = prob_dir / "lean"
        lean_dir.mkdir(exist_ok=True)

        prob_results = {}
        for sol_path in sorted(sols_dir.glob("sol_*.py")):
            status, error = convert_solution(sol_path, lean_dir, tmp_dir)
            prob_results[sol_path.name] = {"status": status}
            if error is not None:
                prob_results[sol_path.name]["error"] = error
                error_histogram[error] = error_histogram.get(error, 0) + 1
            totals[status] += 1
            suffix = f"  -- {error}" if error else ""
            print(f"[{status:>12}] {prob_dir.name}/{sol_path.name}{suffix}")
        problems[prob_dir.name] = prob_results

    # Sort the histogram so the most common failures lead.
    top_errors = dict(sorted(error_histogram.items(), key=lambda kv: kv[1], reverse=True))
    summary = {
        "totals": totals,
        "errors_by_frequency": top_errors,
        "problems": problems,
    }
    (dataset / "convert_summary.json").write_text(json.dumps(summary, indent=2))

    print(
        f"\n[*] Conversion: {totals['ok']} ok, "
        f"{totals['compile_fail']} compile_fail, {totals['convert_fail']} convert_fail"
    )
    if top_errors:
        print("[*] Most common failures:")
        for reason, count in list(top_errors.items())[:10]:
            print(f"      {count:>3}x  {reason}")
    print(f"[*] Summary written to {dataset / 'convert_summary.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
