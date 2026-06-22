#!/usr/bin/env python3
"""Convert + compile-check every example/test Python program in one pass.

Groups and what happens to each:
  - showcase  (example_scripts/showcase)              -> .lean written IN PLACE next to the .py
  - Random    (PastaLeanTest/Random)                  -> .lean written IN PLACE next to the .py
  - General   (PastaLeanTest/PastaLeanCheck/General)  -> compile-checked only (temp file, no write)

For each .py: run the transpiler (`src/py2lean.py --target command --mode both`), then type-check
the generated Lean with `lake env lean`. Prints OK / CONVERT_FAIL / COMPILE_FAIL per file and a
summary; exits non-zero if anything failed.

Usage:  python3 regen_examples.py [--group showcase|Random|General] [--jobs N] [--timeout SECS]
"""
from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parent
VENV_PY = REPO / ".venv/bin/python3"
PY2LEAN = REPO / "src/py2lean.py"

# (label, directory, write-in-place?)
GROUPS: list[tuple[str, Path, bool]] = [
    ("showcase", REPO / "example_scripts/showcase", True),
    ("Random", REPO / "PastaLeanTest/Random", True),
    ("General", REPO / "PastaLeanTest/PastaLeanCheck/General", False),
]

# Helper scripts that are NOT transpiler inputs (they drive/figure showcases, not programs to port).
SKIP_NAMES: set[str] = {"run_showcase.py", "fetch_data.py"}


def python_bin() -> str:
    return str(VENV_PY) if VENV_PY.exists() else sys.executable


def find_pys(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.py") if p.name not in SKIP_NAMES)


def first_error_line(text: str) -> str:
    for line in text.splitlines():
        if "error" in line.lower():
            return line.strip()
    return (text.strip().splitlines() or ["(no detail)"])[0]


def convert(py: Path) -> tuple[str | None, str | None]:
    """Transpile `py` to Lean text (both prove + run twins). Returns (lean, None) or (None, err)."""
    r = subprocess.run(
        [python_bin(), str(PY2LEAN), str(py), "--target", "command", "--mode", "both"],
        capture_output=True, text=True, cwd=REPO,
    )
    if r.returncode != 0 or not r.stdout.strip():
        return None, first_error_line(r.stderr or r.stdout or "convert failed")
    return r.stdout, None


def compile_lean(path: Path, timeout: int) -> str | None:
    """Type-check a Lean file; return None on success, else the first error line."""
    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(path)],
            capture_output=True, text=True, cwd=REPO, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return f"timed out after {timeout}s"
    if r.returncode != 0:
        return first_error_line(r.stdout + "\n" + r.stderr)
    return None


def process(py: Path, in_place: bool, timeout: int) -> tuple[str, Path, str]:
    """Returns (status, py, detail). status in {OK, CONVERT_FAIL, COMPILE_FAIL}."""
    lean, cerr = convert(py)
    if cerr:
        return "CONVERT_FAIL", py, cerr
    if in_place:
        out = py.with_suffix(".lean")
        out.write_text(lean)
        err = compile_lean(out, timeout)
    else:
        tmp = Path(tempfile.mkstemp(suffix=".lean", dir=REPO)[1])
        try:
            tmp.write_text(lean)
            err = compile_lean(tmp, timeout)
        finally:
            tmp.unlink(missing_ok=True)
    return ("COMPILE_FAIL" if err else "OK"), py, (err or "")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--group", choices=[g[0] for g in GROUPS], help="only this group")
    ap.add_argument("--jobs", type=int, default=4, help="parallel compile workers (default 4)")
    ap.add_argument("--timeout", type=int, default=240, help="per-file compile timeout secs (default 240)")
    args = ap.parse_args()

    groups = [g for g in GROUPS if args.group is None or g[0] == args.group]
    ok = fails = 0
    for label, root, in_place in groups:
        if not root.exists():
            print(f"\n## {label}: directory not found ({root.relative_to(REPO)})")
            continue
        pys = find_pys(root)
        print(f"\n## {label}  ({root.relative_to(REPO)})  "
              f"{'-> writing .lean in place' if in_place else '-> compile-check only'}  [{len(pys)} files]")
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
            results = list(ex.map(lambda p: process(p, in_place, args.timeout), pys))
        for status, py, detail in sorted(results, key=lambda r: str(r[1])):
            rel = py.relative_to(REPO)
            if status == "OK":
                ok += 1
                tail = f"  ->  {py.with_suffix('.lean').relative_to(REPO)}" if in_place else ""
                print(f"  OK            {rel}{tail}")
            else:
                fails += 1
                print(f"  {status:<13} {rel}: {detail}")

    print(f"\n=== {ok} OK, {fails} FAILED ===")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
