#!/usr/bin/env bash
# Integration test for cross-file imports + privacy.
#
# PALC's command-target harness wraps generated output inside `namespace PALCGenerated`,
# which turns any `import Foo` into a mid-file import that Lean rejects — so cross-file
# imports cannot be tested as a normal PALC case. This script tests them end-to-end
# instead: it converts a defining module and an importer, places the defining module where
# Lean can import it, and checks that
#   (1) the importer compiles (public names cross the import boundary), and
#   (2) a private (`_`-prefixed) name from the defining module is NOT importable.
#
# Run from the repository root:  bash PyAstLeanTest/PyAstLeanCheck/Imports/run_import_test.sh
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

DEF_PY="PyAstLeanTest/PyAstLeanCheck/Imports/mathlib_module.py"
USE_PY="PyAstLeanTest/PyAstLeanCheck/Imports/importer.py"

# The importer does `from mathlib_module import ...`, which the converter lowers to
# `import Mathlib_module`. Place the converted defining module under the PyAstLean lib so
# it is importable, and (for this test) also expose it at the bare `Mathlib_module` path
# the importer expects by building it directly.
DEF_LEAN="PyAstLean/PyGens/Mathlib_module.lean"
USE_LEAN="/tmp/pyastlean_importer_check.lean"

cleanup() {
  rm -f "$DEF_LEAN" "$USE_LEAN" "$USE_LEAN".gen
  rm -f .lake/build/lib/lean/PyAstLean/PyGens/Mathlib_module.olean \
        .lake/build/lib/lean/PyAstLean/PyGens/Mathlib_module.ilean 2>/dev/null
}
# trap cleanup EXIT

echo "[1/4] Converting defining module ($DEF_PY)..."
python3 src/py2lean.py "$DEF_PY" --target command > "$DEF_LEAN" 2>/dev/null
if ! grep -q "private def _internal_helper" "$DEF_LEAN"; then
  echo "FAIL: expected '_internal_helper' to be lowered as 'private def'"; exit 1
fi
if ! grep -q "private def __SECRET" "$DEF_LEAN"; then
  echo "FAIL: expected '__SECRET' to be lowered as 'private def'"; exit 1
fi
if grep -q "private def add" "$DEF_LEAN"; then
  echo "FAIL: public 'add' must not be private"; exit 1
fi
echo "      privacy OK: _internal_helper and __SECRET are private; add is public."

echo "[2/4] Checking importer emits 'import Mathlib_module'..."
python3 src/py2lean.py "$USE_PY" --target command 2>/dev/null > "$USE_LEAN".gen
if ! grep -q "^import Mathlib_module" "$USE_LEAN".gen; then
  echo "FAIL: importer did not emit 'import Mathlib_module'"; cat "$USE_LEAN".gen; exit 1
fi
echo "      import path OK: 'from mathlib_module import ...' -> 'import Mathlib_module'."

echo "[3/4] Building defining module so it is importable..."
if ! lake build PyAstLean.PyGens.Mathlib_module >/dev/null 2>&1; then
  echo "FAIL: defining module did not compile"; exit 1
fi

echo "[4/4] Compiling importer: public names must resolve, private must not..."
cat > "$USE_LEAN" <<'LEAN'
import PyAstLean
import PyAstLean.PyGens.Mathlib_module
open PyAstLean

-- Public names cross the import boundary.
#check @add
#check @scale
#check @PUBLIC_CONST
#check @__version__
LEAN
if ! lake env lean "$USE_LEAN" >/dev/null 2>&1; then
  echo "FAIL: public names did not import/compile"; lake env lean "$USE_LEAN" 2>&1 | head; exit 1
fi
echo "      public names import OK."

# A private name must be rejected.
cat > "$USE_LEAN" <<'LEAN'
import PyAstLean
import PyAstLean.PyGens.Mathlib_module
open PyAstLean
#check @_internal_helper
LEAN
if lake env lean "$USE_LEAN" >/dev/null 2>&1; then
  echo "FAIL: private '_internal_helper' was importable (should be private)"; exit 1
fi
echo "      private name correctly NOT importable."

echo ""
echo "PASS: cross-file imports + privacy work end-to-end."
