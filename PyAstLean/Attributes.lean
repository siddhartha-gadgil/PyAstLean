import Mathlib
import PyAstLean.PyAPI

namespace PyAstLean

/--
Registry mapping Python-style method names to their Lean runtime implementations.

The runtime functions themselves live under `PyAstLean/PyAPI/*`; this file keeps the
codegen-facing dispatch table in one place.

Only Python methods belong here. Builtins and operators that lower to CommonProtocols
functions like `pyLen` or `pyContains` should be wired through builtin/operator
lowering instead of this table.
-/
def pythonMethodMap (attr : String) : Option Lean.Name :=
  match attr with
  | "split"      => some ``pySplit
  | "join"       => some ``pyJoin
  | "replace"    => some ``pyReplace
  | "strip"      => some ``pyStrip
  | "find"       => some ``pyFind
  | "index"      => some ``pyIndex
  | "startswith" => some ``pyStartswith
  | "endswith"   => some ``pyEndswith
  | "lower"      => some ``pyLower
  | "upper"      => some ``pyUpper
  | "append"     => some ``pyAppend
  | "items"      => some ``pyItems
  | "keys"       => some ``pyKeys
  | "values"     => some ``pyValues
  | "clear"      => some ``pyClear
  | "pop"        => some ``pyPop
  | "update"     => some ``pyUpdate
  | _            => none

end PyAstLean
