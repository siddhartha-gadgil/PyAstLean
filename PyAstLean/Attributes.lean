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
def pythonMethodMap? (attr : String) : Option Lean.Name :=
  match attr with
  -- String Only
  | "split"      => some ``pyStringSplit
  | "join"       => some ``pyStringJoin
  | "replace"    => some ``pyStringReplace
  | "strip"      => some ``pyStringStrip
  | "find"        => some ``pyStringFind
  | "index"      => some ``pyStringIndex
  | "startswith" => some ``pyStringStartswith
  | "endswith"   => some ``pyStringEndswith
  | "lower"      => some ``pyStringLower
  | "upper"      => some ``pyStringUpper
  -- List Only
  | "append"     => some ``pyAppend
  -- Dict Only
  | "items"      => some ``pyItems
  | "keys"       => some ``pyKeys
  | "values"     => some ``pyValues
  -- Common
  | "clear"      => some ``pyClear
  | "pop"        => some ``pyPop
  | "update"     => some ``pyUpdate
  | _            => none

/--
Backward-compatible alias used by older codegen paths.

The `?`-suffixed version is the canonical name because lookup may fail, but keeping
this alias avoids churn in generators that still call `pythonMethodMap`.
-/
def pythonMethodMap (attr : String) : Option Lean.Name :=
  pythonMethodMap? attr

end PyAstLean
