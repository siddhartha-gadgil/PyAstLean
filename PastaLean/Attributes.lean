import Mathlib
import PastaLean.PyAPI

namespace PastaLean

/--
Registry mapping Python-style method names to their Lean runtime implementations.

The runtime functions themselves live under `PastaLean/PyAPI/*`; this file keeps the
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
  | "startswith" => some ``pyStringStartswith
  | "endswith"   => some ``pyStringEndswith
  | "lower"      => some ``pyStringLower
  | "upper"      => some ``pyStringUpper
  | "islower"    => some ``pyIsLower
  | "isupper"    => some ``pyIsUpper
  | "isalpha"    => some ``pyIsAlpha
  | "isdecimal"  => some ``pyIsDecimal
  | "isalphanum" => some ``pyIsAlphanum
  | "isspace"    => some ``pyIsWhitespace
  | "partition"  => some ``pyPartition
  | "capitalize" => some ``pyStringCapitalize
  -- List Only
  | "append"     => some ``pyAppend
  | "extend"     => some ``pyExtend
  | "reverse"    => some ``pyReverse
  | "copy"       => some ``pyCopy
  -- Dict Only
  | "items"      => some ``pyItems
  | "keys"       => some ``pyKeys
  | "values"     => some ``pyValues
  -- Dunder methods
  | "__len__"    => some ``pyLen
  -- Common
  | "clear"      => some ``pyClear
  | "update"     => some ``pyUpdate
  | "pop"        => some ``pyPop
  | "count"      => some ``pyCount
  | "find"        => some ``pyStringFind
  | "index"      => some ``pyIndex
  | _            => none

/--
Backward-compatible alias used by older codegen paths.

The `?`-suffixed version is the canonical name because lookup may fail, but keeping
this alias avoids churn in generators that still call `pythonMethodMap`.
-/
def pythonMethodMap (attr : String) : Option Lean.Name :=
  pythonMethodMap? attr

end PastaLean
