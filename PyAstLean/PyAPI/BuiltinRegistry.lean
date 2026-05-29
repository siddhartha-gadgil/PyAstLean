import PyAstLean.PyAPI

namespace PyAstLean

/-!
Registry for Python builtins that lower to ordinary Lean runtime names.

Special builtins such as `print`, `input`, and `reduce` still need custom call lowering
because they affect evaluation order, effects, or argument interpretation.
-/

/-- Direct builtin mapping for plain function calls that need no special syntax handling. -/
def pythonBuiltinMap? (name : String) : Option Lean.Name :=
  match name with
  | "len" => some ``pyLen
  | "sorted" => some ``pySort
  | "zip" => some ``pyZip
  | "enumerate" => some ``pyEnumerate
  | "sum" => some ``pySum
  | "min" => some ``pyMin
  | "max" => some ``pyMax
  | "bool" => some ``pyBool
  | "any" => some ``pyAny
  | _ => none

end PyAstLean
