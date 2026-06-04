import PyAstLean.PyAPI

namespace PyAstLean

/-!
Registry for Python builtins that lower to ordinary Lean runtime names.

Special builtins such as `print` and `input` still need custom call lowering
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
  | "reversed" => some ``pyReversed
  | "chr" => some ``pyChr
  | "ord" => some ``pyOrd
  -- `pow(b, e)` ≡ `b ** e`; `pow(b, e, m)` is modular exponentiation. `pyPow`'s modulus
  -- argument defaults to `0` ("no modulus"), so both arities lower to the same name.
  | "pow" => some ``pyPow
  | "set" => some ``pySet
  -- `int`/`str` have dedicated special-case lowering for *direct* calls (`int(x)`); the
  -- registry entries make them usable as first-class callables, e.g. `map(int, xs)`.
  | "int" => some ``pyInt
  | "str" => some ``pyStr
  | "float" => some ``pyFloat
  -- We have no real tuple-from-iterable runtime; `tuple(xs)` is treated as a list, which is
  -- adequate for the membership/comparison/iteration uses that appear in this subset.
  | "tuple" => some ``pyList
  -- `map`/`filter`/`list` also have dedicated special-case lowering for direct calls (which
  -- wins, being matched first). The registry entries are the fallback used when the call is
  -- IO-effectful and routed through `inlineIOTerm`, e.g. `map(int, input().split())`.
  | "map" => some ``pyMap
  | "filter" => some ``pyFilter
  | "list" => some ``pyList
  | _ => none

end PyAstLean
