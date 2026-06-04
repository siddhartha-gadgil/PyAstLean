import Mathlib
import PyAstLean.PyAPI.CommonProtocols.Iterable
import PyAstLean.PyAPI.PyPrint

namespace PyAstLean

/--
Typeclass for Python-style `int(...)` coercions used by translated code.

This intentionally keeps the current CP-oriented behavior forgiving: invalid strings
become `0` instead of raising, so `int(input())` stays simple in the current subset.
-/
class PyIntCast (α : Type) where
  pyInt : α → Int

/-- Dispatch Python-style integer coercions. -/
def pyInt {α : Type} [PyIntCast α] (x : α) : Int :=
  PyIntCast.pyInt x

instance : PyIntCast Int where
  pyInt x := x

instance : PyIntCast Nat where
  pyInt x := x

instance : PyIntCast Bool where
  pyInt
    | true => 1
    | false => 0

instance : PyIntCast String where
  pyInt s := s.trimAscii.toString.toInt? |>.getD 0

/-- Python `int(x)` on a float truncates toward zero (e.g. `int(n ** 0.5)`). -/
instance : PyIntCast Float where
  pyInt x := if x ≥ 0 then (x.toUInt64.toNat : Int) else -((-x).toUInt64.toNat : Int)

/--
Python-style `str(...)` coercion.

This reuses the printing runtime so values render with the same Python-like surface as
they would inside `print(...)`.
-/
def pyStr {α : Type} [PyPrintable α] (x : α) : String :=
  pyStringify x

/--
Python-style eager `list(...)` coercion.

This currently follows the iterable protocol, so strings become character lists,
lists stay lists, and dictionaries become their key lists.
-/
def pyList {α β : Type} [PyIterable α β] (x : α) : List β :=
  pyIter x

/-- Convert an `Int` to a `Float` (no `Float.ofInt` in core; build from the magnitude). -/
private def floatOfInt (x : Int) : Float :=
  if x ≥ 0 then Float.ofNat x.toNat else - Float.ofNat (-x).toNat

/--
Typeclass for Python-style `float(...)` coercions.

Numeric inputs convert directly. Strings recognise the `inf`/`-inf`/`nan` sentinels
(common in competitive programming as comparison bounds); other strings currently fall back
to `0.0` since the runtime has no general float parser yet.
-/
class PyFloatCast (α : Type) where
  pyFloat : α → Float

/-- Dispatch Python-style float coercions. -/
def pyFloat {α : Type} [PyFloatCast α] (x : α) : Float :=
  PyFloatCast.pyFloat x

instance : PyFloatCast Float where pyFloat x := x
instance : PyFloatCast Int where pyFloat x := floatOfInt x
instance : PyFloatCast Nat where pyFloat x := Float.ofNat x
instance : PyFloatCast Bool where
  pyFloat | true => 1.0 | false => 0.0
instance : PyFloatCast String where
  pyFloat s :=
    let t := s.trimAscii.toString
    if t == "inf" || t == "+inf" || t == "Infinity" then (1.0 : Float) / 0.0
    else if t == "-inf" || t == "-Infinity" then (-1.0 : Float) / 0.0
    else if t == "nan" then (0.0 : Float) / 0.0
    else 0.0

end PyAstLean
