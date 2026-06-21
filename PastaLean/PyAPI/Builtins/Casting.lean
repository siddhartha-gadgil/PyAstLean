import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.PyPrint

namespace PastaLean

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

/-- `int(x)` on an exact-mode real number (a transcendental result). `ℝ` is noncomputable, so this
is `noncomputable` and only lets the program elaborate — regenerate with `--approx` to evaluate.
Uses the floor `⌊x⌋`. -/
noncomputable instance : PyIntCast ℝ where
  pyInt x := ⌊x⌋

/-- `int(q)` on an exact-mode rational truncates toward the floor (`⌊q⌋`), computable. -/
instance : PyIntCast Rat where
  pyInt q := ⌊q⌋

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
/-- `10.0 ^ n` built by repeated multiplication (avoids `Nat` overflow for the exponent). -/
private def tenPowNat : Nat → Float
  | 0 => 1.0
  | n + 1 => 10.0 * tenPowNat n

/--
Parse a Python-style decimal float literal: optional sign, integer and/or fractional part,
and an optional `e`/`E` exponent (e.g. `"2.75"`, `"-.5"`, `"1.5e-3"`). Anything unparseable
in a part contributes `0`, matching the forgiving `int(...)` cast above.
-/
private def parseFloatString (s : String) : Float :=
  let t := s.trimAscii.toString
  if t == "inf" || t == "+inf" || t == "Infinity" then (1.0 : Float) / 0.0
  else if t == "-inf" || t == "-Infinity" then (-1.0 : Float) / 0.0
  else if t == "nan" then (0.0 : Float) / 0.0
  else
    let (neg, body) :=
      if t.startsWith "-" then (true, (t.drop 1).toString)
      else if t.startsWith "+" then (false, (t.drop 1).toString)
      else (false, t)
    -- normalise the exponent marker so the split below catches both `e` and `E`
    let lower := body.map (fun c => if c == 'E' then 'e' else c)
    let (mant, exp) :=
      match lower.splitOn "e" with
      | [m] => (m, (0 : Int))
      | [m, e] => (m, e.toInt?.getD 0)
      | _ => (lower, 0)
    let (ip, fp) :=
      match mant.splitOn "." with
      | [i] => (i, "")
      | [i, f] => (i, f)
      | _ => (mant, "")
    let intVal : Nat := ip.toNat?.getD 0
    let fracVal : Nat := fp.toNat?.getD 0
    let base := Float.ofNat intVal + Float.ofNat fracVal / tenPowNat fp.length
    let scale := if exp ≥ 0 then tenPowNat exp.toNat else 1.0 / tenPowNat (-exp).toNat
    let v := base * scale
    if neg then -v else v

instance : PyFloatCast String where
  pyFloat s := parseFloatString s

/-! ## Exact-mode `float(...)` → `ℚ`

In the default (exact) numeric mode `float(x)` lowers to `pyRat`, producing an exact rational.
Notably a decimal string parses *exactly* (`float("0.1") = 1/10`), and `int`/`bool`/`Rat` inputs
coerce losslessly. `inf`/`nan` have no `ℚ` value, so the string parser degrades them to `0`
(exact mode does not model them — use `--approx` for `float('inf')`). -/

/-- Typeclass for exact-mode `float(...)` coercions producing `ℚ`. -/
class PyRatCast (α : Type) where
  pyRat : α → Rat

/-- Dispatch exact-mode float coercions to `ℚ`. -/
def pyRat {α : Type} [PyRatCast α] (x : α) : Rat :=
  PyRatCast.pyRat x

instance : PyRatCast Rat where pyRat x := x
instance : PyRatCast Int where pyRat x := (x : Rat)
instance : PyRatCast Nat where pyRat x := (x : Rat)
instance : PyRatCast Bool where
  pyRat | true => 1 | false => 0

/-- `10 ^ n` as a `ℚ` via repeated multiplication. -/
private def tenPowNatRat : Nat → Rat
  | 0 => 1
  | n + 1 => 10 * tenPowNatRat n

/-- Parse a Python-style decimal float literal into an *exact* `ℚ` (sign, integer/fractional
parts, optional `e`/`E` exponent). `inf`/`nan` are not representable in `ℚ` and degrade to `0`. -/
private def parseRatString (s : String) : Rat :=
  let t := s.trimAscii.toString
  if t == "inf" || t == "+inf" || t == "Infinity" || t == "-inf" || t == "-Infinity" || t == "nan" then 0
  else
    let (neg, body) :=
      if t.startsWith "-" then (true, (t.drop 1).toString)
      else if t.startsWith "+" then (false, (t.drop 1).toString)
      else (false, t)
    let lower := body.map (fun c => if c == 'E' then 'e' else c)
    let (mant, exp) :=
      match lower.splitOn "e" with
      | [m] => (m, (0 : Int))
      | [m, e] => (m, e.toInt?.getD 0)
      | _ => (lower, 0)
    let (ip, fp) :=
      match mant.splitOn "." with
      | [i] => (i, "")
      | [i, f] => (i, f)
      | _ => (mant, "")
    let intVal : Nat := ip.toNat?.getD 0
    let fracVal : Nat := fp.toNat?.getD 0
    let base : Rat := (intVal : Rat) + (fracVal : Rat) / tenPowNatRat fp.length
    let scale : Rat := if exp ≥ 0 then tenPowNatRat exp.toNat else 1 / tenPowNatRat (-exp).toNat
    let v := base * scale
    if neg then -v else v

instance : PyRatCast String where pyRat s := parseRatString s

end PastaLean
