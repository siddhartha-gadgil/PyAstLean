import Mathlib

namespace PyAstLean

class PyHAdd (α β : Type) (γ : outParam Type) where
  hAdd : α → β → γ

infix:65 " +ₚ " => PyHAdd.hAdd

@[default_instance]
instance {α β γ} [HAdd α β γ] : PyHAdd α β γ where
  hAdd := HAdd.hAdd

@[default_instance]
instance (priority := high) : PyHAdd Rat Rat Rat where
  hAdd := fun a b => (a : Rat) + (b : Rat)

instance : PyHAdd String String String where
  hAdd := String.append

/-- String building by appending a single character, e.g. `s + word[i]`. -/
instance : PyHAdd String Char String where
  hAdd := fun s c => s ++ c.toString

/-! Mixed numeric `+`. Lean has no heterogeneous `HAdd Nat Int` / `HAdd Rat Int`, so the
generic `[HAdd α β γ]` instance does not cover these mixed-type sums that arise when one
operand came from integer division (`Rat`) or a length/count (`Nat`). The result widens to
the more general type. -/
instance (priority := high) : PyHAdd Rat Int Rat where
  hAdd := fun a b => a + (b : Rat)

instance (priority := high) : PyHAdd Int Rat Rat where
  hAdd := fun a b => (a : Rat) + b

instance (priority := high) : PyHAdd Nat Int Int where
  hAdd := fun a b => (a : Int) + b

instance (priority := high) : PyHAdd Int Nat Int where
  hAdd := fun a b => a + (b : Int)

class PyHSub (α β : Type) (γ : outParam Type) where
  hSub : α → β → γ

infix:65 " -ₚ " => PyHSub.hSub

@[default_instance]
instance (priority := low) {α β γ} [HSub α β γ] : PyHSub α β γ where
  hSub := HSub.hSub

instance (priority := high) : PyHSub Nat Nat Int where
  hSub := fun a b => (a : Int) - (b : Int)

@[default_instance]
instance (priority := high) : PyHSub Rat Int Rat where
  hSub := fun a b => (a : Rat) - (b : Int)

class PyHMul (α β : Type) (γ : outParam Type) where
  hMul : α → β → γ

infix:70 " *ₚ " => PyHMul.hMul

@[default_instance]
instance {α β γ} [HMul α β γ] : PyHMul α β γ where
  hMul := HMul.hMul

instance : PyHMul String Nat String where
  hMul := fun s n => String.intercalate "" (List.replicate n s)

instance : PyHMul String Int String where
  hMul := fun s n =>
    if n < 0 then
      ""
    else
      String.intercalate "" (List.replicate n.toNat s)

/-- Python list repetition `xs * n` (and the symmetric `n * xs`): repeats the list `n` times,
matching `[0] * n` style array initialization. A non-positive count yields `[]`. -/
instance {α : Type} : PyHMul (List α) Int (List α) where
  hMul := fun xs n => if n ≤ 0 then [] else (List.replicate n.toNat xs).flatten

instance {α : Type} : PyHMul Int (List α) (List α) where
  hMul := fun n xs => if n ≤ 0 then [] else (List.replicate n.toNat xs).flatten

@[default_instance]
instance (priority := high) : PyHMul Rat Rat Rat where
  hMul := fun a b => (a : Rat) * (b : Rat)

class PyHPow (α β : Type) (γ : outParam Type) where
  hPow : α → β → γ

infix:80 " ^ₚ " => PyHPow.hPow

class PyModulo (α β : Type) (γ : outParam Type) where
  hMod : α → β → γ

infix:70 " %ₚ " => PyModulo.hMod

def pyMod (a b : Int) : Int :=
  if b == 0 then
    a
  else
    let r := a % b
    if (r < 0 && b > 0) || (r > 0 && b < 0) then
      r + b
    else
      r

@[default_instance]
instance (priority := high) : PyModulo Int Int Int where
  hMod := pyMod

instance : PyModulo Nat Nat Nat where
  hMod := fun a b => a % b

@[default_instance]
instance {α β γ} [HPow α β γ] : PyHPow α β γ where
  hPow := HPow.hPow

@[default_instance]
instance (priority := high) {α β} [Pow α β] : PyHPow α β α where
  hPow := Pow.pow

@[default_instance]
instance (priority := high) : PyHPow Rat Int Rat where
  hPow := fun a b => (a : Rat) ^ (b : Int)

/-- Python `a ** b` on integers, e.g. `2 ** n`. Lean has no `HPow Int Int Int` (a negative
exponent would be a rational), so we raise to `b.toNat`; this matches competitive-programming
use, where exponents are non-negative. -/
@[default_instance]
instance (priority := high) : PyHPow Int Int Int where
  hPow := fun a b => a ^ b.toNat

instance : PyHPow Nat Nat Nat where
  hPow := fun a b => a ^ b

/-- Python `a ** b` with a float exponent (e.g. `n ** 0.5` for a square root) yields a float.
The base is widened to `Float`; the common idiom is `int(n ** 0.5)`. -/
instance (priority := high) : PyHPow Int Float Float where
  hPow := fun a b => Float.pow (Float.ofInt a) b

instance (priority := high) : PyHPow Float Float Float where
  hPow := fun a b => Float.pow a b

@[default_instance]
instance (priority := high) : Neg Rat where
  neg := fun a => - (a : Rat)

class PyHDiv (α β : Type) (γ : outParam Type) where
  hDiv : α → β → γ

infix:70 " /ₚ " => PyHDiv.hDiv

@[default_instance]
instance {α β γ} [HDiv α β γ] : PyHDiv α β γ where
  hDiv := HDiv.hDiv

instance (priority := high) : PyHDiv Int Int Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

instance (priority := high) : PyHDiv Nat Nat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

@[default_instance]
instance (priority := high) : PyHDiv Rat Rat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)


/-- Python-style floor division: `a // b` truncates toward negative infinity. -/
def pyFloorDiv (a b : Int) : Int :=
  if b == 0 then
    panic! "ZeroDivisionError: integer division or modulo by zero"
  else
    Int.fdiv a b

/-!
Python-style integer bitwise operators.

These assume non-negative operands, which covers competitive-programming use. Python's
infinite two's-complement semantics for negative integers is intentionally out of scope:
operands are taken through `Int.toNat`, so a negative operand is treated as `0`.
-/

/-- Python `a & b`. -/
def pyBitAnd (a b : Int) : Int := Int.ofNat (Nat.land a.toNat b.toNat)

/-- Python `a | b`. -/
def pyBitOr (a b : Int) : Int := Int.ofNat (Nat.lor a.toNat b.toNat)

/-- Python `a ^ b` (bitwise xor). -/
def pyBitXor (a b : Int) : Int := Int.ofNat (Nat.xor a.toNat b.toNat)

/-- Python `a << b`. -/
def pyShiftLeft (a b : Int) : Int := a * (2 ^ b.toNat)

/-- Python `a >> b` (floor division by `2 ^ b`). -/
def pyShiftRight (a b : Int) : Int := Int.fdiv a (2 ^ b.toNat)

end PyAstLean
