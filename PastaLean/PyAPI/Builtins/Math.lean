import Mathlib

namespace PastaLean

/-!
Python's builtin `pow`.

`pow(b, e)` is the same as `b ** e`; `pow(b, e, m)` is *modular* exponentiation,
`(b ** e) % m`, computed with fast (square-and-multiply) exponentiation so that the
competitive-programming idiom `pow(k, p, 1000000007)` with a huge exponent stays cheap
instead of materializing the astronomically large `b ** e` first.
-/

/-- Square-and-multiply helper: `(b ^ e * acc) % m`, halving `e` each step. -/
private partial def pyPowModGo (m b e acc : Nat) : Nat :=
  if e == 0 then acc
  else
    let acc := if e % 2 == 1 then (acc * b) % m else acc
    pyPowModGo m ((b * b) % m) (e / 2) acc

/-- Fast modular exponentiation over the naturals: `(base ^ exp) % m` (with `m = 0` meaning
"no modulus", i.e. plain `base ^ exp`). -/
def pyPowModNat (base exp m : Nat) : Nat :=
  if m == 0 then base ^ exp
  else pyPowModGo m (base % m) exp (1 % m)

/-- Python `pow(base, exp, m)` modular exponentiation on integers, normalizing the result into
`[0, m)` like Python. A zero modulus falls back to plain `base ^ exp` (the 2-arg form passes
`m = 0`). Negative exponents are not supported (Python would return a float / modular inverse);
they are clamped via `toNat`, matching competitive-programming use. -/
def pyPow (base exp : Int) (m : Int := 0) : Int :=
  if m == 0 then
    base ^ exp.toNat
  else
    let mn := m.natAbs
    -- reduce the base into [0, m) first so `toNat` is faithful for negative bases
    let b := ((base % m) + m) % m
    (pyPowModNat b.toNat exp.toNat mn : Int)

/-! ### `abs` -/

/-- Python's builtin `abs`, kept polymorphic over the numeric types via a small protocol so the
result type matches the argument (`abs(-3) : Int`, `abs(-2.5) : Float`). -/
class PyAbs (α : Type) where
  pyAbs : α → α

/-- Dispatch Python `abs` through the `PyAbs` protocol. -/
def pyAbs {α : Type} [PyAbs α] (x : α) : α := PyAbs.pyAbs x

instance : PyAbs Int where pyAbs x := if x < 0 then -x else x
instance : PyAbs Nat where pyAbs x := x
instance : PyAbs Float where pyAbs x := if x < 0.0 then -x else x
instance : PyAbs Rat where pyAbs x := if x < 0 then -x else x

/-! ### `divmod` -/

/-- Python `divmod(a, b) = (a // b, a % b)` with floor-division semantics (the remainder takes
the sign of the divisor), so that `b * q + r = a` always holds. -/
def pyDivmod (a b : Int) : Int × Int :=
  let q := if (a % b == 0) || ((a < 0) == (b < 0)) then a / b else a / b - 1
  (q, a - b * q)

/-! ### `round` -/

/-- Convert an integral `Float` to an `Int` (truncating toward zero, faithful for both signs). -/
private def floatIntegralToInt (f : Float) : Int :=
  if f ≥ 0.0 then Int.ofNat f.toUInt64.toNat
  else -(Int.ofNat (-f).toUInt64.toNat)

/-- Round a `Float` to the nearest integer using round-half-to-even ("banker's rounding"),
matching Python's `round(x)` (which returns an `int`). -/
def pyRound (x : Float) : Int :=
  let fl := x.floor
  let flI := floatIntegralToInt fl
  let diff := x - fl  -- in [0, 1)
  if diff < 0.5 then flI
  else if diff > 0.5 then flI + 1
  else if flI % 2 == 0 then flI else flI + 1  -- exactly .5 → round to even

/-- Python `round(x, ndigits)`: round to `ndigits` decimal places, returning a `Float`. -/
def pyRoundDigits (x : Float) (ndigits : Int) : Float :=
  let p : Float := (10.0 : Float) ^ (Float.ofInt ndigits)
  let scaled := x * p
  -- round-half-to-even on the scaled value, then unscale
  (Float.ofInt (pyRound scaled)) / p

end PastaLean
