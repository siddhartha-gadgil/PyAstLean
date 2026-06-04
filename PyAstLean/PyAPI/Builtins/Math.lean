import Mathlib

namespace PyAstLean

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

end PyAstLean
