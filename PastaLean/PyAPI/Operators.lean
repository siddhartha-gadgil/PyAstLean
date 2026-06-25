import Mathlib
import PastaLean.PyAPI.TasteIngr

namespace PastaLean

class PyHAdd (α β : Type) (γ : outParam Type) where
  hAdd : α → β → γ

infixl:65 " +ₚ " => PyHAdd.hAdd

@[default_instance]
instance {α β γ} [HAdd α β γ] : PyHAdd α β γ where
  hAdd := HAdd.hAdd

@[default_instance]
instance (priority := high) : PyHAdd Rat Rat Rat where
  hAdd := fun a b => (a : Rat) + (b : Rat)

-- Keep `Int + Int = Int` (Python semantics) even when the operands are still metavariables at
-- elaboration (e.g. `[x + y for x in xs for y in ys]` over `List Int`). Without this, the
-- `Rat` defaulting above coerces both operands to `ℚ`, which then forces the iterable's element
-- type to `ℚ` and fails (the rat-default-instance hazard). A higher *defaulting* priority on the
-- concrete `Int` instance wins the tie. Mirrors the existing `Int`-preserving behavior of `-ₚ`.
@[default_instance 10001]
instance (priority := high) : PyHAdd Int Int Int where
  hAdd := fun a b => a + b

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

infixl:65 " -ₚ " => PyHSub.hSub

@[default_instance]
instance (priority := low) {α β γ} [HSub α β γ] : PyHSub α β γ where
  hSub := HSub.hSub

instance (priority := high) : PyHSub Nat Nat Int where
  hSub := fun a b => (a : Int) - (b : Int)

-- Not a `default_instance`: this instance must remain available for a genuine `Rat - Int`,
-- but it must NOT be used to *default* an unconstrained left operand to `Rat`. Marking it
-- default made `ok -ₚ ng` (with `ng : Int` and `ok` a yet-unconstrained parameter) pin
-- `ok := Rat`, which then forced integer-only follow-ups like `pyFloorDiv (ok +ₚ ng)` to fail.
instance (priority := high) : PyHSub Rat Int Rat where
  hSub := fun a b => (a : Rat) - (b : Int)

-- Symmetric `Int - Rat` (e.g. `1 - g/k` in a logistic term where `g/k : ℚ`). Plain instance, NOT
-- `@[default_instance]` (same rat-default-instance hazard note as above).
instance (priority := high) : PyHSub Int Rat Rat where
  hSub := fun a b => (a : Rat) - b

class PyHMul (α β : Type) (γ : outParam Type) where
  hMul : α → β → γ

infixl:70 " *ₚ " => PyHMul.hMul

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

/-! Symmetric string repetition `n * s` (Python allows the count on either side). -/
instance : PyHMul Nat String String where
  hMul := fun n s => String.intercalate "" (List.replicate n s)

instance : PyHMul Int String String where
  hMul := fun n s => if n < 0 then "" else String.intercalate "" (List.replicate n.toNat s)

/-- Python list repetition `xs * n` as an ordinary function (not the `outParam`-result `*ₚ`
operator). Codegen targets this for a *list-literal* operand (`[None] * n`, `[0] * n`) so the
result type is concretely `List α` even when `α` is still an unresolved metavariable — the
`outParam` operator would leave the whole list type postponed, which then stalls later
`pyIter`/`pyGetItem`/`pySetItem` on a `[None] * n` placeholder whose element type only gets
pinned by a later assignment. A non-positive count yields `[]`, matching Python. -/
def pyListRepeat {α : Type} (xs : List α) (n : Int) : List α :=
  if n ≤ 0 then [] else (List.replicate n.toNat xs).flatten

/-- Python list repetition `xs * n` (and the symmetric `n * xs`): repeats the list `n` times,
matching `[0] * n` style array initialization. A non-positive count yields `[]`. -/
instance {α : Type} : PyHMul (List α) Int (List α) where
  hMul := fun xs n => pyListRepeat xs n

instance {α : Type} : PyHMul Int (List α) (List α) where
  hMul := fun n xs => pyListRepeat xs n

@[default_instance]
instance (priority := high) : PyHMul Rat Rat Rat where
  hMul := fun a b => (a : Rat) * (b : Rat)

-- Mixed `Rat * Int` / `Rat * Nat` (and symmetric). Plain instances, NOT `@[default_instance]`:
-- a default here would pin an unconstrained operand to `Rat` (the rat-default-instance hazard).
instance (priority := high) : PyHMul Rat Int Rat where hMul := fun a b => a * (b : Rat)
instance (priority := high) : PyHMul Int Rat Rat where hMul := fun a b => (a : Rat) * b
instance (priority := high) : PyHMul Rat Nat Rat where hMul := fun a b => a * (b : Rat)
instance (priority := high) : PyHMul Nat Rat Rat where hMul := fun a b => (a : Rat) * b

-- Keep `Int * Int = Int` (Python semantics) even with still-metavariable operands — see the
-- `PyHAdd Int Int Int` note above (the rat-default-instance hazard, here for `*ₚ`).
@[default_instance 10001]
instance (priority := high) : PyHMul Int Int Int where hMul := fun a b => a * b

class PyHPow (α β : Type) (γ : outParam Type) where
  hPow : α → β → γ

infixr:80 " ^ₚ " => PyHPow.hPow

class PyModulo (α β : Type) (γ : outParam Type) where
  hMod : α → β → γ

infixl:70 " %ₚ " => PyModulo.hMod

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

infixl:70 " /ₚ " => PyHDiv.hDiv

@[default_instance]
instance {α β γ} [HDiv α β γ] : PyHDiv α β γ where
  hDiv := HDiv.hDiv

instance (priority := high) : PyHDiv Int Int Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

-- Mixed `Rat / Int` / `Rat / Nat` (and symmetric). The common case is `total / len(xs)` where
-- `total : Rat` and `len(xs) : Int`. Plain instances (no `@[default_instance]`) — see the mul note.
instance (priority := high) : PyHDiv Rat Int Rat where hDiv := fun a b => a / (b : Rat)
instance (priority := high) : PyHDiv Int Rat Rat where hDiv := fun a b => (a : Rat) / b
instance (priority := high) : PyHDiv Rat Nat Rat where hDiv := fun a b => a / (b : Rat)
instance (priority := high) : PyHDiv Nat Rat Rat where hDiv := fun a b => (a : Rat) / b

instance (priority := high) : PyHDiv Nat Nat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

@[default_instance]
instance (priority := high) : PyHDiv Rat Rat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

-- Python true division `/` always yields a float when a float is involved. `pyLen`/`int` operands
-- are `Int`, so e.g. `total / len(xs)` is `Float / Int`; these instances cover the mixed cases.
instance (priority := high) : PyHDiv Float Int Float where
  hDiv := fun a b => a / Rat.toFloat (b : Rat)

instance (priority := high) : PyHDiv Int Float Float where
  hDiv := fun a b => Rat.toFloat (a : Rat) / b

instance (priority := high) : PyHDiv Float Nat Float where
  hDiv := fun a b => a / Rat.toFloat (b : Rat)

instance (priority := high) : PyHDiv Nat Float Float where
  hDiv := fun a b => Rat.toFloat (a : Rat) / b

/-! Mixed `Float`/`Int` and `Float`/`Nat` `+`/`-`/`*` (Python promotes the integer to float).
Lean has no heterogeneous `HAdd Float Int` etc., so these are needed whenever an integer literal
or a `len()`/`int()` result meets a float — e.g. `1 - g / k`, `grass[i] + 1`, `2 * x`. -/
instance (priority := high) : PyHAdd Float Int Float where hAdd a b := a + Rat.toFloat (b : Rat)
instance (priority := high) : PyHAdd Int Float Float where hAdd a b := Rat.toFloat (a : Rat) + b
instance (priority := high) : PyHAdd Float Nat Float where hAdd a b := a + Rat.toFloat (b : Rat)
instance (priority := high) : PyHAdd Nat Float Float where hAdd a b := Rat.toFloat (a : Rat) + b

instance (priority := high) : PyHSub Float Int Float where hSub a b := a - Rat.toFloat (b : Rat)
instance (priority := high) : PyHSub Int Float Float where hSub a b := Rat.toFloat (a : Rat) - b
instance (priority := high) : PyHSub Float Nat Float where hSub a b := a - Rat.toFloat (b : Rat)
instance (priority := high) : PyHSub Nat Float Float where hSub a b := Rat.toFloat (a : Rat) - b

instance (priority := high) : PyHMul Float Int Float where hMul a b := a * Rat.toFloat (b : Rat)
instance (priority := high) : PyHMul Int Float Float where hMul a b := Rat.toFloat (a : Rat) * b
instance (priority := high) : PyHMul Float Nat Float where hMul a b := a * Rat.toFloat (b : Rat)
instance (priority := high) : PyHMul Nat Float Float where hMul a b := Rat.toFloat (a : Rat) * b

/-! ## Mixed `ℚ`/`ℝ` (and `ℤ`/`ℕ` with `ℝ`) arithmetic — exact mode

In exact mode a transcendental yields `ℝ` while the surrounding rational/integer values are `ℚ`/`ℤ`,
e.g. `g *ₚ math.log (g +ₚ 1)` with `g : ℚ`. Lean has no heterogeneous `HMul ℚ ℝ`, so these promote
the rational/integer operand into `ℝ` and produce `ℝ`. (`ℝ×ℝ` already works via the generic
`[HMul α β γ]` instance.) `noncomputable`, since the `ℚ ↪ ℝ` / `ℤ ↪ ℝ` casts are. -/
noncomputable instance (priority := high) : PyHMul Real Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Rat Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Rat Real where hMul a b := a * (b : ℝ)
noncomputable instance (priority := high) : PyHMul Int Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Int Real where hMul a b := a * (b : ℝ)
noncomputable instance (priority := high) : PyHMul Nat Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Nat Real where hMul a b := a * (b : ℝ)

noncomputable instance (priority := high) : PyHAdd Real Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Rat Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Rat Real where hAdd a b := a + (b : ℝ)
noncomputable instance (priority := high) : PyHAdd Int Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Int Real where hAdd a b := a + (b : ℝ)
noncomputable instance (priority := high) : PyHAdd Nat Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Nat Real where hAdd a b := a + (b : ℝ)

noncomputable instance (priority := high) : PyHSub Real Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Rat Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Rat Real where hSub a b := a - (b : ℝ)
noncomputable instance (priority := high) : PyHSub Int Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Int Real where hSub a b := a - (b : ℝ)
noncomputable instance (priority := high) : PyHSub Nat Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Nat Real where hSub a b := a - (b : ℝ)

noncomputable instance (priority := high) : PyHDiv Real Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Rat Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Rat Real where hDiv a b := a / (b : ℝ)
noncomputable instance (priority := high) : PyHDiv Int Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Int Real where hDiv a b := a / (b : ℝ)
noncomputable instance (priority := high) : PyHDiv Nat Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Nat Real where hDiv a b := a / (b : ℝ)


/-! ## Auto-derived mixed numeric arithmetic — `PyNumJoin`

Rather than writing every mixed pair out four times (once per `+ - * /`), `PyNumJoin α β γ` names the
common result type `γ` of mixing `α` and `β` **once**, together with the two coercions into it. A
*single* generic instance per operator then derives all four. Adding a new numeric type later means
adding its coercion pairs here once — not `4 ×` new operator instances.

These are LOW priority and NOT `@[default_instance]`: the carefully-tuned homogeneous defaults above
(`Rat`/`Int` `@[default_instance]`, the `@[simp] rfl` lemmas) still win for same-type and
unconstrained-operand resolution; `PyNumJoin` only fires for a genuinely-mixed *concrete* pair that
no higher-priority instance already covers (e.g. `ℚ × Float`, which arises when a run-twin function
multiplies a shared `ℚ` constant by a `Float` local). The `ℝ` mixes stay explicit (`noncomputable`)
just above; this covers the computable tower `ℕ ⊂ ℤ ⊂ ℚ` and `Float`. -/
class PyNumJoin (α β : Type) (γ : outParam Type) where
  coeL : α → γ
  coeR : β → γ

namespace PyNumJoin
/-- `α` mixed with itself does not need a join (the homogeneous `[HAdd α α α]` instance handles it);
`mk2 f g` builds the two-coercion record for a genuinely mixed pair. -/
abbrev mk2 {α β γ} (f : α → γ) (g : β → γ) : PyNumJoin α β γ := ⟨f, g⟩
end PyNumJoin

-- ℕ ⊂ ℤ
instance : PyNumJoin Nat Int Int := .mk2 (Int.ofNat) id
instance : PyNumJoin Int Nat Int := .mk2 id (Int.ofNat)
-- · ⊂ ℚ
instance : PyNumJoin Nat Rat Rat := .mk2 (fun n => (n : ℚ)) id
instance : PyNumJoin Rat Nat Rat := .mk2 id (fun n => (n : ℚ))
instance : PyNumJoin Int Rat Rat := .mk2 (fun n => (n : ℚ)) id
instance : PyNumJoin Rat Int Rat := .mk2 id (fun n => (n : ℚ))
-- · ⊂ Float  (ℚ → Float is `Rat.toFloat`; this is the pair the prove/run twin split needs)
instance : PyNumJoin Nat Float Float := .mk2 (fun n => Float.ofNat n) id
instance : PyNumJoin Float Nat Float := .mk2 id (fun n => Float.ofNat n)
instance : PyNumJoin Int Float Float := .mk2 (fun n => Float.ofInt n) id
instance : PyNumJoin Float Int Float := .mk2 id (fun n => Float.ofInt n)
instance : PyNumJoin Rat Float Float := .mk2 Rat.toFloat id
instance : PyNumJoin Float Rat Float := .mk2 id Rat.toFloat

-- One generic instance per operator derives `+ - * /` for every `PyNumJoin` pair. Project through
-- the named `j` (its `β` is fixed) — a bare `PyNumJoin.coeL a` would leave `β` a metavar.
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Add γ] : PyHAdd α β γ where
  hAdd a b := j.coeL a + j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Sub γ] : PyHSub α β γ where
  hSub a b := j.coeL a - j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Mul γ] : PyHMul α β γ where
  hMul a b := j.coeL a * j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Div γ] : PyHDiv α β γ where
  hDiv a b := j.coeL a / j.coeR b


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
-- `&`, `|`, `^` are bitwise on integers *and* the binary set operations (intersection, union,
-- symmetric difference) on Python sets. They are typeclasses (Int instances here; the
-- list-backed set instances live in `Sets.lean`) so codegen emits one stable name per operator
-- and the operand type selects the meaning.
class PyBitAnd (α β : Type) (γ : outParam Type) where bitAnd : α → β → γ
class PyBitOr (α β : Type) (γ : outParam Type) where bitOr : α → β → γ
class PyBitXor (α β : Type) (γ : outParam Type) where bitXor : α → β → γ

/-- Python `a & b` (integer bitwise-and, or set intersection). -/
def pyBitAnd {α β γ : Type} [PyBitAnd α β γ] (a : α) (b : β) : γ := PyBitAnd.bitAnd a b
/-- Python `a | b` (integer bitwise-or, or set union). -/
def pyBitOr {α β γ : Type} [PyBitOr α β γ] (a : α) (b : β) : γ := PyBitOr.bitOr a b
/-- Python `a ^ b` (integer bitwise-xor, or set symmetric difference). -/
def pyBitXor {α β γ : Type} [PyBitXor α β γ] (a : α) (b : β) : γ := PyBitXor.bitXor a b

instance : PyBitAnd Int Int Int where bitAnd a b := Int.ofNat (Nat.land a.toNat b.toNat)
instance : PyBitOr Int Int Int where bitOr a b := Int.ofNat (Nat.lor a.toNat b.toNat)
instance : PyBitXor Int Int Int where bitXor a b := Int.ofNat (Nat.xor a.toNat b.toNat)

/-- Python `a << b`. -/
def pyShiftLeft (a b : Int) : Int := a * (2 ^ b.toNat)

/-- Python `a >> b` (floor division by `2 ^ b`). -/
def pyShiftRight (a b : Int) : Int := Int.fdiv a (2 ^ b.toNat)

/-!
## Reduction lemmas — `simp` rewrites the Python operators to the standard ones

Generated code uses `+ₚ -ₚ *ₚ /ₚ` (the `PyH*` typeclasses). They are *definitionally* the
ordinary `ℚ`/`ℤ` operators, but `ring`/`nlinarith`/`linarith` don't see through the notation.
These `@[simp]` lemmas (all `rfl`) let a proof do `simp [myFunc]` to expose plain `+ - * /`, after
which `ring`/`nlinarith` close the goal. So theorems can be proved directly on the generated
`ℚ` definitions (no re-statement over `ℝ`). -/

-- Also in the `taste_ingr` set, so `taste?`'s `simp only [taste_ingr]` clears the `*ₚ` operators
-- (turning them into plain `+ - * /`) without naming each lemma in the tactic.
@[simp, taste_ingr] theorem pyAdd_rat (a b : ℚ) : a +ₚ b = a + b := rfl
@[simp, taste_ingr] theorem pySub_rat (a b : ℚ) : a -ₚ b = a - b := rfl
@[simp, taste_ingr] theorem pyMul_rat (a b : ℚ) : a *ₚ b = a * b := rfl
@[simp, taste_ingr] theorem pyDiv_rat (a b : ℚ) : a /ₚ b = a / b := rfl

@[simp, taste_ingr] theorem pyAdd_int (a b : ℤ) : a +ₚ b = a + b := rfl
@[simp, taste_ingr] theorem pySub_int (a b : ℤ) : a -ₚ b = a - b := rfl
@[simp, taste_ingr] theorem pyMul_int (a b : ℤ) : a *ₚ b = a * b := rfl

end PastaLean
