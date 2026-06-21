import Mathlib
import PastaLean.PyAPI.Dicts

namespace PastaLean

/--
Protocol for Python-style `pop`.

The key/index type `κ` and element/value type `β` are `outParam`s (not associated types):
an associated `Key`/`Elem` projection stays "stuck" and never reduces to a concrete type,
breaking resolution downstream of `pyPop`'s result. As `outParam`s they reduce concretely
once the container type `α` is known.
-/
class PyPop (α : Type) (κ : outParam Type) (β : outParam Type) where
  /--
  For dictionary-like types, `default` is used when the key is missing.
  For list-like types, `default` is used when the index is out of bounds.
  -/
  pyPop : α → κ → Option β → (Option β × α)

/--
Codegen should target this stable name; concrete types extend the behavior by adding
`PyPop` instances.
-/
def pyPop {α κ β : Type} [PyPop α κ β] (container : α) (key : κ)
    (default : Option β := none) : (Option β × α) :=
  PyPop.pyPop container key default

/--
Local list-pop helper kept here to avoid importing `PastaLean.PyAPI.Lists`, which
currently exposes other public method names that clash with dictionary names.
-/
def pyProtocolListPop (xs : List α) (idx : Int) (default : Option α := none) : (Option α × List α) :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if hUpper : natIdx < xs.length then
      let value := xs.get ⟨natIdx, hUpper⟩
      (some value, xs.eraseIdx natIdx)
    else
      (default, xs)
  else
    (default, xs)

/-- Popping from List -/
instance : PyPop (List α) Int α where
  pyPop xs idx default := pyProtocolListPop xs idx default

/-! Python `pop` removes an element *and* returns it. Since the runtime containers are
immutable values, codegen splits this into two independent reads of the original container:
`pyPopValue` (the returned element) and `pyPopRest` (the container with that element removed).
The index defaults to `-1` (the last element), matching `list.pop()`; `set.pop()` removes an
arbitrary element, and "the last" is an acceptable arbitrary choice for the list-backed set. -/

/-- Normalize a possibly-negative `pop` index against a length; out-of-range stays out of range. -/
private def pyPopIndex (len : Nat) (idx : Int) : Int :=
  if idx < 0 then (len : Int) + idx else idx

/-- The element `pop(idx)` returns (defaulting to the last). Out-of-range yields `default`. -/
def pyPopValue [Inhabited α] (xs : List α) (idx : Int := -1) : α :=
  let i := pyPopIndex xs.length idx
  if 0 ≤ i ∧ i < xs.length then xs[i.toNat]! else default

/-- The container after `pop(idx)` removes its element (defaulting to the last). -/
def pyPopRest (xs : List α) (idx : Int := -1) : List α :=
  let i := pyPopIndex xs.length idx
  if 0 ≤ i ∧ i < xs.length then xs.eraseIdx i.toNat else xs

/-- Instance for popping from a HashMap. -/
instance [BEq α] [Hashable α] : PyPop (Std.HashMap α β) α β where
  pyPop m key default := pyDictPop m key default

end PastaLean
