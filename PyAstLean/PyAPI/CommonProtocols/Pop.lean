import Mathlib
import PyAstLean.PyAPI.Dicts

namespace PyAstLean

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
Local list-pop helper kept here to avoid importing `PyAstLean.PyAPI.Lists`, which
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

/-- Instance for popping from a HashMap. -/
instance [BEq α] [Hashable α] : PyPop (Std.HashMap α β) α β where
  pyPop m key default := pyDictPop m key default

end PyAstLean
