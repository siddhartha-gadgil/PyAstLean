import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/-!
For python's `reversed()` builtin, which returns an iterator that yields the iterable of a sequence in reverse order.
-/

/-!
`PyIterable` is a protocol, not a concrete return type, so `reversed(...)` needs a small
runtime wrapper whose public behavior is "this can be iterated with `pyIter`".
-/
structure PyReversedIter (α : Type) where
  items : List α
  deriving Inhabited, Repr

instance : PyIterable (PyReversedIter α) α where
  toPyList value := value.items

class PyReversible (α : Type) (β : outParam Type) where
  toReversedIter : α → PyReversedIter β

/-- Dispatch Python-style reversed iteration through the `PyReversible` protocol. -/
def pyReversed {α β : Type} [inst : PyReversible α β] (value : α) : PyReversedIter β :=
  inst.toReversedIter value

/-- Any `PyIterable` can be reversed by converting to a list and reversing it. -/
instance {α β : Type} [PyIterable α β] : PyReversible α β where
  toReversedIter value := ⟨(pyIter value).reverse⟩

end PastaLean
