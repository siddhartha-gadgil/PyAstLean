import Mathlib

namespace PyAstLean

/--
Protocol for Python-style sorting.

This models builtin `sorted(...)` rather than in-place `list.sort()`. Different runtime
types may expose different underlying element collections, but the public result is a
sorted list of elements.

The element type `β` is an `outParam` (not an associated type) so the result type of
`pySort value` reduces to a concrete `List β` once the container is known — an associated
`Elem` projection would stay stuck and break downstream resolution (e.g. `BEq`/`Hashable`
on a sorted dict key).
-/
class PySort (α : Type) (β : outParam Type) where
  pySort : α → List β

/--
Public runtime surface for Python-style sorting.

Codegen can target `pySort` as one stable name; individual runtime types extend the
behavior by adding `PySort` instances.
-/
def pySort {α β : Type} [PySort α β] (value : α) : List β :=
  PySort.pySort value

/-- Boolean comparison derived from `Ord`, suitable for `mergeSort`. -/
def pyOrdLe [Ord α] (a b : α) : Bool :=
  compare a b != Ordering.gt

/-- Sorting a list returns its elements in ascending order. -/
instance [Ord α] : PySort (List α) α where
  pySort xs := xs.mergeSort pyOrdLe

/-- Sorting an array sorts its elements after converting to a list. -/
instance [Ord α] : PySort (Array α) α where
  pySort xs := xs.toList.mergeSort pyOrdLe

/--
Sorting a string follows Python `sorted(str)` semantics and returns the characters in
ascending order.
-/
instance : PySort String Char where
  pySort s := s.toList.mergeSort pyOrdLe

/--
Sorting a dictionary follows Python `sorted(dict)` semantics and sorts the keys.
-/
instance {β : Type} [Ord α] [BEq α] [Hashable α] : PySort (Std.HashMap α β) α where
  pySort m := (m.toList.map Prod.fst).mergeSort pyOrdLe

/--
Sorting a homogeneous 2-tuple returns a sorted list of its elements.

This matches `sorted((a, b))` rather than preserving tuple shape.
-/
instance [Ord α] : PySort (α × α) α where
  pySort p := [p.1, p.2].mergeSort pyOrdLe

-- #eval pySort #[3, 1, 4, 1, 5, 9] -- [1, 1, 3, 4, 5, 9]

end PyAstLean
