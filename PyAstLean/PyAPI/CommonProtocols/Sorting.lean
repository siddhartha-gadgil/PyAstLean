import Mathlib

namespace PyAstLean

/--
Protocol for Python-style sorting.

This models builtin `sorted(...)` rather than in-place `list.sort()`. Different runtime
types may expose different underlying element collections, but the public result is a
sorted list of elements.
-/
class PySort (α : Type) where
  Elem : Type
  pySort : α → List Elem

/--
Public runtime surface for Python-style sorting.

Codegen can target `pySort` as one stable name; individual runtime types extend the
behavior by adding `PySort` instances.
-/
def pySort {α : Type} [inst : PySort α] (value : α) : List inst.Elem :=
  inst.pySort value

/-- Boolean comparison derived from `Ord`, suitable for `mergeSort`. -/
def pyOrdLe [Ord α] (a b : α) : Bool :=
  compare a b != Ordering.gt

/-- Sorting a list returns its elements in ascending order. -/
instance [Ord α] : PySort (List α) where
  Elem := α
  pySort xs := xs.mergeSort pyOrdLe

/-- Sorting an array sorts its elements after converting to a list. -/
instance [Ord α] : PySort (Array α) where
  Elem := α
  pySort xs := xs.toList.mergeSort pyOrdLe

/--
Sorting a string follows Python `sorted(str)` semantics and returns the characters in
ascending order.
-/
instance : PySort String where
  Elem := Char
  pySort s := s.toList.mergeSort pyOrdLe

/--
Sorting a dictionary follows Python `sorted(dict)` semantics and sorts the keys.
-/
instance [Ord α] [BEq α] [Hashable α] : PySort (Std.HashMap α β) where
  Elem := α
  pySort m := (m.toList.map Prod.fst).mergeSort pyOrdLe

/--
Sorting a homogeneous 2-tuple returns a sorted list of its elements.

This matches `sorted((a, b))` rather than preserving tuple shape.
-/
instance [Ord α] : PySort (α × α) where
  Elem := α
  pySort p := [p.1, p.2].mergeSort pyOrdLe

-- #eval pySort #[3, 1, 4, 1, 5, 9] -- [1, 1, 3, 4, 5, 9]

end PyAstLean
