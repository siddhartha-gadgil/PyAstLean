import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

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

/-- Lexicographic ordering on pairs, matching Python's tuple comparison (compare first
components, break ties by the second). This makes `sorted`/`min`/`max`/`<` over tuples — e.g.
`sorted(zip(a, b))` — resolve, since Lean provides no default `Ord` on `α × β`. -/
instance instPyOrdProd [Ord α] [Ord β] : Ord (α × β) where
  compare p q := match compare p.1 q.1 with
    | Ordering.eq => compare p.2 q.2
    | o => o

/-- Boolean comparison derived from `Ord`, suitable for `mergeSort`. -/
def pyOrdLe [Ord α] (a b : α) : Bool :=
  compare a b != Ordering.gt

/--
Python `sorted(iterable, key=…, reverse=…)` / `list.sort(key=…, reverse=…)`.

Sorts the iterable's elements by a projected key. `List.mergeSort` is stable, matching
Python: elements comparing equal under `key` keep their original relative order, and that
holds for `reverse := true` as well (we negate the strict comparison, not the whole list, so
equal keys are *not* re-reversed). When `reverse` is `false` the `key`-less form is just
`key := id`.
-/
def pySortBy {α β γ : Type} [PyIterable α β] [Ord γ]
    (key : β → γ) (reverse : Bool := false) (xs : α) : List β :=
  let le := fun a b =>
    let c := compare (key a) (key b)
    if reverse then c != Ordering.lt else c != Ordering.gt
  (pyIter xs).mergeSort le

/-- Sorting a list returns its elements in ascending order. -/
instance [Ord α] : PySort (List α) α where
  pySort xs := xs.mergeSort pyOrdLe

/-- Sorting an array sorts its elements after converting to a list. -/
instance [Ord α] : PySort (Array α) α where
  pySort xs := xs.toList.mergeSort pyOrdLe

/--
Sorting a string follows Python `sorted(str)` semantics and returns the characters in ascending
order as one-character strings (Python has no character type, so `sorted(s)` is a list of
length-1 `str`s).
-/
instance : PySort String String where
  pySort s := (s.toList.map (·.toString)).mergeSort pyOrdLe

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

end PastaLean
