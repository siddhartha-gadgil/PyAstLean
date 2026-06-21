import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.Operators

namespace PastaLean

/-!
Python-style sets.

Sets are modeled as a deduplicated `List` so that the existing list-backed protocols
(`pyContains` for `in`, `pyLen` for `len`, `PyIterable` for iteration/comprehensions) apply
unchanged. Elements only need `BEq` for the membership checks. Insertion order is preserved,
which is irrelevant to Python set semantics but keeps output deterministic.

Like the other container runtimes these are immutable values: `s.add(x)` rebuilds the list
and the codegen reassigns the variable (`s := pySetAdd s x`).
-/

/-- Build a set from a list, dropping duplicates (used for `{a, b, c}` literals and `set(xs)`). -/
def pySetFromList {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Python `set(iterable)` for any iterable (lists, `range(...)`, comprehensions, strings,
`map`/`zip` results), normalized through `pyIter` so `set("abc")`, `set(range(n))`, etc. work. -/
def pySet {α β : Type} [PyIterable β α] [BEq α] (xs : β) : List α :=
  pySetFromList (pyIter xs)

/-- Python `s.add(x)`: insert `x` if not already present. -/
def pySetAdd {α : Type} [BEq α] (s : List α) (x : α) : List α :=
  if s.contains x then s else s ++ [x]

/-- Python `s.discard(x)`: remove `x` if present (no error if absent). -/
def pySetDiscard {α : Type} [BEq α] (s : List α) (x : α) : List α :=
  s.filter (fun y => y != x)

/-- Python `s.remove(x)`: like `discard` here (we do not raise `KeyError` on absence). -/
def pySetRemove {α : Type} [BEq α] (s : List α) (x : α) : List α :=
  pySetDiscard s x

/-! ### Binary set operations (`|`, `&`, `-`, `^`)

Sets are deduplicated lists, so these operate elementwise and keep the result deduplicated. Each
takes two already-deduplicated sets and returns a deduplicated set. -/

/-- Python set union `a | b`: elements in either set. -/
def pySetUnion {α : Type} [BEq α] (a b : List α) : List α :=
  b.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) a

/-- Python set intersection `a & b`: elements in both sets. -/
def pySetIntersection {α : Type} [BEq α] (a b : List α) : List α :=
  a.filter (fun x => b.contains x)

/-- Python set difference `a - b`: elements of `a` not in `b`. -/
def pySetDifference {α : Type} [BEq α] (a b : List α) : List α :=
  a.filter (fun x => !b.contains x)

/-- Python symmetric difference `a ^ b`: elements in exactly one of the two sets. -/
def pySetSymmetricDifference {α : Type} [BEq α] (a b : List α) : List α :=
  (a.filter (fun x => !b.contains x)) ++ (b.filter (fun x => !a.contains x))

/-! The binary set operators reuse the same surface names as the integer bitwise operators
(`&`, `|`, `^`) and Python subtraction (`-`), so a set expression `a & b` lowers identically to
codegen and the list-backed instance is selected by type. -/
instance {α : Type} [BEq α] : PyBitAnd (List α) (List α) (List α) where bitAnd := pySetIntersection
instance {α : Type} [BEq α] : PyBitOr (List α) (List α) (List α) where bitOr := pySetUnion
instance {α : Type} [BEq α] : PyBitXor (List α) (List α) (List α) where bitXor := pySetSymmetricDifference
instance {α : Type} [BEq α] : PyHSub (List α) (List α) (List α) where hSub := pySetDifference

end PastaLean
