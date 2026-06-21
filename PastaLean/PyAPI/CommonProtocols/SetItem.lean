import Mathlib

namespace PastaLean

/--
Typeclass for Python-style item assignment, `container[index] = value`.

Lists and dicts are immutable values in this runtime, so item assignment is modeled as a
pure rebuild: `pySetItem c i v` returns a new container with the slot updated, and the
codegen reassigns the variable (`c := pySetItem c i v`). The index type `ι` and value type
`β` are `outParam`s (not associated types): an associated `Index`/`Value` projection stays
"stuck" and never reduces to a concrete type, which breaks resolution of any instance needed
on the result; as `outParam`s they reduce concretely once the container type `α` is known.
-/
class PySetItem (α : Type) (ι : outParam Type) (β : outParam Type) where
  setItem : α → ι → β → α

/-- Dispatch `container[index] = value` through the `PySetItem` typeclass. -/
def pySetItem {α ι β : Type} [PySetItem α ι β] (c : α) (i : ι) (v : β) : α :=
  PySetItem.setItem c i v

/-- Lists support item assignment with Python negative-index semantics; an out-of-range
index panics with an `IndexError`, matching `pyListGetItem`. -/
instance {β : Type} : PySetItem (List β) Int β where
  setItem xs idx v :=
    let len := xs.length
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      panic! "IndexError: list assignment index out of range"
    else
      xs.set trueIdx.toNat v

/-- Assigning a concrete value into an `Option`-element list stores it as `some v`. This is the
`[None] * n` placeholder pattern: the list starts as `none`s (the unset sentinel) and `xs[i] = v`
fills slot `i` with `some v`, leaving the element type free to unify with `v`. Higher priority
than the generic list instance so a `List (Option α)` container prefers wrapping a bare `α` over
demanding an already-`Option` value. -/
instance (priority := high) {α : Type} : PySetItem (List (Option α)) Int α where
  setItem xs idx v :=
    let len := xs.length
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      panic! "IndexError: list assignment index out of range"
    else
      xs.set trueIdx.toNat (some v)

/-- Dictionaries support item assignment as insert/overwrite. -/
instance {κ ν : Type} [BEq κ] [Hashable κ] : PySetItem (Std.HashMap κ ν) κ ν where
  setItem m k v := m.insert k v

/--
Typeclass for Python-style item deletion, `del container[index]`.

Like the other item protocols, the runtime containers are immutable values, so deletion is a
rebuild: `pyDelItem c i` returns a new container without that slot, and codegen reassigns the
variable (`c := pyDelItem c i`). The index type is an `outParam` so it reduces once the
container type is known.
-/
class PyDelItem (α : Type) (ι : outParam Type) where
  delItem : α → ι → α

/-- Dispatch `del container[index]` through the `PyDelItem` typeclass. -/
def pyDelItem {α ι : Type} [PyDelItem α ι] (c : α) (i : ι) : α :=
  PyDelItem.delItem c i

/-- `del xs[i]` removes the element at `i` (Python negative-index semantics); an out-of-range
index leaves the list unchanged. -/
instance {β : Type} : PyDelItem (List β) Int where
  delItem xs idx :=
    let len := xs.length
    let trueIdx := if idx < 0 then (len : Int) + idx else idx
    if 0 ≤ trueIdx && trueIdx < len then xs.eraseIdx trueIdx.toNat else xs

/-- `del d[k]` removes the key from a dictionary. -/
instance {κ ν : Type} [BEq κ] [Hashable κ] : PyDelItem (Std.HashMap κ ν) κ where
  delItem m k := m.erase k

end PastaLean
