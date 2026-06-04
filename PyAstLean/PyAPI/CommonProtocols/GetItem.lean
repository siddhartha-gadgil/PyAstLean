import Mathlib
import PyAstLean.PyAPI.Core

namespace PyAstLean

/--
Typeclass for Python-style item access, `container[index]`.

The index type `ι` and value type `β` are `outParam`s (not associated types) so that the
result type of `pyGetItem c i` reduces to a concrete type once the container type is known —
an associated-type projection like `inst.Value` would stay stuck and break downstream
typeclass resolution (e.g. `PyPrintable`/`PyHAdd` on the result). Codegen emits one stable
name `pyGetItem c i` for the generic index case; string and tuple indexing keep their own
dedicated lowering.
-/
class PyGetItem (α : Type) (ι : outParam Type) (β : outParam Type) where
  getItem : α → ι → β

/-- Dispatch `container[index]` through the `PyGetItem` typeclass. -/
def pyGetItem {α ι β : Type} [PyGetItem α ι β] (c : α) (i : ι) : β :=
  PyGetItem.getItem c i

/-- Lists index by `Int` with Python negative-index semantics (reusing `pyListGetItem`). -/
instance {β : Type} [Inhabited β] : PyGetItem (List β) Int β where
  getItem xs i := pyListGetItem xs i

/-- A string variable indexed by `Int` yields the character at that position (negative indices
count from the end), consistent with iterating a string as `Char`s. An out-of-range index
falls back to the default character. -/
instance : PyGetItem String Int Char where
  getItem s i := (pyStringGetItem s i).getD default

/-- Dictionaries index by key; a missing key panics with a `KeyError`, matching Python's
strict `d[k]` (use `d.get(k, default)` for the non-raising form). -/
instance {κ ν : Type} [BEq κ] [Hashable κ] [Inhabited ν] : PyGetItem (Std.HashMap κ ν) κ ν where
  getItem m k :=
    match m.get? k with
    | some v => v
    | none => panic! "KeyError"

end PyAstLean
