import Mathlib

namespace PyAstLean

/--
Typeclass for Python-style item assignment, `container[index] = value`.

Lists and dicts are immutable values in this runtime, so item assignment is modeled as a
pure rebuild: `pySetItem c i v` returns a new container with the slot updated, and the
codegen reassigns the variable (`c := pySetItem c i v`). The index and value types vary by
container, so they are associated types (as in `PySort`).
-/
class PySetItem (α : Type) where
  Index : Type
  Value : Type
  setItem : α → Index → Value → α

/-- Dispatch `container[index] = value` through the `PySetItem` typeclass. -/
def pySetItem {α : Type} [inst : PySetItem α] (c : α) (i : inst.Index) (v : inst.Value) : α :=
  inst.setItem c i v

/-- Lists support item assignment with Python negative-index semantics; an out-of-range
index panics with an `IndexError`, matching `pyListGetItem`. -/
instance {β : Type} : PySetItem (List β) where
  Index := Int
  Value := β
  setItem xs idx v :=
    let len := xs.length
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      panic! "IndexError: list assignment index out of range"
    else
      xs.set trueIdx.toNat v

/-- Dictionaries support item assignment as insert/overwrite. -/
instance {κ ν : Type} [BEq κ] [Hashable κ] : PySetItem (Std.HashMap κ ν) where
  Index := κ
  Value := ν
  setItem m k v := m.insert k v

end PyAstLean
