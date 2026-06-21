import Mathlib
import PastaLean.PyAPI.Lists
import PastaLean.PyAPI.Dicts

namespace PastaLean

/--
Protocol for Python-style `clear()`.

This keeps one stable public Lean surface, `pyClear`, while concrete runtime types
provide the actual clearing behavior via instances.
-/
class PyClear (α : Type) where
  /-- For `clear()`, return an empty container of the same type. -/
  pyClear : α → α

/-- Public runtime surface for Python `clear()`. -/
def pyClear {α : Type} [inst : PyClear α] (container : α) : α :=
  inst.pyClear container

/-- Lists clear to `[]`. -/
instance : PyClear (List α) where
  pyClear xs := pyListClear xs

/-- Dictionaries clear to the empty map. -/
instance [BEq α] [Hashable α] : PyClear (Std.HashMap α β) where
  pyClear m := pyDictClear m

end PastaLean
