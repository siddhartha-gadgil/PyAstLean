import Mathlib

namespace PyAstLean

/--
Typeclass for Python-style length queries.

Use this for builtins like `len(x)` when one Python surface operation should work
across several Lean runtime types.
-/
class PyLen (α : Type) where
  pyLen : α → Int

/-- Dispatch `len`-style queries through the `PyLen` typeclass. -/
def pyLen {α : Type} [PyLen α] (x : α) : Int :=
  PyLen.pyLen x

/-- Lists use their element count as Python length. -/
instance : PyLen (List α) where
  pyLen xs := xs.length

/-- Strings use their Lean string length as Python length. -/
instance : PyLen String where
  pyLen s := s.length

/-- Hash maps use their number of stored key-value pairs as Python length. -/
instance [BEq α] [Hashable α] : PyLen (Std.HashMap α β) where
  pyLen m := m.size

end PyAstLean
