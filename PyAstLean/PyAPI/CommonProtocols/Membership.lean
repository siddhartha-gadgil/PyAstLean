import Mathlib

namespace PyAstLean

/--
Typeclass for Python-style membership tests.

This is the runtime API behind operations like `x in y` when one surface operation
should work across several container types.

This file defines the stable public Lean surface `pyContains`; individual runtime
types extend it by adding `PyContains` instances rather than changing codegen.
-/
class PyContains (α : Type) where
  Elem : Type
  contains : α → Elem → Bool

/-- Dispatch Python-style membership checks through the `PyContains` typeclass. -/
def pyContains {α : Type} [inst : PyContains α] (container : α) (value : inst.Elem) : Bool :=
  inst.contains container value

/-- Lists check membership with element equality. -/
instance [BEq α] : PyContains (List α) where
  Elem := α
  contains := fun xs x => xs.contains x

/-- Strings check membership character-by-character. -/
instance : PyContains String where
  Elem := Char
  contains := fun s c => s.contains c

/-- Hash maps check membership by key presence. -/
instance [BEq α] [Hashable α] : PyContains (Std.HashMap α β) where
  Elem := α
  contains := fun m k => m.contains k

end PyAstLean
