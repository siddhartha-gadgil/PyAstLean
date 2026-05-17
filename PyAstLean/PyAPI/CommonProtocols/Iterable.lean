import Mathlib

namespace PyAstLean

/--
Typeclass for Python-style iteration.

Use this when codegen should normalize different iterable runtime values into one
public Lean operation, `pyIter`, without caring which concrete type supplied the
elements.
-/
class PyIterable (α : Type) where
  Elem : Type
  toPyList : α → List Elem

/-- Dispatch Python-style iteration through the `PyIterable` protocol. -/
def pyIter {α : Type} [inst : PyIterable α] (value : α) : List inst.Elem :=
  inst.toPyList value

/-- Lists are already Python-style iterables. -/
instance : PyIterable (List α) where
  Elem := α
  toPyList := id

/-- Arrays iterate by converting to lists. -/
instance : PyIterable (Array α) where
  Elem := α
  toPyList := Array.toList

/-- Strings iterate over characters. -/
instance : PyIterable String where
  Elem := Char
  toPyList := String.toList

end PyAstLean
