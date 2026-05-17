import Mathlib

namespace PyAstLean

class PyIterable (α : Type) where
  Elem : Type
  toPyList : α → List Elem

def pyIter {α : Type} [inst : PyIterable α] (value : α) : List inst.Elem :=
  inst.toPyList value

instance : PyIterable (List α) where
  Elem := α
  toPyList := id

instance : PyIterable (Array α) where
  Elem := α
  toPyList := Array.toList

instance : PyIterable String where
  Elem := Char
  toPyList := String.toList

end PyAstLean
