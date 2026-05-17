import Mathlib

namespace PyAstLean

/-
For `list.append(elem)`, we want to return a new list with the element appended to the end.
-/
def pyListAppend : List α → α → List α
  | lst, elem => lst ++ [elem]


end PyAstLean
