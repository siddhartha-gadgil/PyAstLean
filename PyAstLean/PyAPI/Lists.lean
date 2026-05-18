import Mathlib

namespace PyAstLean

/-- Concrete list implementation for Python-style `append`. -/
def pyListAppend : List α → α → List α
  | lst, elem => lst ++ [elem]

/--
Concrete list implementation for Python-style `pop(index)`.

If the index is out of bounds, return the provided default and leave the list unchanged.
-/
def pyListPop (xs : List α) (idx : Int) (default : Option α := none) : (Option α × List α) :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if hUpper : natIdx < xs.length then
      let value := xs.get ⟨natIdx, hUpper⟩
      (some value, xs.eraseIdx natIdx)
    else
      (default, xs)
  else
    (default, xs)

/--
Public runtime surface for Python `append`.

Keep codegen targeting `pyAppend`; if another runtime type later needs append-like
behavior, this public name can be promoted to a protocol without changing the
generated Lean surface.
-/
def pyAppend : List α → α → List α :=
  pyListAppend

end PyAstLean
