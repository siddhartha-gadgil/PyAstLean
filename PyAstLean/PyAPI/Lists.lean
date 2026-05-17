import Mathlib

namespace PyAstLean

/-- Concrete list implementation for Python-style `append`. -/
def pyListAppend : List α → α → List α
  | lst, elem => lst ++ [elem]

/--
Public runtime surface for Python `append`.

Keep codegen targeting `pyAppend`; if another runtime type later needs append-like
behavior, this public name can be promoted to a protocol without changing the
generated Lean surface.
-/
def pyAppend : List α → α → List α :=
  pyListAppend

end PyAstLean
