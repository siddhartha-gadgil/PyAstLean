import Mathlib

namespace PyAstLean

/--
Python substring test `needle in haystack` for two strings. Implemented via `splitOn`:
a non-empty `needle` occurs in `haystack` iff splitting on it yields more than one piece.
The empty string is a substring of every string, matching Python.
-/
def pyStrContainsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else (haystack.splitOn needle).length > 1

/--
Typeclass for Python-style membership tests, `value in container`.

The element type `β` is an `outParam` so it is *determined by the container*: writing
`pyContains xs x` pins `x`'s type from `xs` (e.g. `List ℤ ⇒ ℤ`), which matters when `x` is
otherwise an unconstrained lambda parameter that would default to `ℚ`. The flip side is that
each container has a single element type, so `String` membership is `Char` here; *substring*
membership (`"ab" in s`) is handled at codegen time via `pyStrContainsSubstr`, since a string
literal on the left is detectable there.

This file defines the stable public Lean surface `pyContains`; individual runtime types
extend it by adding `PyContains` instances rather than changing codegen.
-/
class PyContains (α : Type) (β : outParam Type) where
  contains : α → β → Bool

/-- Dispatch Python-style membership checks through the `PyContains` typeclass. -/
def pyContains {α β : Type} [PyContains α β] (container : α) (value : β) : Bool :=
  PyContains.contains container value

/-- Lists check membership with element equality. -/
instance [BEq α] : PyContains (List α) α where
  contains := fun xs x => xs.contains x

/-- `c in s` for a character checks character-by-character membership. -/
instance : PyContains String Char where
  contains := fun s c => s.contains c

/-- Hash maps check membership by key presence. -/
instance {β : Type} [BEq α] [Hashable α] : PyContains (Std.HashMap α β) α where
  contains := fun m k => m.contains k

end PyAstLean
