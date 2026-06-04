import Mathlib

namespace PyAstLean

/--
Python truthiness, `bool(x)` — the implicit conversion used by `if x:`, `while x:`, `not x`,
and boolean operators. Numbers are truthy when non-zero; strings/lists/dicts/sets when
non-empty; `None`/`Option.none` is falsy; an actual `Bool` is itself.

Codegen wraps condition expressions in `pyTruthy` so a non-`Bool` value (the common
`if cnt:` / `while stack:` idiom) is accepted where Lean wants a `Bool`. `PyTruthy Bool` is
the identity, so wrapping an already-boolean test (e.g. a comparison) is a no-op.
-/
class PyTruthy (α : Type) where
  truthy : α → Bool

/-- Dispatch Python truthiness through the `PyTruthy` typeclass. -/
def pyTruthy {α : Type} [PyTruthy α] (x : α) : Bool := PyTruthy.truthy x

instance : PyTruthy Bool where truthy b := b
instance : PyTruthy Int where truthy n := n != 0
instance : PyTruthy Nat where truthy n := n != 0
instance : PyTruthy Rat where truthy q := q != 0
instance : PyTruthy Float where truthy x := x != 0.0
instance : PyTruthy Char where truthy _ := true
instance : PyTruthy String where truthy s := !s.isEmpty
instance {α : Type} : PyTruthy (List α) where truthy xs := !xs.isEmpty
instance {α : Type} : PyTruthy (Option α) where truthy o := o.isSome
instance {κ ν : Type} [BEq κ] [Hashable κ] : PyTruthy (Std.HashMap κ ν) where
  truthy m := !m.isEmpty

end PyAstLean
