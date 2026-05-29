import Mathlib

namespace PyAstLean

/-
For Python's `bool` type, we can just use Lean's `Bool` directly.
Output of this function is simply False if it is 0, empty, or None, and True otherwise.
-/

class PyBool (α : Type) where
  pyBool : α → Bool

def pyBool {α : Type} [PyBool α] (x : α) : Bool :=
  PyBool.pyBool x

instance : PyBool Unit where
  pyBool _ := false

instance : PyBool Nat where
  pyBool n := n != 0

instance : PyBool Int where
  pyBool n := n != 0

instance : PyBool Float where
  pyBool f := f != 0.0

instance : PyBool Rat where
  pyBool r := r != 0

instance : PyBool Bool where
  pyBool b := b

instance : PyBool (List α) where
  pyBool xs := xs.length != 0

instance : PyBool String where
  pyBool s := s.length != 0

instance [BEq α] [Hashable α] : PyBool (Std.HashMap α β) where
  pyBool m := m.size != 0
