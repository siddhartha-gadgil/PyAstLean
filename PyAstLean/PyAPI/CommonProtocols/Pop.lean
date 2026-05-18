import Mathlib
import PyAstLean.PyAPI.Dicts
import PyAstLean.PyAPI.Lists

namespace PyAstLean

/--
Protocol for Python-style `pop`.

Different runtime types may use different key/index types and element/value types, so
the protocol carries both as associated types.
-/
class PyPop (α : Type) where
  Key : Type
  Elem : Type
  /--
  For dictionary-like types, `default` is used when the key is missing.
  For list-like types, `default` is used when the index is out of bounds.
  -/
  pyPop : α → Key → Option Elem → (Option Elem × α)

/--
Codegen should target this stable name; concrete types extend the behavior by adding
`PyPop` instances.
-/
def pyPop {α : Type} [inst : PyPop α] (container : α) (key : inst.Key)
    (default : Option inst.Elem := none) : (Option inst.Elem × α) :=
  inst.pyPop container key default

/-- Popping from List -/
instance : PyPop (List α) where
  Key := Int
  Elem := α
  pyPop xs idx default := pyListPop xs idx default

/-- Instance for popping from a HashMap. -/
instance [BEq α] [Hashable α] : PyPop (Std.HashMap α β) where
  Key := α
  Elem := β
  pyPop m key default := pyDictPop m key default

end PyAstLean
