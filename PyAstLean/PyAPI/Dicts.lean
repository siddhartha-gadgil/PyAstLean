import Mathlib

namespace PyAstLean

/-- Concrete dictionary implementation for Python-style `items()`. -/
def pyDictItems [BEq α] [Hashable α] : Std.HashMap α β → List (α × β)
  | m => m.toList

/--
Public runtime surface for Python `items()`.

Keep codegen targeting `pyItems`; if another dictionary-like runtime type later needs
an `items` view, this public name can be promoted without changing emitted syntax.
-/
def pyItems [BEq α] [Hashable α] : Std.HashMap α β → List (α × β) :=
  pyDictItems

/-- For `dict.keys()`, return the list of keys. -/
def pyDictKeys [BEq α] [Hashable α] : Std.HashMap α β → List α
  | m => m.toList.map (fun (k, _) => k)

/-- Public runtime surface for Python `keys()`. -/
def pyKeys [BEq α] [Hashable α] : Std.HashMap α β → List α :=
  pyDictKeys

/-- For `dict.values()`, return the list of values. -/
def pyDictValues [BEq α] [Hashable α] : Std.HashMap α β → List β
  | m => m.toList.map (fun (_, v) => v)

/-- Public runtime surface for Python `values()`. -/
def pyValues [BEq α] [Hashable α] : Std.HashMap α β → List β :=
  pyDictValues

/-- For `dict.clear()`, return an empty map. -/
def pyDictClear [BEq α] [Hashable α] (_ : Std.HashMap α β) : Std.HashMap α β :=
  {}

/-- Public runtime surface for Python `clear()`. -/
def pyClear [BEq α] [Hashable α] (m : Std.HashMap α β) : Std.HashMap α β :=
  pyDictClear m

/--
For `dict.pop(key, default)`, return the value associated with the key (or the
default if missing) together with the updated map.
-/
def pyDictPop [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : Option β := none) : (Option β × Std.HashMap α β) :=
  match m.get? key with
  | some value => (some value, m.erase key)
  | none => (default, m)

/-- Public runtime surface for Python `pop()`. -/
def pyPop [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : Option β := none) : (Option β × Std.HashMap α β) :=
  pyDictPop m key default

def pyDictUpdate [BEq α] [Hashable α] (m : Std.HashMap α β) (updates : List (α × β)) : Std.HashMap α β :=
  updates.foldl (fun acc (k, v) => acc.insert k v) m

/-- Public runtime surface for Python `update()`. -/
def pyUpdate [BEq α] [Hashable α] (m : Std.HashMap α β) (updates : List (α × β)) : Std.HashMap α β :=
  pyDictUpdate m updates

-- #eval do
--   let myMap : Std.HashMap String Nat := {}

--   -- Inserting values
--   let updatedMap := myMap.insert "apple" 1
--   let updatedMap2 := updatedMap.insert "banana" 2

--   pyItems updatedMap2 -- [("apple", 1), ("banana", 2)]

end PyAstLean
