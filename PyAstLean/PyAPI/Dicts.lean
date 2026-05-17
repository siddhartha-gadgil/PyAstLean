import Mathlib

namespace PyAstLean

/-
For `dict.items()`, we want to return a list of key-value pairs.
-/
def pyDictItems [BEq α] [Hashable α] : Std.HashMap α β → List (α × β)
  | m => m.toList

/-
For `dict.keys()`, we want to return a list of keys.
-/
def pyDictKeys [BEq α] [Hashable α] : Std.HashMap α β → List α
  | m => m.toList.map (fun (k, _) => k)

/-
For `dict.values()`, we want to return a list of values.
-/
def pyDictValues [BEq α] [Hashable α] : Std.HashMap α β → List β
  | m => m.toList.map (fun (_, v) => v)

/-
For `dict.clear()`, we want to return an empty dictionary. Since `Std.HashMap` is immutable, we can just return a new empty map.
-/
def pyDictClear [BEq α] [Hashable α] (_ : Std.HashMap α β) : Std.HashMap α β :=
  {}

/-
For `dict.pop(key, default)`, we want to return a tuple of the value associated with the key (or the default if the key is not present) and the new dictionary with the key removed if it was present.
-/
def pyDictPop [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : Option β := none) : (Option β × Std.HashMap α β) :=
  match m.get? key with
  | some value => (some value, m.erase key)
  | none => (default, m)

def pyDictUpdate [BEq α] [Hashable α] (m : Std.HashMap α β) (updates : List (α × β)) : Std.HashMap α β :=
  updates.foldl (fun acc (k, v) => acc.insert k v) m

-- #eval do
--   let myMap : Std.HashMap String Nat := {}

--   -- Inserting values
--   let updatedMap := myMap.insert "apple" 1
--   let updatedMap2 := updatedMap.insert "banana" 2

--   pyItems updatedMap2 -- [("apple", 1), ("banana", 2)]

end PyAstLean
