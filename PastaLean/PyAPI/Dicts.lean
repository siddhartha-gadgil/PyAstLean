import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/-- Python `dict(pairs)`: build a hash map from an iterable of key/value pairs (e.g.
`dict(zip(keys, values))`). Later duplicate keys overwrite earlier ones, matching Python. -/
def pyDict {α β γ : Type} [PyIterable γ (α × β)] [BEq α] [Hashable α] (pairs : γ) :
    Std.HashMap α β :=
  Std.HashMap.ofList (pyIter pairs)

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

/--
For `dict.pop(key, default)`, return the value associated with the key (or the
default if missing) together with the updated map.
-/
def pyDictPop [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : Option β := none) : (Option β × Std.HashMap α β) :=
  match m.get? key with
  | some value => (some value, m.erase key)
  | none => (default, m)

def pyDictUpdate [BEq α] [Hashable α] (m : Std.HashMap α β) (updates : List (α × β)) : Std.HashMap α β :=
  updates.foldl (fun acc (k, v) => acc.insert k v) m

/-- Public runtime surface for Python `update()`. -/
def pyUpdate [BEq α] [Hashable α] (m : Std.HashMap α β) (updates : List (α × β)) : Std.HashMap α β :=
  pyDictUpdate m updates


/--
Optional form of `dict.get(key)`.

When the key is missing and no default is supplied, Python returns `None`, so the
natural Lean model is `Option β`.
-/
def pyDictGetOpt? [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) : Option β :=
  match m.get? key with
  | some value => some value
  | none => none

/--
Defaulted form of `dict.get(key, default)`.

When a default is supplied, Python returns a plain value, not an optional wrapper.
-/
def pyDictGetD [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : β) : β :=
  match m.get? key with
  | some value => value
  | none => default

/-- Public runtime surface for Python `get(key)`. -/
def pyGetOpt? [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) : Option β :=
  pyDictGetOpt? m key

/-- Public runtime surface for Python `get(key, default)`. -/
def pyGetD [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (default : β) : β :=
  pyDictGetD m key default


theorem pyDict_length_eq_items_length [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α](m : Std.HashMap α β) :
  m.size = (pyItems m).length := by
    simp [pyItems,pyDictItems, Std.HashMap.length_toList]

theorem pyDict_keys_length_eq_items_length [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α](m : Std.HashMap α β) :
  (pyKeys m).length = (pyItems m).length := by
    simp [pyKeys,pyItems, pyDictItems, Std.HashMap.length_toList, pyDictKeys]

theorem pyDict_values_length_eq_items_length [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α](m : Std.HashMap α β) :
  (pyValues m).length = (pyItems m).length := by
    simp [pyValues, pyItems, pyDictItems, Std.HashMap.length_toList, pyDictValues]

theorem pyDict_keys_length_eq_values_length [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α](m : Std.HashMap α β) :
  (pyKeys m).length = (pyValues m).length := by
    simp [pyDict_keys_length_eq_items_length, pyDict_values_length_eq_items_length]

#eval do
  let myMap : Std.HashMap String Nat := {}

  -- Inserting values
  let updatedMap := myMap.insert "apple" 1
  let updatedMap2 := updatedMap.insert "banana" 2
  pyDictGetOpt? updatedMap2 "apple" -- some 1

--   pyItems updatedMap2 -- [("apple", 1), ("banana", 2)]

-- #check List.length_foldr_permutationsAux2

end PastaLean
