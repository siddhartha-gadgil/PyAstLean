import Mathlib
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.TasteIngr


namespace PastaLean

/-!
# Range lemmas for contract verification

`pyRange n` (Python `range(n)`) is `[0, 1, …, n-1]` as `Int`. These lemmas expose its structure to
`taste?`/`grind` for loop-invariant maintenance over `for i in range(n)` loops.

* `pyRange_eq` rewrites `pyRange n` to a `List.range` form (so grind sees the enumeration).
* `pyRange_split` is the "element = index" fact a loop maintenance step needs when the invariant
  references the loop index (e.g. `s = i*i`).
-/


@[taste_ingr] theorem pyRange_eq (n : Int) :
    pyRange n = (List.range n.toNat).map (fun i => (i : Int)) := by
  unfold pyRange; simp [List.range_eq_range']

theorem pyRange_elem_aux {m : Nat} {pref suff : List Int} {cur : Int}
    (h : (List.range m).map Int.ofNat = pref ++ cur :: suff) : cur = (pref.length : Int) := by
  have hlen := congrArg List.length h
  simp at hlen
  have key := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_map, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero] at key
  rw [List.getElem?_eq_getElem (show pref.length < (List.range m).length by simp; omega),
      List.getElem_range] at key
  simp at key; omega

theorem pyRange_split {m : Nat} {pref suff : List Int} {cur : Int}
    (h : List.flatMap (fun a => [(↑a : Int)]) (List.range m) = pref ++ cur :: suff) :
    cur = (pref.length : Int) := by
  apply pyRange_elem_aux (m := m)
  rw [← h]; simp [List.map_eq_flatMap]


end PastaLean
