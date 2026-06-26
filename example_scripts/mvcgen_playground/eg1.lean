import Mathlib
import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

abbrev PyExceptId (α : Type) := ExceptT PyException Id α

def massert (_p : Prop) : PyExceptId Unit := pure ()

@[spec]
theorem assertM_spec (p : Prop) :
  ⦃⌜p⌝⦄ (massert p) ⦃⇓ _ => ⌜p⌝⦄ := by
  mvcgen [massert]

@[spec]
theorem List.mapM_spec {α β : Type} (f : α → PyExceptId β) (xs : List α)
    (P : α → Prop) (Q : α → β → Prop) (E : α → PastaLean.PyException → Prop) :
  (∀ x ∈ xs, ⦃⌜P x⌝⦄ f x ⦃post⟨fun y => ⌜Q x y⌝, fun e => ⌜E x e⌝⟩⦄) →
  ⦃⌜∀ x ∈ xs, P x⌝⦄
  xs.mapM f
  ⦃post⟨fun ys => ⌜xs.length = ys.length ∧ ∀ x ∈ xs, ∃ y ∈ ys, Q x y⌝,
        fun e => ⌜∃ x ∈ xs, E x e⌝⟩⦄ := by
  intro hspec
  induction xs with
  | nil =>
    simp [List.mapM]
    mvcgen
  | cons x xs ih =>
    simp [List.mapM]
    mvcgen
    all_goals sorry

noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  ((do
      if PastaLean.pyLen p1 ≠ PastaLean.pyLen p2 then
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString "Points must have the same number of dimensions"))
      -- Using zip, list comprehension, and math.pow
      massert (PastaLean.pyLen p1 = PastaLean.pyLen p2)
      let mut sq_diffs :=
        (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
          let a := Prod.fst _pair_1;
          let b := Prod.snd _pair_1;
          Libraries.math.pyMathPowExact (a -ₚ b) (2 : Int)
      let __py_ret_1 := Libraries.math.pyMathSqrtR (PastaLean.pySum sq_diffs)
      return __py_ret_1
    ) :
    PyExceptId _)

theorem euclidean_distance_asserts : ⦃⌜ True ⌝⦄ euclidean_distance l1 l2 ⦃post⟨fun _ => ⌜ pyLen l1 = pyLen l2 ⌝, fun _ => ⌜ pyLen l1 ≠ pyLen l2 ⌝⟩⦄ := by
  mvcgen [euclidean_distance] with grind

theorem euclidean_distance_same_len_no_throw : ⦃⌜ pyLen l1 = pyLen l2 ⌝⦄ euclidean_distance l1 l2 ⦃post⟨fun _ => ⌜ True ⌝, fun _ => ⌜ False ⌝⟩⦄ := by
  mvcgen [euclidean_distance] with grind

noncomputable def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  ((do
      try
        -- Calculate distances using list comprehension
        let mut distances := (← (PastaLean.pyIter dataset).mapM fun point => euclidean_distance target point)
        let mut min_dist := PastaLean.pyMin distances
        massert (∀ d ∈ distances, min_dist ≤ d ∧ ∃ d ∈ distances, min_dist = d)
        -- Find the index of the minimum distance
        -- Using a loop since index() might not be supported based on tests
        let mut min_index := -(1 : Int)
        for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances))do
          let i := Prod.fst _pair_1
          let d := Prod.snd _pair_1
          if h_1 : d == min_dist then
            min_index := i
            break
          else
            let _ := ()
        let __py_ret_1 := (min_dist, dataset⦋min_index⦌)
        return __py_ret_1
      catch caught =>
        if (caught).OfKind == "ValueError" then
          let __py_ret_2 := (-(1.0 : Real), [])
          return __py_ret_2
        else
          throw caught) :
    PyExceptId _)

@[grind .]
theorem pyMin_le_all : ∀ x ∈ (xs : List ℝ), PastaLean.pyMin xs ≤ x ∧ PastaLean.pyMin xs ∈ xs := by
  simp [PastaLean.pyMin, PastaLean.pyIter]
  sorry


-- New theorems about euclidean_distance

-- Euclidean distance is non-negative
theorem euclidean_distance_nonneg :
  ⦃⌜ p1.length = p2.length ⌝⦄
  euclidean_distance p1 p2
  ⦃⇓ d => ⌜ d ≥ 0 ⌝⦄ := by
  sorry


-- Euclidean distance is zero iff points are equal
theorem euclidean_distance_zero_iff_equal :
  ⦃⌜ p1.length = p2.length ⌝⦄
  euclidean_distance p1 p2
  ⦃⇓ d => ⌜ (d = 0 ↔ p1 = p2) ⌝⦄ := by
  sorry

-- Euclidean distance is symmetric
theorem euclidean_distance_symmetric :
  ⦃⌜ p1.length = p2.length ⌝⦄
  (do let d1 ← euclidean_distance p1 p2; let d2 ← euclidean_distance p2 p1; return (d1, d2))
  ⦃⇓ (d1, d2) => ⌜ d1 = d2 ⌝⦄ := by
  sorry

-- Triangle inequality for euclidean distance
theorem euclidean_distance_triangle :
  ⦃⌜ p1.length = p2.length ∧ p2.length = p3.length ⌝⦄
  (do
    let d12 ← euclidean_distance p1 p2
    let d23 ← euclidean_distance p2 p3
    let d13 ← euclidean_distance p1 p3
    return (d12, d23, d13))
  ⦃⇓ (d12, d23, d13) => ⌜ d13 ≤ d12 + d23 ⌝⦄ := by
  sorry

-- New theorems about find_nearest_neighbor

-- If dataset is non-empty and all same dimension as target, returns a valid point
theorem find_nearest_neighbor_returns_dataset_point :
  ⦃⌜ dataset ≠ [] ∧ ∀ p ∈ dataset, p.length = target.length ⌝⦄
  find_nearest_neighbor target dataset
  ⦃⇓ (dist, nearest) => ⌜ nearest ∈ dataset ∧ dist ≥ 0 ⌝⦄ := by
  sorry

-- The returned distance is minimal among all dataset points
theorem find_nearest_neighbor_is_minimal :
  ⦃⌜ dataset ≠ [] ∧ ∀ p ∈ dataset, p.length = target.length ⌝⦄
  (do
    let (min_dist, nearest) ← find_nearest_neighbor target dataset
    let all_dists ← dataset.mapM (euclidean_distance target)
    return (min_dist, all_dists))
  ⦃⇓ (min_dist, all_dists) => ⌜ ∀ d ∈ all_dists, min_dist ≤ d ⌝⦄ := by
  sorry

-- Empty dataset returns the fallback value
theorem find_nearest_neighbor_empty_fallback :
  ⦃⌜ dataset = [] ⌝⦄
  find_nearest_neighbor target dataset
  ⦃⇓ (dist, nearest) => ⌜ dist = -1.0 ∧ nearest = [] ⌝⦄ := by
  sorry

-- Mixed dimensions trigger fallback
theorem find_nearest_neighbor_mixed_dimensions :
  ⦃⌜ ∃ p ∈ dataset, p.length ≠ target.length ⌝⦄
  find_nearest_neighbor target dataset
  ⦃⇓ (dist, nearest) => ⌜ dist = -1.0 ∧ nearest = [] ⌝⦄ := by
  sorry

-- Single element dataset returns that element
theorem find_nearest_neighbor_singleton :
  ⦃⌜ dataset = [p] ∧ p.length = target.length ⌝⦄
  find_nearest_neighbor target dataset
  ⦃⇓ (dist, nearest) => ⌜ nearest = p ⌝⦄ := by
  sorry

-- The nearest point's distance equals the returned distance
theorem find_nearest_neighbor_distance_consistent :
  ⦃⌜ dataset ≠ [] ∧ ∀ p ∈ dataset, p.length = target.length ⌝⦄
  (do
    let (min_dist, nearest) ← find_nearest_neighbor target dataset
    let actual_dist ← euclidean_distance target nearest
    return (min_dist, actual_dist))
  ⦃⇓ (min_dist, actual_dist) => ⌜ min_dist = actual_dist ⌝⦄ := by
  sorry

-- noncomputable def run_example :=
--   ((do
--       let mut dataset :=
--         [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)], [(7 : Int), (8 : Int), (9 : Int)],
--           [(2 : Int), (1 : Int), (4 : Int)]]
--       let mut target_point := [(2 : Int), (3 : Int), (4 : Int)]
--       let mut invalid_point := [(1 : Int), (2 : Int)]
--       -- Valid Case
--       let __unpack_value_1 ← find_nearest_neighbor target_point dataset
--       let __unpack_pair_1 := __unpack_value_1
--       let mut dist := Prod.fst __unpack_pair_1
--       let mut nearest := Prod.snd __unpack_pair_1
--       let _ ← pyPrintNoop [pyPrintArg "Nearest Neighbor to Target:"]
--       let _ ← pyPrintNoop [pyPrintArg "Point:", pyPrintArg nearest]
--       let _ ← pyPrintNoop [pyPrintArg "Distance:", pyPrintArg dist]
--       -- Invalid Case
--       let _ ← pyPrintNoop [pyPrintArg "\nTesting Invalid Point:"]
--       let __unpack_value_2 ← find_nearest_neighbor invalid_point dataset
--       let __unpack_pair_2 := __unpack_value_2
--       let mut dist_inv := Prod.fst __unpack_pair_2
--       let mut nearest_inv := Prod.snd __unpack_pair_2
--       let _ ← pyPrintNoop [pyPrintArg "Fallback Distance:", pyPrintArg dist_inv]) :
--     PyExceptId _)

-- noncomputable def main : IO Unit := do
--   let result ←
--     (((do
--             let _ ← run_example
--             pure ()) :
--           PyExceptId Unit)).run
--   match result with
--   | .ok _ =>
--     pure ()
--   | .error err =>
--     throw (IO.userError (toString err))

-- def main'rn : IO Unit := do
--   let result ←
--     (((do
--             let _ ← run_example'rn
--             pure ()) :
--           PyExceptId Unit)).run
--   match result with
--   | .ok _ =>
--     pure ()
--   | .error err =>
--     throw (IO.userError (toString err))
