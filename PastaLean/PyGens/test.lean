import PastaLean
import Libraries

open PastaLean
open Libraries

noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  (do
      if h: PastaLean.pyLen p1 != PastaLean.pyLen p2 then
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString "Points must have the same number of dimensions"))
      else
        let _ := ()
      have hpq : PastaLean.pyLen p1 == PastaLean.pyLen p2 := by
        sorry
  )
