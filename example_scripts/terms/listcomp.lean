import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def l :=
  (PastaLean.pyIter [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)]]).flatMap fun l =>
    (PastaLean.pyIter l).flatMap fun x => (PastaLean.pyIter l).map fun y => x *ₚ y
