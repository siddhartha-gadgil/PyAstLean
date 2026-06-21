import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def l :=
  (PyAstLean.pyIter [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)]]).flatMap fun l =>
    (PyAstLean.pyIter l).flatMap fun x => (PyAstLean.pyIter l).map fun y => x *ₚ y
