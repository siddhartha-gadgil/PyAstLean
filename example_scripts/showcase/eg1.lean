import PyAstLean
import Libraries

open PyAstLean
open Libraries

def euclidean_distance : List Int → List Int → PyAstLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if PyAstLean.pyLen p1 != PyAstLean.pyLen p2 then 
    throw
        (PyAstLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    (PyAstLean.pyIter (PyAstLean.pyZip p1 p2)).map fun _pair =>
      let a := Prod.fst _pair;
      let b := Prod.snd _pair;
      Libraries.math.pyMathPow (a -ₚ b) (2 : Int)
  let __py_ret := Libraries.math.pyMathSqrt (PyAstLean.pySum sq_diffs)
  return __py_ret

def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  ((do
      try
        do
          let __py_try_val ←
            PyAstLean.PyExcept.captureIOErrors
                (do
                  do
                    -- Calculate distances using list comprehension
                    let mut distances :=
                      (← (PyAstLean.pyIter dataset).mapM fun point => euclidean_distance target point)
                    -- Find the minimum distance
                    let mut min_dist := PyAstLean.pyMin distances
                    -- Find the index of the minimum distance
                    -- Using a loop since index() might not be supported based on tests
                    let mut min_index := -(1 : Int)
                    for _pair in (PyAstLean.pyIter (PyAstLean.pyEnumerate distances))do
                      let i := Prod.fst _pair
                      let d := Prod.snd _pair
                      if d == min_dist then 
                        min_index := i
                        break
                      else
                        let _ := ()
                    let __py_ret := (min_dist, dataset⦋min_index⦌)
                    return __py_ret)
          return __py_try_val
      catch caught =>
        if (caught).OfKind == "ValueError" then 
          do
            let e := caught
            let _ ← pyPrintIO [pyPrintArg s! "Error calculating distances: {e}"]
            let __py_ret_1 := (-(1.0 : Float), [])
            return __py_ret_1
        else
          throw caught) :
    PyAstLean.PyExcept _)

def run_example :=
  ((do
      let mut dataset :=
        [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)], [(7 : Int), (8 : Int), (9 : Int)],
          [(2 : Int), (1 : Int), (4 : Int)]]
      let mut target_point := [(2 : Int), (3 : Int), (4 : Int)]
      let mut invalid_point := [(1 : Int), (2 : Int)]
      let _ ← pyPrintIO [pyPrintArg "Dataset:", pyPrintArg dataset]
      let _ ← pyPrintIO [pyPrintArg "Target Point:", pyPrintArg target_point]
      -- Valid Case
      let __unpack_value ← find_nearest_neighbor target_point dataset
      let __unpack_pair := __unpack_value
      let mut dist := Prod.fst __unpack_pair
      let mut nearest := Prod.snd __unpack_pair
      let _ ← pyPrintIO [pyPrintArg "Nearest Neighbor to Target:"]
      let _ ← pyPrintIO [pyPrintArg "Point:", pyPrintArg nearest]
      let _ ← pyPrintIO [pyPrintArg "Distance:", pyPrintArg dist]
      -- Invalid Case
      let _ ← pyPrintIO [pyPrintArg "\nTesting Invalid Point:"]
      let __unpack_value_1 ← find_nearest_neighbor invalid_point dataset
      let __unpack_pair_1 := __unpack_value_1
      let mut dist_inv := Prod.fst __unpack_pair_1
      let mut nearest_inv := Prod.snd __unpack_pair_1
      let _ ← pyPrintIO [pyPrintArg "Fallback Distance:", pyPrintArg dist_inv]) :
    PyAstLean.PyExcept _)

def main : IO Unit := do
  let result ←
    (((do
            let _ ← run_example
            pure ()) :
          PyAstLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))
