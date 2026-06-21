import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def process_data := fun (data : List (List Rat)) ↦ fun (weights : List (List Rat)) ↦
  ((do
      try
        let __py_try_val ←
          PastaLean.PyExcept.captureIOErrors
              (do
                -- Calculate mean of the dataset
                let mut m := Libraries.numpy.pyNumpyMean data
                let _ ← pyPrintNoop
                -- Center the data by subtracting the mean
                -- (Using a manual broadcast-like subtraction for this example)
                -- Note: np.subtract is mapped to pyNumpySubtract
                let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
                -- Perform matrix multiplication
                -- Note: np.matmul is mapped to pyNumpyMatmul
                let mut result := Libraries.numpy.pyNumpyMatmul centered weights
                return result)
        return __py_try_val
      catch caught =>
        if (caught).OfKind == "ValueError" then
          let e := caught
          let _ ← pyPrintNoop
          -- Fallback to a zero matrix if dimensions fail
          let __py_ret := Libraries.numpy.pyNumpyZeros ((2 : Int), (2 : Int))
          return __py_ret
        else
          throw caught) :
    PastaLean.PyExcept _)

def process_data'rn : List (List Float) → List (List Float) → PastaLean.PyExcept (List (List Float)) :=
  fun (data : List (List Float)) ↦ fun (weights : List (List Float)) ↦ do
  try
    let __py_try_val ←
      PastaLean.PyExcept.captureIOErrors
          (do
            -- Calculate mean of the dataset
            let mut m := Libraries.numpy.pyNumpyMean data
            let _ ← pyPrintIO [pyPrintArg s! "Dataset Global Mean: {m}"]
            -- Center the data by subtracting the mean
            -- (Using a manual broadcast-like subtraction for this example)
            -- Note: np.subtract is mapped to pyNumpySubtract
            let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
            -- Perform matrix multiplication
            -- Note: np.matmul is mapped to pyNumpyMatmul
            let mut result := Libraries.numpy.pyNumpyMatmul centered weights
            return result)
    return __py_try_val
  catch caught =>
    if (caught).OfKind == "ValueError" then
      let e := caught
      let _ ← pyPrintIO [pyPrintArg s! "Processing failed: {e}"]
      -- Fallback to a zero matrix if dimensions fail
      let __py_ret := Libraries.numpy.pyNumpyZeros ((2 : Int), (2 : Int))
      return __py_ret
    else
      throw caught

def run_example :=
  ((do
      -- Define a 2x2 dataset and a 2x2 weight matrix
      let mut dataset := [[(1.0 : Rat), (2.0 : Rat)], [(3.0 : Rat), (4.0 : Rat)]]
      let mut weights := [[(0.5 : Rat), (0.5 : Rat)], [(1.0 : Rat), (2.0 : Rat)]]
      let _ ← pyPrintNoop
      let _ ← pyPrintNoop
      let _ ← pyPrintNoop
      -- 1. Main Processing Pipeline
      let _ ← pyPrintNoop
      let mut output := (← process_data dataset weights)
      let _ ← pyPrintNoop
      -- 2. Utility Operations
      let _ ← pyPrintNoop
      let _ ← pyPrintNoop
      let _ ← pyPrintNoop
      let mut __py_unpack1 := Libraries.numpy.pyNumpyShape dataset
      let mut rows := __py_unpack1⦋(0 : Int)⦌
      let mut cols := __py_unpack1⦋(1 : Int)⦌
      let _ ← pyPrintNoop
      -- 4. Error Handling Simulation
      let _ ← pyPrintNoop
      let mut invalid_data := [[(1.0 : Rat), (2.0 : Rat), (3.0 : Rat)]]
      -- This should trigger the ValueError in np.matmul(1x3, 2x2)
      let _ ← process_data invalid_data weights) :
    PastaLean.PyExcept _)

def run_example'rn :=
  ((do
      -- Define a 2x2 dataset and a 2x2 weight matrix
      let mut dataset := [[(1.0 : Float), (2.0 : Float)], [(3.0 : Float), (4.0 : Float)]]
      let mut weights := [[(0.5 : Float), (0.5 : Float)], [(1.0 : Float), (2.0 : Float)]]
      let _ ← pyPrintIO [pyPrintArg "=== PastaLean NumPy Showcase ==="]
      let _ ← pyPrintIO [pyPrintArg s! "Input Data: {dataset}"]
      let _ ← pyPrintIO [pyPrintArg s! "Weight Matrix: {weights}"]
      -- 1. Main Processing Pipeline
      let _ ← pyPrintIO [pyPrintArg "\n[1] Running Data Pipeline:"]
      let mut output := (← process_data'rn dataset weights)
      let _ ← pyPrintIO [pyPrintArg s! "Final Result:\n{output}"]
      -- 2. Utility Operations
      let _ ← pyPrintIO [pyPrintArg "\n[2] Structural Operations:"]
      let _ ← pyPrintIO [pyPrintArg s! "Identity Matrix (2x2):\n{Libraries.numpy.pyNumpyEye (2 : Int)}"]
      let _ ← pyPrintIO [pyPrintArg s! "Flattened Weights: {Libraries.numpy.pyNumpyFlatten weights}"]
      let mut __py_unpack1 := Libraries.numpy.pyNumpyShape dataset
      let mut rows := __py_unpack1⦋(0 : Int)⦌
      let mut cols := __py_unpack1⦋(1 : Int)⦌
      let _ ← pyPrintIO [pyPrintArg s! "Dataset Shape: {rows }x{cols}"]
      -- 4. Error Handling Simulation
      let _ ← pyPrintIO [pyPrintArg "\n[3] Exception Handling (Mismatched Dimensions):"]
      let mut invalid_data := [[(1.0 : Float), (2.0 : Float), (3.0 : Float)]]
      -- This should trigger the ValueError in np.matmul(1x3, 2x2)
      let _ ← process_data'rn invalid_data weights) :
    PastaLean.PyExcept _)

def main : IO Unit := do
  let result ←
    (((do
            let _ ← run_example
            pure ()) :
          PastaLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let result ←
    (((do
            let _ ← run_example'rn
            pure ()) :
          PastaLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))
