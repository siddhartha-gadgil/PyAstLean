import PyAstLean
import Libraries

open PyAstLean
open Libraries

def sigmoid := fun (x : Float) ↦ (1.0 : Float) /ₚ ((1.0 : Float) +ₚ Libraries.math.pyMathExp (-x))

def predict := fun (x : List Float) ↦ fun (w1 : List (List Float)) ↦ fun (b1 : List Float) ↦
  fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  -- Forward pass through a 2 -> 2 -> 1 network.
  let h0 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
  let h1 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
  let hidden := [h0, h1]
  sigmoid (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)

def mean_squared_error := fun (xs : List (List Float)) ↦ fun (ys : List Float) ↦ fun (w1 : List (List Float)) ↦
  fun (b1 : List Float) ↦ fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  Id.run
    (do
      let mut total := (0.0 : Float)
      for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
        let mut diff := predict xs⦋i⦌ w1 b1 w2 b2 -ₚ ys⦋i⦌
        total := total +ₚ diff *ₚ diff
      let __py_ret := total /ₚ PyAstLean.pyLen xs
      return __py_ret)

def main' :=
  ((do
      -- XOR is not linearly separable, so a single layer cannot solve it -- the
      -- hidden layer is what makes this learnable.
      let mut xs :=
        [[(0.0 : Float), (0.0 : Float)], [(0.0 : Float), (1.0 : Float)], [(1.0 : Float), (0.0 : Float)],
          [(1.0 : Float), (1.0 : Float)]]
      let mut ys := [(0.0 : Float), (1.0 : Float), (1.0 : Float), (0.0 : Float)]
      -- Fixed initial weights so the run is reproducible (no RNG needed).
      let mut w1 := [[(0.5 : Float), -(0.4 : Float)], [(0.9 : Float), (1.0 : Float)]]
      let mut b1 := [(0.1 : Float), -(0.2 : Float)]
      let mut w2 := [[(0.7 : Float), -(0.8 : Float)]]
      let mut b2 := [(0.3 : Float)]
      let mut lr := (0.5 : Float)
      let mut epochs := (4000 : Int)
      let _ ← pyPrintIO [pyPrintArg "=== Training a neural net on XOR (NumPy + math) ==="]
      let _ ← pyPrintIO [pyPrintArg s! "initial loss: {mean_squared_error xs ys w1 b1 w2 b2}"]
      for epoch in (PyAstLean.pyRange epochs)do
        for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
          let mut x := xs⦋i⦌
          let mut y := ys⦋i⦌
          -- Forward pass, keeping the hidden activations for backprop.
          let mut h0 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
          let mut h1 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
          let mut hidden := [h0, h1]
          let mut out := sigmoid (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)
          -- Backward pass: gradients of 1/2 the squared error.
          let mut d_out := (out -ₚ y) *ₚ out *ₚ ((1.0 : Float) -ₚ out)
          let mut d_h0 := d_out *ₚ w2⦋(0 : Int)⦌⦋(0 : Int)⦌ *ₚ h0 *ₚ ((1.0 : Float) -ₚ h0)
          let mut d_h1 := d_out *ₚ w2⦋(0 : Int)⦌⦋(1 : Int)⦌ *ₚ h1 *ₚ ((1.0 : Float) -ₚ h1)
          -- Gradient-descent step (rebuild each weight row in place).
          w2 :=
            PyAstLean.pySetItem w2 (0 : Int)
              [w2⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h0, w2⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h1]
          b2 := [b2⦋(0 : Int)⦌ -ₚ lr *ₚ d_out]
          w1 :=
            PyAstLean.pySetItem w1 (0 : Int)
              [w1⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(0 : Int)⦌,
                w1⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(1 : Int)⦌]
          w1 :=
            PyAstLean.pySetItem w1 (1 : Int)
              [w1⦋(1 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(0 : Int)⦌,
                w1⦋(1 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(1 : Int)⦌]
          b1 := [b1⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0, b1⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1]
        if (epoch +ₚ (1 : Int)) %ₚ (1000 : Int) == (0 : Int) then 
          let _ ← pyPrintIO [pyPrintArg s!"epoch {(epoch +ₚ (1 : Int))}: loss = {mean_squared_error xs ys w1 b1 w2 b2}"]
        else
          let _ := ()
      let _ ← pyPrintIO [pyPrintArg "learned predictions:"]
      for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
        let mut p := predict xs⦋i⦌ w1 b1 w2 b2
        let mut label := if decide (p > (0.5 : Float)) then (1 : Int) else (0 : Int)
        let _ ← pyPrintIO [pyPrintArg s! "  {xs⦋i⦌} -> {p }  (class {label }, target {PyAstLean.pyInt ys⦋i⦌})"]) :
    IO _)

def main : IO Unit := do
  let _ ← main'
  pure ()
