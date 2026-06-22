import PastaLean
import Libraries

open PastaLean
open Libraries

set_option linter.all false

/-
A small numeric-toolkit showcase: `typing` annotations + a `scipy` subset, all transpiled
to Lean 4 and backed only by Mathlib (computable Float implementations).
-/
def variance := fun (xs : List Rat) ↦
  Id.run
    (do
      let mut m := Libraries.scipy.pyScipyTmean xs
      let mut total := (0.0 : Rat)
      for x in (PastaLean.pyIter xs)do
        total := total +ₚ (x -ₚ m) *ₚ (x -ₚ m)
      let __py_ret_1 := total /ₚ PastaLean.pyLen xs
      return __py_ret_1)

def variance'rn := fun (xs : List Float) ↦
  Id.run
    (do
      let mut m := Libraries.scipy.pyScipyTmean xs
      let mut total := (0.0 : Float)
      for x in (PastaLean.pyIter xs)do
        total := total +ₚ (x -ₚ m) *ₚ (x -ₚ m)
      let __py_ret_1 := total /ₚ PastaLean.pyLen xs
      return __py_ret_1)

noncomputable def main' :=
  ((do
      let mut data :=
        [(2.0 : Rat), (4.0 : Rat), (4.0 : Rat), (4.0 : Rat), (5.0 : Rat), (5.0 : Rat), (7.0 : Rat), (9.0 : Rat)]
      let _ ← pyPrintNoop [pyPrintArg "=== scipy.special ==="]
      let _ ← pyPrintNoop [pyPrintArg "5!        =", pyPrintArg (Libraries.scipy.pyScipyFactorial (5 : Int))]
      let _ ← pyPrintNoop [pyPrintArg "C(8,3)    =", pyPrintArg (Libraries.scipy.pyScipyComb (8 : Int) (3 : Int))]
      let _ ← pyPrintNoop [pyPrintArg "gamma(6)  =", pyPrintArg (Libraries.scipy.pyScipyGammaR (6.0 : Rat))]
      let _ ← pyPrintNoop [pyPrintArg "erf(1)    =", pyPrintArg (Libraries.scipy.pyScipyErf (1.0 : Rat))]
      let _ ← pyPrintNoop [pyPrintArg "=== scipy.constants ==="]
      let _ ← pyPrintNoop [pyPrintArg "pi        =", pyPrintArg Libraries.scipy.pyScipyPiR]
      let _ ← pyPrintNoop [pyPrintArg "golden    =", pyPrintArg Libraries.scipy.pyScipyGolden]
      let _ ← pyPrintNoop [pyPrintArg "=== scipy.stats ==="]
      let _ ← pyPrintNoop [pyPrintArg "mean      =", pyPrintArg (Libraries.scipy.pyScipyTmean data)]
      let _ ← pyPrintNoop [pyPrintArg "gmean     =", pyPrintArg (Libraries.scipy.pyScipyGmeanR data)]
      let _ ← pyPrintNoop [pyPrintArg "hmean     =", pyPrintArg (Libraries.scipy.pyScipyHmean data)]
      let _ ← pyPrintNoop [pyPrintArg "variance  =", pyPrintArg (variance data)]
      let _ ← pyPrintNoop [pyPrintArg "=== scipy.linalg ==="]
      let mut matrix := [[(4.0 : Rat), (3.0 : Rat)], [(6.0 : Rat), (3.0 : Rat)]]
      let _ ← pyPrintNoop [pyPrintArg "det       =", pyPrintArg (Libraries.scipy.pyScipyDet matrix)]
      let _ ←
        pyPrintNoop [pyPrintArg "norm[3,4] =", pyPrintArg (Libraries.scipy.pyScipyNormR [(3.0 : Rat), (4.0 : Rat)])]) :
    IO _)

def main''rn :=
  ((do
      let mut data :=
        [(2.0 : Float), (4.0 : Float), (4.0 : Float), (4.0 : Float), (5.0 : Float), (5.0 : Float), (7.0 : Float),
          (9.0 : Float)]
      let _ ← pyPrintIO [pyPrintArg "=== scipy.special ==="]
      let _ ← pyPrintIO [pyPrintArg "5!        =", pyPrintArg (Libraries.scipy.pyScipyFactorial (5 : Int))]
      let _ ← pyPrintIO [pyPrintArg "C(8,3)    =", pyPrintArg (Libraries.scipy.pyScipyComb (8 : Int) (3 : Int))]
      let _ ← pyPrintIO [pyPrintArg "gamma(6)  =", pyPrintArg (Libraries.scipy.pyScipyGamma (6.0 : Float))]
      let _ ← pyPrintIO [pyPrintArg "erf(1)    =", pyPrintArg (Libraries.scipy.pyScipyErf (1.0 : Float))]
      let _ ← pyPrintIO [pyPrintArg "=== scipy.constants ==="]
      let _ ← pyPrintIO [pyPrintArg "pi        =", pyPrintArg Libraries.scipy.pyScipyPi]
      let _ ← pyPrintIO [pyPrintArg "golden    =", pyPrintArg Libraries.scipy.pyScipyGolden]
      let _ ← pyPrintIO [pyPrintArg "=== scipy.stats ==="]
      let _ ← pyPrintIO [pyPrintArg "mean      =", pyPrintArg (Libraries.scipy.pyScipyTmean data)]
      let _ ← pyPrintIO [pyPrintArg "gmean     =", pyPrintArg (Libraries.scipy.pyScipyGmean data)]
      let _ ← pyPrintIO [pyPrintArg "hmean     =", pyPrintArg (Libraries.scipy.pyScipyHmean data)]
      let _ ← pyPrintIO [pyPrintArg "variance  =", pyPrintArg (variance'rn data)]
      let _ ← pyPrintIO [pyPrintArg "=== scipy.linalg ==="]
      let mut matrix := [[(4.0 : Float), (3.0 : Float)], [(6.0 : Float), (3.0 : Float)]]
      let _ ← pyPrintIO [pyPrintArg "det       =", pyPrintArg (Libraries.scipy.pyScipyDet matrix)]
      let _ ←
        pyPrintIO [pyPrintArg "norm[3,4] =", pyPrintArg (Libraries.scipy.pyScipyNorm [(3.0 : Float), (4.0 : Float)])]) :
    IO _)

noncomputable def main : IO Unit := do
  let _ ← main'
  pure ()

def main'rn : IO Unit := do
  let _ ← main''rn
  pure ()
