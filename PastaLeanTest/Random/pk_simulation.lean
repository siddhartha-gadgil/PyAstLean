import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
noncomputable def main' :=
  ((do
      -- parameters for the 3-body system (grass, rabbits, wolves)
      -- grass growth rate
      let mut r := (1.2 : Rat)
      -- grass carrying capacity
      let mut k := (100.0 : Rat)
      -- rabbit consumption of grass
      let mut a := (0.1 : Rat)
      -- rabbit birth rate from grass
      let mut b := (0.05 : Rat)
      -- rabbit natural death rate
      let mut d := (0.4 : Rat)
      -- wolf consumption of rabbits
      let mut c := (0.1 : Rat)
      -- wolf birth rate from rabbits
      let mut e := (0.02 : Rat)
      -- wolf natural death rate
      let mut _f := (0.3 : Rat)
      let system := fun (state : List Rat) ↦ fun (t : Rat) ↦
        let __py_unpack1 := state
        let g := __py_unpack1⦋(0 : Int)⦌
        let r_pop := __py_unpack1⦋(1 : Int)⦌
        let w := __py_unpack1⦋(2 : Int)⦌
        -- grass dynamics: logistic growth minus eaten by rabbits
        let dgdt := r *ₚ g *ₚ ((1 : Int) -ₚ g /ₚ k) -ₚ a *ₚ g *ₚ r_pop
        -- rabbit dynamics: birth from grass minus death minus eaten by wolves
        let drdt := b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w
        -- wolf dynamics: birth from rabbits minus death
        let dwdt := e *ₚ r_pop *ₚ w -ₚ _f *ₚ w
        [dgdt, drdt, dwdt]
      -- initial conditions: 50 grass, 10 rabbits, 5 wolves
      let mut init_state := [(50.0 : Rat), (10.0 : Rat), (5.0 : Rat)]
      -- time points
      let mut t := Libraries.numpy.pyNumpyLinspace (0 : Int) (100 : Int) (5000 : Int)
      -- solve the ODE
      let mut solution := Libraries.scipy.pyScipyOdeint system init_state t
      -- extract results
      let mut grass := List.map (fun row => row⦋(0 : Int)⦌) solution
      let mut rabbits := List.map (fun row => row⦋(1 : Int)⦌) solution
      let mut wolves := List.map (fun row => row⦋(2 : Int)⦌) solution
      -- print some results in a messy way
      let _ ← pyPrintNoop
      let _ ← pyPrintNoop
      for i in (PastaLean.pyRange (5000 : Int) (0 : Int) (100 : Int))do
        -- bunching up printing and math
        let mut avg := (grass⦋i⦌ +ₚ rabbits⦋i⦌ +ₚ wolves⦋i⦌) /ₚ (3.0 : Rat)
        let mut entropy :=
          -(grass⦋i⦌ *ₚ Libraries.math.pyMathLogR (grass⦋i⦌ +ₚ (1 : Int)) +ₚ
                rabbits⦋i⦌ *ₚ Libraries.math.pyMathLogR (rabbits⦋i⦌ +ₚ (1 : Int)) +ₚ
              wolves⦋i⦌ *ₚ Libraries.math.pyMathLogR (wolves⦋i⦌ +ₚ (1 : Int)))
        let _ ← pyPrintNoop
      -- final check
      if decide (wolves⦋-1⦌ > (0.1 : Rat)) then
        let _ ← pyPrintNoop
      else
        let _ ← pyPrintNoop) :
    IO _)

def main''rn :=
  ((do
      -- parameters for the 3-body system (grass, rabbits, wolves)
      -- grass growth rate
      let mut r := (1.2 : Float)
      -- grass carrying capacity
      let mut k := (100.0 : Float)
      -- rabbit consumption of grass
      let mut a := (0.1 : Float)
      -- rabbit birth rate from grass
      let mut b := (0.05 : Float)
      -- rabbit natural death rate
      let mut d := (0.4 : Float)
      -- wolf consumption of rabbits
      let mut c := (0.1 : Float)
      -- wolf birth rate from rabbits
      let mut e := (0.02 : Float)
      -- wolf natural death rate
      let mut _f := (0.3 : Float)
      let system := fun (state : List Float) ↦ fun (t : Float) ↦
        let __py_unpack1 := state
        let g := __py_unpack1⦋(0 : Int)⦌
        let r_pop := __py_unpack1⦋(1 : Int)⦌
        let w := __py_unpack1⦋(2 : Int)⦌
        -- grass dynamics: logistic growth minus eaten by rabbits
        let dgdt := r *ₚ g *ₚ ((1 : Int) -ₚ g /ₚ k) -ₚ a *ₚ g *ₚ r_pop
        -- rabbit dynamics: birth from grass minus death minus eaten by wolves
        let drdt := b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w
        -- wolf dynamics: birth from rabbits minus death
        let dwdt := e *ₚ r_pop *ₚ w -ₚ _f *ₚ w
        [dgdt, drdt, dwdt]
      -- initial conditions: 50 grass, 10 rabbits, 5 wolves
      let mut init_state := [(50.0 : Float), (10.0 : Float), (5.0 : Float)]
      -- time points
      let mut t := Libraries.numpy.pyNumpyLinspace (0 : Int) (100 : Int) (5000 : Int)
      -- solve the ODE
      let mut solution := Libraries.scipy.pyScipyOdeint system init_state t
      -- extract results
      let mut grass := List.map (fun row => row⦋(0 : Int)⦌) solution
      let mut rabbits := List.map (fun row => row⦋(1 : Int)⦌) solution
      let mut wolves := List.map (fun row => row⦋(2 : Int)⦌) solution
      -- print some results in a messy way
      let _ ← pyPrintIO [pyPrintArg "Simulation results for 3-species system:"]
      let _ ← pyPrintIO [pyPrintArg "Time | Grass | Rabbits | Wolves"]
      for i in (PastaLean.pyRange (5000 : Int) (0 : Int) (100 : Int))do
        -- bunching up printing and math
        let mut avg := (grass⦋i⦌ +ₚ rabbits⦋i⦌ +ₚ wolves⦋i⦌) /ₚ (3.0 : Float)
        let mut entropy :=
          -(grass⦋i⦌ *ₚ Libraries.math.pyMathLog (grass⦋i⦌ +ₚ (1 : Int)) +ₚ
                rabbits⦋i⦌ *ₚ Libraries.math.pyMathLog (rabbits⦋i⦌ +ₚ (1 : Int)) +ₚ
              wolves⦋i⦌ *ₚ Libraries.math.pyMathLog (wolves⦋i⦌ +ₚ (1 : Int)))
        let _ ←
          pyPrintIO
              [pyPrintArg
                  s!"{(PastaLean.pyFormatSpec t⦋i⦌
                      ".1f")} | {(PastaLean.pyFormatSpec grass⦋i⦌
                      ".2f")} | {(PastaLean.pyFormatSpec rabbits⦋i⦌
                      ".2f")} | {(PastaLean.pyFormatSpec wolves⦋i⦌
                      ".2f")} | Avg: {(PastaLean.pyFormatSpec avg
                      ".2f")} | Messy Entropy: {PastaLean.pyFormatSpec entropy ".2f"}"]
      -- final check
      if decide (wolves⦋-1⦌ > (0.1 : Float)) then
        let _ ← pyPrintIO [pyPrintArg "The ecosystem survived!"]
      else
        let _ ← pyPrintIO [pyPrintArg "The wolves went extinct."]) :
    IO _)

noncomputable def main : IO Unit := do
  let _ ← main'
  pure ()

def main'rn : IO Unit := do
  let _ ← main''rn
  pure ()
