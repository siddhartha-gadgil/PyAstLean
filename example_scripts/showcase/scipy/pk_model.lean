import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
/-
A pharmacokinetic (PK) drug-concentration simulator -- the dynamical core PyAstLean
transpiles to Lean 4.

Classic two-compartment model with first-order oral absorption and repeated dosing:

    Gut depot  D  --ka-->  Plasma  C  --ke--> (eliminated)
                           C  <--k21-- / --k12-->  Tissue  P

The ODE right-hand sides and the derived quantities each live in their own function; `main`
only reads the parameters from stdin, administers doses, and steps the integrator. A fixed dose
is dropped into the gut every `dose_step` steps, so plasma concentration climbs with each dose,
converges to a steady state, then washes out -- the textbook drug-accumulation curve.

Run directly it uses real SciPy; transpiled by PyAstLean it uses the Mathlib-only `Libraries.scipy`
shim. The showcase runs both and overlays the Python and Lean trajectories.
-/
def depot_rate := fun (ka : Rat) ↦ fun (depot : Rat) ↦
  /-
  dD/dt -- drug leaving the gut depot by absorption.
  -/
  -ka *ₚ depot

def depot_rate'rn := fun (ka : Float) ↦ fun (depot : Float) ↦
  /-
  dD/dt -- drug leaving the gut depot by absorption.
  -/
  -ka *ₚ depot

def central_rate := fun (ka : Rat) ↦ fun (ke : Rat) ↦ fun (k12 : Rat) ↦ fun (k21 : Rat) ↦ fun (depot : Rat) ↦
  fun (central : Rat) ↦ fun (periph : Rat) ↦
  /-
  dC/dt -- absorption in, elimination out, exchange with the peripheral compartment.
  -/
  ka *ₚ depot -ₚ ke *ₚ central -ₚ k12 *ₚ central +ₚ k21 *ₚ periph

def central_rate'rn := fun (ka : Float) ↦ fun (ke : Float) ↦ fun (k12 : Float) ↦ fun (k21 : Float) ↦
  fun (depot : Float) ↦ fun (central : Float) ↦ fun (periph : Float) ↦
  /-
  dC/dt -- absorption in, elimination out, exchange with the peripheral compartment.
  -/
  ka *ₚ depot -ₚ ke *ₚ central -ₚ k12 *ₚ central +ₚ k21 *ₚ periph

def periph_rate := fun (k12 : Rat) ↦ fun (k21 : Rat) ↦ fun (central : Rat) ↦ fun (periph : Rat) ↦
  /-
  dP/dt -- distribution into and back out of the tissue compartment.
  -/
  k12 *ₚ central -ₚ k21 *ₚ periph

def periph_rate'rn := fun (k12 : Float) ↦ fun (k21 : Float) ↦ fun (central : Float) ↦ fun (periph : Float) ↦
  /-
  dP/dt -- distribution into and back out of the tissue compartment.
  -/
  k12 *ₚ central -ₚ k21 *ₚ periph

def concentration := fun (amount : Rat) ↦ fun (vol : Rat) ↦
  /-
  Convert a compartment amount (mg) to a concentration (mg/L).
  -/
  amount /ₚ vol

def concentration'rn := fun (amount : Float) ↦ fun (vol : Float) ↦
  /-
  Convert a compartment amount (mg) to a concentration (mg/L).
  -/
  amount /ₚ vol

noncomputable def body_load := fun (depot : Rat) ↦ fun (central : Rat) ↦ fun (periph : Rat) ↦
  /-
  Total body drug load as the Euclidean norm of the compartment vector (via scipy).
  -/
  Libraries.scipy.pyScipyNormR [depot, central, periph]

def body_load'rn := fun (depot : Float) ↦ fun (central : Float) ↦ fun (periph : Float) ↦
  /-
  Total body drug load as the Euclidean norm of the compartment vector (via scipy).
  -/
  Libraries.scipy.pyScipyNorm [depot, central, periph]

noncomputable def main' :=
  ((do
      let mut ka := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut ke := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut k12 := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut k21 := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut vol := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut dose := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut dt := PyAstLean.pyRat (← PyAstLean.pyInputIO "")
      let mut dose_step := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut ndoses := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut nsteps := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut every := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut depot := (0.0 : Rat)
      let mut central := (0.0 : Rat)
      let mut periph := (0.0 : Rat)
      let mut t := (0.0 : Rat)
      let mut dose_num := (0 : Int)
      for step in (PyAstLean.pyRange nsteps)do
        -- Administer a dose into the gut depot when one is due.
        if step %ₚ dose_step == (0 : Int) then 
          if decide (dose_num < ndoses) then 
            depot := depot +ₚ dose
            dose_num := dose_num +ₚ (1 : Int)
          else
            let _ := ()
        else
          let _ := ()
        -- One forward-Euler step using the rate functions.
        let mut d_depot := depot_rate ka depot
        let mut d_central := central_rate ka ke k12 k21 depot central periph
        let mut d_periph := periph_rate k12 k21 central periph
        depot := depot +ₚ d_depot *ₚ dt
        central := central +ₚ d_central *ₚ dt
        periph := periph +ₚ d_periph *ₚ dt
        t := t +ₚ dt
        if step %ₚ every == (0 : Int) then 
          let _ ← pyPrintNoop
        else
          let _ := ()) :
    IO _)

def main''rn :=
  ((do
      let mut ka := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut ke := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut k12 := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut k21 := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut vol := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut dose := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut dt := PyAstLean.pyFloat (← PyAstLean.pyInputIO "")
      let mut dose_step := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut ndoses := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut nsteps := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut every := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
      let mut depot := (0.0 : Float)
      let mut central := (0.0 : Float)
      let mut periph := (0.0 : Float)
      let mut t := (0.0 : Float)
      let mut dose_num := (0 : Int)
      for step in (PyAstLean.pyRange nsteps)do
        -- Administer a dose into the gut depot when one is due.
        if step %ₚ dose_step == (0 : Int) then 
          if decide (dose_num < ndoses) then 
            depot := depot +ₚ dose
            dose_num := dose_num +ₚ (1 : Int)
          else
            let _ := ()
        else
          let _ := ()
        -- One forward-Euler step using the rate functions.
        let mut d_depot := depot_rate'rn ka depot
        let mut d_central := central_rate'rn ka ke k12 k21 depot central periph
        let mut d_periph := periph_rate'rn k12 k21 central periph
        depot := depot +ₚ d_depot *ₚ dt
        central := central +ₚ d_central *ₚ dt
        periph := periph +ₚ d_periph *ₚ dt
        t := t +ₚ dt
        if step %ₚ every == (0 : Int) then 
          let _ ←
            pyPrintIO
                [pyPrintArg "S", pyPrintArg step, pyPrintArg t, pyPrintArg (concentration'rn central vol),
                  pyPrintArg (concentration'rn periph vol), pyPrintArg depot,
                  pyPrintArg (body_load'rn depot central periph)]
        else
          let _ := ()) :
    IO _)

noncomputable def main : IO Unit := do
  let _ ← main'
  pure ()

def main'rn : IO Unit := do
  let _ ← main''rn
  pure ()
