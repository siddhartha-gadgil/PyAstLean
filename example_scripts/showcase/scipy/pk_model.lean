import PastaLean
import Libraries

open PastaLean
open Libraries

set_option linter.all false
set_option maxHeartbeats 800000

/-
A pharmacokinetic (PK) drug-concentration simulator -- the dynamical core PastaLean
transpiles to Lean 4.

Classic two-compartment model with first-order oral absorption and repeated dosing:

    Gut depot  D  --ka-->  Plasma  C  --ke--> (eliminated)
                           C  <--k21-- / --k12-->  Tissue  P

The ODE right-hand sides and the derived quantities each live in their own function; `main`
only reads the parameters from stdin, administers doses, and steps the integrator. A fixed dose
is dropped into the gut every `dose_step` steps, so plasma concentration climbs with each dose,
converges to a steady state, then washes out -- the textbook drug-accumulation curve.

Run directly it uses real SciPy; transpiled by PastaLean it uses the Mathlib-only `Libraries.scipy`
shim. The showcase runs both and overlays the Python and Lean trajectories.
-/
def depot_rate := fun (ka : Rat) ↦ fun (depot : Rat) ↦
  /-
  dD/dt -- drug leaving the gut depot by absorption.
  -/
  -ka *ₚ depot

attribute [simp, taste_ingr] depot_rate

def depot_rate'rn := fun (ka : Float) ↦ fun (depot : Float) ↦
  /-
  dD/dt -- drug leaving the gut depot by absorption.
  -/
  -ka *ₚ depot

def central_rate := fun (ka : Rat) ↦ fun ke ↦ fun (k12 : Rat) ↦ fun (k21 : Rat) ↦ fun (depot : Rat) ↦
  fun (central : Rat) ↦ fun (periph : Rat) ↦
  /-
  dC/dt -- absorption in, elimination out, exchange with the peripheral compartment.
  -/
  ka *ₚ depot -ₚ ke *ₚ central -ₚ k12 *ₚ central +ₚ k21 *ₚ periph

attribute [simp, taste_ingr] central_rate

def central_rate'rn := fun (ka : Float) ↦ fun ke ↦ fun (k12 : Float) ↦ fun (k21 : Float) ↦ fun (depot : Float) ↦
  fun (central : Float) ↦ fun (periph : Float) ↦
  /-
  dC/dt -- absorption in, elimination out, exchange with the peripheral compartment.
  -/
  ka *ₚ depot -ₚ ke *ₚ central -ₚ k12 *ₚ central +ₚ k21 *ₚ periph

def periph_rate := fun (k12 : Rat) ↦ fun (k21 : Rat) ↦ fun (central : Rat) ↦ fun (periph : Rat) ↦
  /-
  dP/dt -- distribution into and back out of the tissue compartment.
  -/
  k12 *ₚ central -ₚ k21 *ₚ periph

attribute [simp, taste_ingr] periph_rate

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

attribute [simp, taste_ingr] concentration

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

attribute [simp] body_load

def body_load'rn := fun (depot : Float) ↦ fun (central : Float) ↦ fun (periph : Float) ↦
  /-
  Total body drug load as the Euclidean norm of the compartment vector (via scipy).
  -/
  Libraries.scipy.pyScipyNorm [depot, central, periph]

-- --- Provable invariants of the model (transpiled to `theorem ... := by taste?`) ---
-- Each function's parameters are the universally-quantified variables; the `assert` is the property.
-- These are proof obligations: in the prove (ℚ) version they become `have/theorem ... := by taste?`;
-- the runnable version drops them.
theorem mass_balance :
    ∀ (ka : Rat),
      ∀ (ke : Rat),
        ∀ (k12 : Rat),
          ∀ (k21 : Rat),
            ∀ (depot : Rat),
              ∀ (central : Rat),
                ∀ (periph : Rat),
                  ((depot_rate ka depot +ₚ central_rate ka ke k12 k21 depot central periph +ₚ
                        periph_rate k12 k21 central periph ==
                      -ke *ₚ central) =
                    true) :=
  by taste?

theorem distribution_conserves :
    ∀ (k12 : Rat),
      ∀ (k21 : Rat),
        ∀ (central : Rat),
          ∀ (periph : Rat),
            ((-k12 *ₚ central +ₚ k21 *ₚ periph +ₚ (k12 *ₚ central -ₚ k21 *ₚ periph) == (0 : Int)) = true) :=
  by taste?

theorem conserved_without_elimination :
    ∀ (ka : Rat),
      ∀ (k12 : Rat),
        ∀ (k21 : Rat),
          ∀ (depot : Rat),
            ∀ (central : Rat),
              ∀ (periph : Rat),
                ((depot_rate ka depot +ₚ central_rate ka (0 : Int) k12 k21 depot central periph +ₚ
                      periph_rate k12 k21 central periph ==
                    (0 : Int)) =
                  true) :=
  by taste?

def step_mass_balance := fun (ka : Rat) ↦ fun (ke : Rat) ↦ fun (k12 : Rat) ↦ fun (k21 : Rat) ↦ fun (depot : Rat) ↦
  fun (central : Rat) ↦ fun (periph : Rat) ↦ fun (dt : Rat) ↦
  Id.run do
    /-
    One forward-Euler step loses exactly the eliminated amount ke*central*dt (no spurious leak).
    -/
    let mut new_depot := depot +ₚ depot_rate ka depot *ₚ dt
    let mut new_central := central +ₚ central_rate ka ke k12 k21 depot central periph *ₚ dt
    let mut new_periph := periph +ₚ periph_rate k12 k21 central periph *ₚ dt
    have ht_1 :
      ((new_depot +ₚ new_central +ₚ new_periph == depot +ₚ central +ₚ periph -ₚ ke *ₚ central *ₚ dt) = true) := by
      taste?

attribute [simp] step_mass_balance

def step_mass_balance'rn := fun (ka : Float) ↦ fun (ke : Float) ↦ fun (k12 : Float) ↦ fun (k21 : Float) ↦
  fun (depot : Float) ↦ fun (central : Float) ↦ fun (periph : Float) ↦ fun (dt : Float) ↦
  Id.run do
    /-
    One forward-Euler step loses exactly the eliminated amount ke*central*dt (no spurious leak).
    -/
    let mut new_depot := depot +ₚ depot_rate'rn ka depot *ₚ dt
    let mut new_central := central +ₚ central_rate'rn ka ke k12 k21 depot central periph *ₚ dt
    let mut new_periph := periph +ₚ periph_rate'rn k12 k21 central periph *ₚ dt
    let _ := ()

noncomputable def main' :=
  ((do
      let mut ka := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut ke := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut k12 := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut k21 := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut vol := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut dose := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut dt := PastaLean.pyRat (← PastaLean.pyInputIO "")
      let mut dose_step := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut ndoses := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut nsteps := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut every := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut depot := (0.0 : Rat)
      let mut central := (0.0 : Rat)
      let mut periph := (0.0 : Rat)
      let mut t := (0.0 : Rat)
      let mut dose_num := (0 : Int)
      for step in (PastaLean.pyRange nsteps)do
        -- Administer a dose into the gut depot when one is due.
        if h_1 : step %ₚ dose_step = (0 : Int) then 
          if h_2 : dose_num < ndoses then 
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
        if h_2 : step %ₚ every = (0 : Int) then 
          let _ ←
            pyPrintNoop
                [pyPrintArg "S", pyPrintArg step, pyPrintArg t, pyPrintArg (concentration central vol),
                  pyPrintArg (concentration periph vol), pyPrintArg depot, pyPrintArg (body_load depot central periph)]
        else
          let _ := ()) :
    IO _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut ka := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut ke := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut k12 := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut k21 := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut vol := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut dose := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut dt := PastaLean.pyFloat (← PastaLean.pyInputIO "")
      let mut dose_step := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut ndoses := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut nsteps := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut every := PastaLean.pyInt (← PastaLean.pyInputIO "")
      let mut depot := (0.0 : Float)
      let mut central := (0.0 : Float)
      let mut periph := (0.0 : Float)
      let mut t := (0.0 : Float)
      let mut dose_num := (0 : Int)
      for step in (PastaLean.pyRange nsteps)do
        -- Administer a dose into the gut depot when one is due.
        if h_1 : step %ₚ dose_step == (0 : Int) then 
          if h_2 : dose_num < ndoses then 
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
        if h_2 : step %ₚ every == (0 : Int) then 
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
