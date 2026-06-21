import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
-- --- PURE MATH (Tier 0, provable) ---
-- Exact mode lowers these to ℚ (rational, computable AND provable); calc_entropy uses
-- math.log so it is ℝ/noncomputable but still provable. The runnable simulation (odeint,
-- linspace, IO loop) lives in pk_simulation.py and is generated with --approx (all Float).
-- parameters for the 3-body system (grass, rabbits, wolves)
def r :=
  (1.2 : Rat)

def k :=
  (100.0 : Rat)

def a :=
  (0.1 : Rat)

def b :=
  (0.05 : Rat)

def d :=
  (0.4 : Rat)

def c :=
  (0.1 : Rat)

def e :=
  (0.02 : Rat)

private def _f :=
  (0.3 : Rat)

def grass_rate := fun (g : Rat) ↦ fun (r_pop : Rat) ↦ r *ₚ g *ₚ ((1.0 : Rat) -ₚ g /ₚ k) -ₚ a *ₚ g *ₚ r_pop

def grass_rate'rn := fun (g : Float) ↦ fun (r_pop : Float) ↦ r *ₚ g *ₚ ((1.0 : Float) -ₚ g /ₚ k) -ₚ a *ₚ g *ₚ r_pop

def rabbit_rate := fun (g : Rat) ↦ fun (r_pop : Rat) ↦ fun (w : Rat) ↦ b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w

def rabbit_rate'rn := fun (g : Float) ↦ fun (r_pop : Float) ↦ fun (w : Float) ↦
  b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w

def wolf_rate := fun (r_pop : Rat) ↦ fun (w : Rat) ↦ e *ₚ r_pop *ₚ w -ₚ _f *ₚ w

def wolf_rate'rn := fun (r_pop : Float) ↦ fun (w : Float) ↦ e *ₚ r_pop *ₚ w -ₚ _f *ₚ w

def system_deriv := fun (state : List Rat) ↦ fun (t : Rat) ↦
  /-
  Derivative function for the ODE system. Pure (Tier 0).
  -/
  [grass_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌, rabbit_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌ state⦋(2 : Int)⦌,
    wolf_rate state⦋(1 : Int)⦌ state⦋(2 : Int)⦌]

def system_deriv'rn := fun (state : List Float) ↦ fun (t : Float) ↦
  /-
  Derivative function for the ODE system. Pure (Tier 0).
  -/
  [grass_rate'rn state⦋(0 : Int)⦌ state⦋(1 : Int)⦌, rabbit_rate'rn state⦋(0 : Int)⦌ state⦋(1 : Int)⦌ state⦋(2 : Int)⦌,
    wolf_rate'rn state⦋(1 : Int)⦌ state⦋(2 : Int)⦌]

def calc_avg := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦ (g +ₚ r_p +ₚ w) /ₚ (3.0 : Rat)

def calc_avg'rn := fun (g : Float) ↦ fun (r_p : Float) ↦ fun (w : Float) ↦ (g +ₚ r_p +ₚ w) /ₚ (3.0 : Float)

noncomputable def calc_entropy := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦
  -(g *ₚ Libraries.math.pyMathLogR (g +ₚ (1.0 : Rat)) +ₚ r_p *ₚ Libraries.math.pyMathLogR (r_p +ₚ (1.0 : Rat)) +ₚ
      w *ₚ Libraries.math.pyMathLogR (w +ₚ (1.0 : Rat)))

def calc_entropy'rn := fun (g : Float) ↦ fun (r_p : Float) ↦ fun (w : Float) ↦
  -(g *ₚ Libraries.math.pyMathLog (g +ₚ (1.0 : Float)) +ₚ r_p *ₚ Libraries.math.pyMathLog (r_p +ₚ (1.0 : Float)) +ₚ
      w *ₚ Libraries.math.pyMathLog (w +ₚ (1.0 : Float)))

def is_ecosystem_surviving := fun (w_final : Rat) ↦ decide (w_final > (0.1 : Rat))

def is_ecosystem_surviving'rn := fun (w_final : Float) ↦ decide (w_final > (0.1 : Float))
