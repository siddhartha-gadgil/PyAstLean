import PyAstLean
import Libraries

open PyAstLean
open Libraries

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

def rabbit_rate := fun (g : Rat) ↦ fun (r_pop : Rat) ↦ fun (w : Rat) ↦ b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w

def wolf_rate := fun (r_pop : Rat) ↦ fun (w : Rat) ↦ e *ₚ r_pop *ₚ w -ₚ _f *ₚ w

def system_deriv := fun (state : List Rat) ↦ fun (t : Rat) ↦
  /-
  Derivative function for the ODE system. Pure (Tier 0).
  -/
  [grass_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌, rabbit_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌ state⦋(2 : Int)⦌,
    wolf_rate state⦋(1 : Int)⦌ state⦋(2 : Int)⦌]

def calc_avg := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦ (g +ₚ r_p +ₚ w) /ₚ (3.0 : Rat)

noncomputable def calc_entropy := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦
  -(g *ₚ Libraries.math.pyMathLogR (g +ₚ (1.0 : Rat)) +ₚ r_p *ₚ Libraries.math.pyMathLogR (r_p +ₚ (1.0 : Rat)) +ₚ
      w *ₚ Libraries.math.pyMathLogR (w +ₚ (1.0 : Rat)))

def is_ecosystem_surviving := fun (w_final : Rat) ↦ decide (w_final > (0.1 : Rat))

-- ============================================================================
--  THEOREMS — proved directly on the generated ℚ definitions above.
--  (Exact mode: `float` → ℚ, a computable ordered field, so `ring`/`nlinarith`
--   work AND the same defs `#eval`. No separate ℝ re-statement needed.)
-- ============================================================================

/-- No grass ⇒ grass growth is zero (a fixed line of the dynamics). -/
theorem grass_rate_zero (r_pop : ℚ) : grass_rate 0 r_pop = 0 := by
  simp [grass_rate, r, k, a]

/-- Wolves at the all-zero state are stationary (extinction fixed point, wolf axis). -/
theorem wolf_rate_zero : wolf_rate 0 0 = 0 := by
  simp [wolf_rate, e, _f]

/-- `wolf_rate` factors as `w · (e·r_pop − _f)`. -/
theorem wolf_rate_factored (r_pop w : ℚ) :
    wolf_rate r_pop w = w * (e * r_pop - _f) := by
  simp only [wolf_rate, e, _f, PyAstLean.pyMul_rat, PyAstLean.pySub_rat]; ring

/-- With no rabbits, the wolf population strictly declines (`dw/dt < 0` for `w > 0`). -/
theorem wolves_starve (w : ℚ) (hw : 0 < w) : wolf_rate 0 w < 0 := by
  simp only [wolf_rate, e, _f, PyAstLean.pyMul_rat, PyAstLean.pySub_rat]; nlinarith

/-- The all-zero ecosystem is a fixed point of the whole derivative — and it is *computable*
(`ℚ`), so this closes by evaluation. -/
theorem extinction_fixed_point : system_deriv [0, 0, 0] 0 = [0, 0, 0] := by
  native_decide
