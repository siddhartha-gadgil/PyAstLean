import math

# --- PURE MATH (Tier 0, provable) ---
# Exact mode lowers these to ℚ (rational, computable AND provable); calc_entropy uses
# math.log so it is ℝ/noncomputable but still provable. The runnable simulation (odeint,
# linspace, IO loop) lives in pk_simulation.py and is generated with --approx (all Float).

# parameters for the 3-body system (grass, rabbits, wolves)
r = 1.2
k = 100.0
a = 0.1
b = 0.05
d = 0.4
c = 0.1
e = 0.02
_f = 0.3

def grass_rate(g: float, r_pop: float) -> float:
    return r * g * (1.0 - g / k) - a * g * r_pop

def rabbit_rate(g: float, r_pop: float, w: float) -> float:
    return b * g * r_pop - d * r_pop - c * r_pop * w

def wolf_rate(r_pop: float, w: float) -> float:
    return e * r_pop * w - _f * w

def system_deriv(state: list[float], t: float) -> list[float]:
    """Derivative function for the ODE system. Pure (Tier 0)."""
    return [
        grass_rate(state[0], state[1]),
        rabbit_rate(state[0], state[1], state[2]),
        wolf_rate(state[1], state[2])
    ]

def calc_avg(g: float, r_p: float, w: float) -> float:
    return (g + r_p + w) / 3.0

def calc_entropy(g: float, r_p: float, w: float) -> float:
    return -(g * math.log(g + 1.0) + r_p * math.log(r_p + 1.0) + w * math.log(w + 1.0))

def is_ecosystem_surviving(w_final: float) -> bool:
    return w_final > 0.1
