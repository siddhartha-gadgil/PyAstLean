"""A pharmacokinetic (PK) drug-concentration simulator -- the dynamical core PastaLean
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
"""

from scipy.linalg import norm


def depot_rate(ka: float, depot: float) -> float:
    """dD/dt -- drug leaving the gut depot by absorption."""
    return -ka * depot


def central_rate(ka: float, ke: float, k12: float, k21: float,
                 depot: float, central: float, periph: float) -> float:
    """dC/dt -- absorption in, elimination out, exchange with the peripheral compartment."""
    return ka * depot - ke * central - k12 * central + k21 * periph


def periph_rate(k12: float, k21: float, central: float, periph: float) -> float:
    """dP/dt -- distribution into and back out of the tissue compartment."""
    return k12 * central - k21 * periph


def concentration(amount: float, vol: float) -> float:
    """Convert a compartment amount (mg) to a concentration (mg/L)."""
    return amount / vol


def body_load(depot: float, central: float, periph: float) -> float:
    """Total body drug load as the Euclidean norm of the compartment vector (via scipy)."""
    return norm([depot, central, periph])


def main():
    ka = float(input())     # absorption rate (1/h)
    ke = float(input())     # elimination rate (1/h)
    k12 = float(input())    # central -> peripheral
    k21 = float(input())    # peripheral -> central
    vol = float(input())    # volume of distribution (L)
    dose = float(input())   # dose amount (mg)
    dt = float(input())     # timestep (h)
    dose_step = int(input())  # administer a dose every this many steps
    ndoses = int(input())
    nsteps = int(input())
    every = int(input())    # record every this many steps

    depot = 0.0
    central = 0.0
    periph = 0.0
    t = 0.0
    dose_num = 0

    for step in range(nsteps):
        # Administer a dose into the gut depot when one is due.
        if step % dose_step == 0:
            if dose_num < ndoses:
                depot = depot + dose
                dose_num = dose_num + 1

        # One forward-Euler step using the rate functions.
        d_depot = depot_rate(ka, depot)
        d_central = central_rate(ka, ke, k12, k21, depot, central, periph)
        d_periph = periph_rate(k12, k21, central, periph)
        depot = depot + d_depot * dt
        central = central + d_central * dt
        periph = periph + d_periph * dt
        t = t + dt

        if step % every == 0:
            print("S", step, t, concentration(central, vol),
                  concentration(periph, vol), depot, body_load(depot, central, periph))


if __name__ == "__main__":
    main()
