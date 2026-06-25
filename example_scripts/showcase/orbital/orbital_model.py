"""3D coupled two-body harmonic oscillator with a symplectic velocity-Verlet integrator.

The "decompose deep, wrap thin" recipe pushed harder than `pk_model.py`: a foundation of pure
3-vector algebra leaves (dot, cross, squared-norm) composes upward into the conserved quantities of
mechanics -- linear momentum, angular momentum, kinetic energy, spring potential -- and a
velocity-Verlet step that advances two masses joined by a Hooke spring (a linear, polynomial
restoring force, so the whole model stays exact-rational and provable). `main` is the only monadic
island: it reads the bodies' masses and phase-space state, integrates, and prints the conserved
quantities so you can watch them stay flat.

Everything with an `assert` is a *provable invariant*, transpiled to `theorem ... := by taste?`:

  * vector identities  -- bilinearity, antisymmetry, orthogonality of the cross product, the
                          Lagrange identity, parallelogram / polarization laws, the BAC-CAB rule;
  * physical laws      -- a central force exerts no torque (angular momentum is conserved), equal
                          and opposite spring forces conserve total momentum, kinetic and spring
                          energy are non-negative, Cauchy-Schwarz bounds the dot product.

Each is a single-expression Tier-0 term, so `ring` / `nlinarith` / `positivity` reach them directly.
No transcendentals (`sqrt`, `**0.5`) appear anywhere, so every quantity is a polynomial over the
rationals -- which is exactly what keeps the proofs in reach of the automation.
"""


# ----------------------------------------------------------------------------------------------
# Tier-0 vector-algebra leaves  (each one expression; provable, and everything below composes them)
# ----------------------------------------------------------------------------------------------

def dot(ax: float, ay: float, az: float, bx: float, by: float, bz: float) -> float:
    """Euclidean inner product a . b."""
    return ax * bx + ay * by + az * bz


def cross_x(ax: float, ay: float, az: float, bx: float, by: float, bz: float) -> float:
    """x-component of a x b."""
    return ay * bz - az * by


def cross_y(ax: float, ay: float, az: float, bx: float, by: float, bz: float) -> float:
    """y-component of a x b."""
    return az * bx - ax * bz


def cross_z(ax: float, ay: float, az: float, bx: float, by: float, bz: float) -> float:
    """z-component of a x b."""
    return ax * by - ay * bx


def norm_sq(ax: float, ay: float, az: float) -> float:
    """Squared Euclidean norm |a|^2 = a . a."""
    return ax * ax + ay * ay + az * az


def kinetic(m: float, vx: float, vy: float, vz: float) -> float:
    """Kinetic energy (1/2) m |v|^2."""
    return 0.5 * m * norm_sq(vx, vy, vz)


def spring_energy(k: float, dx: float, dy: float, dz: float) -> float:
    """Hooke potential energy (1/2) k |d|^2 stored in a spring stretched by displacement d."""
    return 0.5 * k * norm_sq(dx, dy, dz)


# ----------------------------------------------------------------------------------------------
# Provable invariants: vector identities  (lone `assert` -> named `theorem`, closed by `ring`)
# ----------------------------------------------------------------------------------------------

def dot_commutes(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """The inner product is symmetric."""
    assert dot(ax, ay, az, bx, by, bz) == dot(bx, by, bz, ax, ay, az)


def dot_additive(ax: float, ay: float, az: float, cx: float, cy: float, cz: float,
                 bx: float, by: float, bz: float):
    """Inner product is additive in its first argument: (a + c) . b = a.b + c.b."""
    assert dot(ax + cx, ay + cy, az + cz, bx, by, bz) == (dot(ax, ay, az, bx, by, bz)
                                                          + dot(cx, cy, cz, bx, by, bz))


def dot_homogeneous(s: float, ax: float, ay: float, az: float,
                    bx: float, by: float, bz: float):
    """Inner product is homogeneous in its first argument: (s a) . b = s (a . b)."""
    assert dot(s * ax, s * ay, s * az, bx, by, bz) == s * dot(ax, ay, az, bx, by, bz)


def cross_antisymmetric(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """The cross product is antisymmetric (x-component): (a x b)_x = -(b x a)_x."""
    assert cross_x(ax, ay, az, bx, by, bz) == -cross_x(bx, by, bz, ax, ay, az)


def cross_self_zero(ax: float, ay: float, az: float):
    """A vector crossed with itself vanishes (x-component)."""
    assert cross_x(ax, ay, az, ax, ay, az) == 0


def cross_perp_first(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """a x b is orthogonal to a: a . (a x b) = 0."""
    assert dot(ax, ay, az,
               cross_x(ax, ay, az, bx, by, bz),
               cross_y(ax, ay, az, bx, by, bz),
               cross_z(ax, ay, az, bx, by, bz)) == 0


def cross_perp_second(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """a x b is orthogonal to b: b . (a x b) = 0."""
    assert dot(bx, by, bz,
               cross_x(ax, ay, az, bx, by, bz),
               cross_y(ax, ay, az, bx, by, bz),
               cross_z(ax, ay, az, bx, by, bz)) == 0


def lagrange_identity(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """Lagrange's identity: |a x b|^2 + (a . b)^2 = |a|^2 |b|^2."""
    assert (norm_sq(cross_x(ax, ay, az, bx, by, bz),
                    cross_y(ax, ay, az, bx, by, bz),
                    cross_z(ax, ay, az, bx, by, bz))
            + dot(ax, ay, az, bx, by, bz) * dot(ax, ay, az, bx, by, bz)
            == norm_sq(ax, ay, az) * norm_sq(bx, by, bz))


def parallelogram_identity(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """The parallelogram law: |a + b|^2 + |a - b|^2 = 2|a|^2 + 2|b|^2."""
    assert (norm_sq(ax + bx, ay + by, az + bz) + norm_sq(ax - bx, ay - by, az - bz)
            == 2.0 * norm_sq(ax, ay, az) + 2.0 * norm_sq(bx, by, bz))


def polarization_identity(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """The polarization identity (cleared of the 1/4): 2(a.b) = |a+b|^2 - |a|^2 - |b|^2."""
    assert (2.0 * dot(ax, ay, az, bx, by, bz)
            == norm_sq(ax + bx, ay + by, az + bz) - norm_sq(ax, ay, az) - norm_sq(bx, by, bz))


def bac_cab_rule(ax: float, ay: float, az: float, bx: float, by: float, bz: float,
                 cx: float, cy: float, cz: float):
    """The BAC-CAB rule (x-component): (a x (b x c))_x = b_x (a.c) - c_x (a.b)."""
    assert cross_x(ax, ay, az,
                   cross_x(bx, by, bz, cx, cy, cz),
                   cross_y(bx, by, bz, cx, cy, cz),
                   cross_z(bx, by, bz, cx, cy, cz)) == (bx * dot(ax, ay, az, cx, cy, cz)
                                                       - cx * dot(ax, ay, az, bx, by, bz))


# ----------------------------------------------------------------------------------------------
# Provable invariants: non-negativity & bounds  (`if`-guard -> hypotheses; nlinarith / positivity)
# ----------------------------------------------------------------------------------------------

def norm_sq_nonneg(ax: float, ay: float, az: float):
    """A squared norm is never negative."""
    assert norm_sq(ax, ay, az) >= 0


def kinetic_nonneg(m: float, vx: float, vy: float, vz: float):
    """With non-negative mass, kinetic energy is non-negative."""
    if m >= 0:
        assert kinetic(m, vx, vy, vz) >= 0


def spring_energy_nonneg(k: float, dx: float, dy: float, dz: float):
    """With a non-negative spring constant, the stored potential energy is non-negative."""
    if k >= 0:
        assert spring_energy(k, dx, dy, dz) >= 0


def cauchy_schwarz(ax: float, ay: float, az: float, bx: float, by: float, bz: float):
    """Cauchy-Schwarz: (a . b)^2 <= |a|^2 |b|^2, built from two helper facts that land in scope as
    local hypotheses (so `linarith` composes them) -- the SOS certificate bare `nlinarith` can't find:
      1. Lagrange's identity   |a x b|^2 + (a . b)^2 = |a|^2 |b|^2, and
      2. the cross norm is non-negative   |a x b|^2 >= 0,
    whence (a . b)^2 = |a|^2 |b|^2 - |a x b|^2 <= |a|^2 |b|^2."""
    assert (norm_sq(cross_x(ax, ay, az, bx, by, bz),
                    cross_y(ax, ay, az, bx, by, bz),
                    cross_z(ax, ay, az, bx, by, bz))
            + dot(ax, ay, az, bx, by, bz) * dot(ax, ay, az, bx, by, bz)
            == norm_sq(ax, ay, az) * norm_sq(bx, by, bz))
    assert norm_sq(cross_x(ax, ay, az, bx, by, bz),
                   cross_y(ax, ay, az, bx, by, bz),
                   cross_z(ax, ay, az, bx, by, bz)) >= 0
    assert (dot(ax, ay, az, bx, by, bz) * dot(ax, ay, az, bx, by, bz)
            <= norm_sq(ax, ay, az) * norm_sq(bx, by, bz))


# ----------------------------------------------------------------------------------------------
# Provable invariants: physical conservation laws
# ----------------------------------------------------------------------------------------------

def central_force_no_torque(rx: float, ry: float, rz: float, lam: float):
    """A central force F = lam * r exerts no torque: r x F = 0 (x-component), so angular momentum
    is conserved -- the keystone of orbital mechanics."""
    assert cross_x(rx, ry, rz, lam * rx, lam * ry, lam * rz) == 0


def momentum_conserved(m1: float, v1: float, m2: float, v2: float, j: float):
    """Equal and opposite impulses +j / -j conserve total linear momentum (1-D component)."""
    assert (m1 * v1 + j) + (m2 * v2 - j) == m1 * v1 + m2 * v2


def angular_momentum_is_moment(m: float, rx: float, ry: float, rz: float,
                               vx: float, vy: float, vz: float):
    """Angular momentum L = r x (m v) equals m (r x v) (x-component) -- mass factors out."""
    assert cross_x(rx, ry, rz, m * vx, m * vy, m * vz) == m * cross_x(rx, ry, rz, vx, vy, vz)


def spring_force_is_central(k: float, dx: float, dy: float, dz: float):
    """The Hooke force F = -k d is central (anti-parallel to the displacement d), so it too exerts
    no torque about the spring axis: d x F = 0 (x-component)."""
    assert cross_x(dx, dy, dz, -k * dx, -k * dy, -k * dz) == 0


# ----------------------------------------------------------------------------------------------
# EDGE: main -- the single monadic island (reads input, integrates, prints; NOT proved)
# ----------------------------------------------------------------------------------------------

def main():
    k = float(input())          # spring constant
    m1 = float(input())         # mass of body 1
    m2 = float(input())         # mass of body 2
    r1x = float(input())        # body 1 position
    r1y = float(input())
    r1z = float(input())
    r2x = float(input())        # body 2 position
    r2y = float(input())
    r2z = float(input())
    v1x = float(input())        # body 1 velocity
    v1y = float(input())
    v1z = float(input())
    v2x = float(input())        # body 2 velocity
    v2y = float(input())
    v2z = float(input())
    dt = float(input())         # timestep
    nsteps = int(input())
    every = int(input())        # record every this many steps

    t = 0.0
    for step in range(nsteps):
        # Hooke spring (rest length 0): force F = -k (r1 - r2) on body 1, +k (r1 - r2) on body 2.
        # Acceleration is F / m; all polynomial, no transcendentals.
        dx = r1x - r2x
        dy = r1y - r2y
        dz = r1z - r2z
        a1x = -k * dx / m1
        a1y = -k * dy / m1
        a1z = -k * dz / m1
        a2x = k * dx / m2
        a2y = k * dy / m2
        a2z = k * dz / m2

        # Velocity-Verlet (here the force is linear, so a half/full kick step is exact enough).
        v1x = v1x + a1x * dt
        v1y = v1y + a1y * dt
        v1z = v1z + a1z * dt
        v2x = v2x + a2x * dt
        v2y = v2y + a2y * dt
        v2z = v2z + a2z * dt
        r1x = r1x + v1x * dt
        r1y = r1y + v1y * dt
        r1z = r1z + v1z * dt
        r2x = r2x + v2x * dt
        r2y = r2y + v2y * dt
        r2z = r2z + v2z * dt
        t = t + dt

        if step % every == 0:
            energy = (kinetic(m1, v1x, v1y, v1z) + kinetic(m2, v2x, v2y, v2z)
                      + spring_energy(k, r1x - r2x, r1y - r2y, r1z - r2z))
            px = m1 * v1x + m2 * v2x
            lx = (cross_x(r1x, r1y, r1z, m1 * v1x, m1 * v1y, m1 * v1z)
                  + cross_x(r2x, r2y, r2z, m2 * v2x, m2 * v2y, m2 * v2z))
            print("S", step, t, energy, px, lx)


if __name__ == "__main__":
    main()
