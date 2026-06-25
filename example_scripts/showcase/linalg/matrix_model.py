"""2x2 matrix algebra + a discrete linear dynamical system.

A second, different-flavour stress test for the "decompose deep, wrap thin" recipe (cf. the 3D
vector model in `../orbital/orbital_model.py`): the leaves are the scalar entries of 2x2 matrix
operations -- determinant, trace, and the four entries of a matrix product -- and they compose
upward into the classical identities of linear algebra. `main` is the single monadic island: it
reads a 2x2 matrix and a vector and iterates the linear map x -> A x, printing the orbit and the
(conserved-up-to-det) quantities.

Everything with an `assert` is a *provable invariant*, transpiled to `theorem ... := by taste?`:

  * ring identities  -- determinant multiplicativity det(AB)=det(A)det(B), the adjugate inverse
                        A.adj(A)=det(A).I, the Cayley-Hamilton theorem A^2 - tr(A)A + det(A)I = 0,
                        trace cyclicity tr(AB)=tr(BA), det of the transpose / adjugate, scaling;
  * constrained laws -- a rotation matrix (c^2+s^2=1) has determinant 1 and preserves the norm.

Every entry is a polynomial over the rationals -- no transcendentals -- so `ring` / `nlinarith`
reach the proofs directly.
"""


# ----------------------------------------------------------------------------------------------
# Tier-0 leaves: scalar entries of 2x2 matrix operations.  A 2x2 matrix is its four entries
# (a b ; c d); a product of A=(a b ; c d) and B=(e f ; g h) has the four entries below.
# ----------------------------------------------------------------------------------------------

def det(a: float, b: float, c: float, d: float) -> float:
    """Determinant of (a b ; c d)."""
    return a * d - b * c


def trace(a: float, b: float, c: float, d: float) -> float:
    """Trace of (a b ; c d)."""
    return a + d


def mul11(a: float, b: float, c: float, d: float,
          e: float, f: float, g: float, h: float) -> float:
    """(1,1) entry of A B."""
    return a * e + b * g


def mul12(a: float, b: float, c: float, d: float,
          e: float, f: float, g: float, h: float) -> float:
    """(1,2) entry of A B."""
    return a * f + b * h


def mul21(a: float, b: float, c: float, d: float,
          e: float, f: float, g: float, h: float) -> float:
    """(2,1) entry of A B."""
    return c * e + d * g


def mul22(a: float, b: float, c: float, d: float,
          e: float, f: float, g: float, h: float) -> float:
    """(2,2) entry of A B."""
    return c * f + d * h


# ----------------------------------------------------------------------------------------------
# Provable invariants: ring identities  (lone `assert` -> named `theorem`, closed by `ring`)
# ----------------------------------------------------------------------------------------------

def det_multiplicative(a: float, b: float, c: float, d: float,
                       e: float, f: float, g: float, h: float):
    """Determinant is multiplicative: det(A B) = det(A) det(B)."""
    assert det(mul11(a, b, c, d, e, f, g, h), mul12(a, b, c, d, e, f, g, h),
               mul21(a, b, c, d, e, f, g, h), mul22(a, b, c, d, e, f, g, h)) \
        == det(a, b, c, d) * det(e, f, g, h)


def trace_cyclic(a: float, b: float, c: float, d: float,
                 e: float, f: float, g: float, h: float):
    """Trace is cyclic: tr(A B) = tr(B A)."""
    assert (mul11(a, b, c, d, e, f, g, h) + mul22(a, b, c, d, e, f, g, h)
            == mul11(e, f, g, h, a, b, c, d) + mul22(e, f, g, h, a, b, c, d))


def det_transpose(a: float, b: float, c: float, d: float):
    """The transpose has the same determinant: det(A^T) = det(A)."""
    assert det(a, c, b, d) == det(a, b, c, d)


def det_scale(k: float, a: float, b: float, c: float, d: float):
    """Scaling a 2x2 matrix scales its determinant quadratically: det(kA) = k^2 det(A)."""
    assert det(k * a, k * b, k * c, k * d) == k * k * det(a, b, c, d)


def det_adjugate(a: float, b: float, c: float, d: float):
    """The adjugate has the same determinant: det(adj A) = det(A)."""
    assert det(d, -b, -c, a) == det(a, b, c, d)


def trace_additive(a: float, b: float, c: float, d: float,
                   e: float, f: float, g: float, h: float):
    """Trace is additive: tr(A + B) = tr(A) + tr(B)."""
    assert trace(a + e, b + f, c + g, d + h) == trace(a, b, c, d) + trace(e, f, g, h)


def adjugate_inverse_diag(a: float, b: float, c: float, d: float):
    """A times its adjugate is det(A) times the identity -- the (1,1) entry equals det(A)."""
    assert mul11(a, b, c, d, d, -b, -c, a) == det(a, b, c, d)


def adjugate_inverse_offdiag(a: float, b: float, c: float, d: float):
    """A times its adjugate is det(A) times the identity -- the (1,2) entry vanishes."""
    assert mul12(a, b, c, d, d, -b, -c, a) == 0


def cayley_hamilton_diag(a: float, b: float, c: float, d: float):
    """Cayley-Hamilton, (1,1) entry: A^2 - tr(A) A + det(A) I = 0."""
    assert (mul11(a, b, c, d, a, b, c, d) - trace(a, b, c, d) * a + det(a, b, c, d)) == 0


def cayley_hamilton_offdiag(a: float, b: float, c: float, d: float):
    """Cayley-Hamilton, (1,2) entry: the off-diagonal of A^2 - tr(A) A vanishes (I has none)."""
    assert (mul12(a, b, c, d, a, b, c, d) - trace(a, b, c, d) * b) == 0


# ----------------------------------------------------------------------------------------------
# Provable invariants: constrained laws  (`if`-guard -> hypotheses; ring / nlinarith)
# ----------------------------------------------------------------------------------------------

def rotation_has_unit_det(c: float, s: float):
    """A rotation matrix (c -s ; s c) with c^2 + s^2 = 1 has determinant 1."""
    if c * c + s * s == 1:
        assert det(c, -s, s, c) == 1


def rotation_preserves_norm(c: float, s: float, x: float, y: float):
    """A rotation (c^2 + s^2 = 1) preserves the squared norm of the vector it acts on:
    |(c x - s y, s x + c y)|^2 = x^2 + y^2."""
    if c * c + s * s == 1:
        assert ((c * x - s * y) * (c * x - s * y) + (s * x + c * y) * (s * x + c * y)
                == x * x + y * y)


def det_nonneg_of_symmetric_psd(a: float, b: float, d: float):
    """A 2x2 symmetric matrix (a b ; b d) that is a Gram matrix (a = p^2+q^2 style) ... here:
    if the diagonal dominates (a*d >= b*b), the determinant is non-negative."""
    if a * d >= b * b:
        assert det(a, b, b, d) >= 0


# ----------------------------------------------------------------------------------------------
# EDGE: main -- iterate the linear map x -> A x (a discrete linear dynamical system); NOT proved
# ----------------------------------------------------------------------------------------------

def main():
    a = float(input())          # matrix entries (a b ; c d)
    b = float(input())
    c = float(input())
    d = float(input())
    x = float(input())          # initial vector (x, y)
    y = float(input())
    nsteps = int(input())
    every = int(input())

    detA = det(a, b, c, d)
    for step in range(nsteps):
        # One step of the linear map (x, y) -> (a x + b y, c x + d y).
        nx = a * x + b * y
        ny = c * x + d * y
        x = nx
        y = ny

        if step % every == 0:
            print("S", step, x, y, detA)


if __name__ == "__main__":
    main()
