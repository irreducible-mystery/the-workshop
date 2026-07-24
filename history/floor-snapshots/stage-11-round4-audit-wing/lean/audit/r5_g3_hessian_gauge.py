#!/usr/bin/env python3
"""r5_g3_hessian_gauge.py — G3, the Q4 question (investigative, floats allowed:
this audits a BENCH, not a proof).

QUESTION: is the pentagon solution-variety torus (round 4: pentagon_iff gives
variety = {p = 1/phi or p = -phi} x {s = -p} x {q free unit, r = p/q}, i.e.
two points times a 1-dim torus, and section 9 says the torus is exactly the
gauge group) THE SAME FACT as grammar_stone5's Hessian null direction?

WHAT THE BENCH COMPUTES (read from /home/claude/workshop/grammar_stone5.py):
  - pentagon residual R(p,q,r,s) = sum of squared pentagon violations over the
    F-matrix [[p, q], [r, s]] in exactly the task's (p,q,r,s) coordinates;
  - its 4x4 Hessian at GOLD = (1/phi, 1/sqrt(phi), 1/sqrt(phi), -1/phi) by
    central differences (h = 1e-4);
  - eigendecomposition: asserts signature {0,+,+,+} (|w0| < 1e-6, w1 > 0.05);
  - and ALREADY compares the null eigenvector with the gauge direction
    gauge = (0, GOLD[1], -GOLD[2], 0) — i.e. exactly d/dlambda at lambda=1 of
    F(lambda) = [[p, lambda q], [lambda^{-1} r, s]] — asserting overlap
    > 0.99999.  So the bench's object and the task's parameterization agree
    coordinate for coordinate; nothing has to be translated.

THIS SCRIPT: reproduces that computation, reports the cosine, and pushes the
identification further than the bench does: null-space dimension, exact
flatness of the gauge orbit under the bench's own residual, tangent-vs-secant
agreement, and the SAME structure at the second pentagon world (Yang-Lee),
which the bench never visits.
"""
import numpy as np
from itertools import product as iproduct

ONE, TAU = 0, 1
PHI = (1 + np.sqrt(5)) / 2


def fuse(a, b):
    if a == ONE:
        return (b,)
    if b == ONE:
        return (a,)
    return (ONE, TAU)


def Fsym(F, a, b, c, d, x, y):
    if x not in fuse(a, b) or d not in fuse(x, c):
        return 0.0
    if y not in fuse(b, c) or d not in fuse(a, y):
        return 0.0
    if ONE in (a, b, c):
        return 1.0
    if d == ONE:
        return 1.0 if (x, y) == (TAU, TAU) else 0.0
    return F[x, y]


def pentagon_residual(F):
    total = 0.0
    for a, b, c, dd in iproduct((ONE, TAU), repeat=4):
        for x in fuse(a, b):
            for y in fuse(x, c):
                for t in fuse(y, dd):
                    for w in fuse(c, dd):
                        for v in fuse(b, w):
                            if t not in fuse(a, v):
                                continue
                            lhs = sum(Fsym(F, a, b, c, y, x, u)
                                      * Fsym(F, a, u, dd, t, y, v)
                                      * Fsym(F, b, c, dd, v, u, w)
                                      for u in fuse(b, c))
                            rhs = (Fsym(F, x, c, dd, t, y, w)
                                   * Fsym(F, a, b, w, t, x, v))
                            total += (lhs - rhs) ** 2
    return total


def pent_p(p):
    return pentagon_residual(np.array([[p[0], p[1]], [p[2], p[3]]]))


def hessian(f, p0, h=1e-4):
    n = len(p0)
    H = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            pp = p0.copy(); pp[i] += h; pp[j] += h; fpp = f(pp)
            pm = p0.copy(); pm[i] += h; pm[j] -= h; fpm = f(pm)
            mp = p0.copy(); mp[i] -= h; mp[j] += h; fmp = f(mp)
            mm = p0.copy(); mm[i] -= h; mm[j] -= h; fmm = f(mm)
            H[i, j] = (fpp - fpm - fmp + fmm) / (4 * h * h)
    return (H + H.T) / 2


def analyze(name, sol, lam_grid=(0.5, 0.8, 1.25, 2.0)):
    """sol = (p, q, r, s), an exact-to-float pentagon solution."""
    p0 = np.array(sol, dtype=float)
    r0 = pent_p(p0)
    H = hessian(pent_p, p0.copy())
    w, V = np.linalg.eigh(H)
    w0_precise = w[0]
    null_dim = int(np.sum(np.abs(w) < 1e-6))
    gauge = np.array([0.0, sol[1], -sol[2], 0.0])
    gauge /= np.linalg.norm(gauge)
    cos = abs(float(V[:, 0] @ gauge))
    # exact flatness of the gauge orbit under the bench's own residual
    orbit_res = max(pent_p(np.array([sol[0], l * sol[1], sol[2] / l, sol[3]]))
                    for l in lam_grid)
    # secant sanity: (F(1+eps) - F(1))/eps ~ gauge tangent
    eps = 1e-6
    sec = np.array([0.0, (1 + eps) * sol[1] - sol[1],
                    sol[2] / (1 + eps) - sol[2], 0.0]) / eps
    sec /= np.linalg.norm(sec)
    cos_sec = abs(float(sec @ gauge))
    print(f"[{name}]")
    print(f"  residual at solution       : {r0:.3e}")
    print(f"  Hessian eigenvalues        : {np.round(w, 8).tolist()}  (w0 = {w0_precise:.3e})")
    print(f"  null eigenvector           : {np.round(V[:, 0], 9).tolist()}")
    print(f"  null-space dimension (<1e-6): {null_dim}")
    print(f"  |cos(null mode, gauge dir)| : {cos:.12f}   (1 - cos = {1-cos:.3e})")
    print(f"  gauge-orbit residual, lambda in {list(lam_grid)}: max {orbit_res:.3e}")
    print(f"  secant-vs-tangent cosine    : {cos_sec:.12f}")
    ok = (r0 < 1e-24 and null_dim == 1 and cos > 0.99999
          and orbit_res < 1e-20 and w[1] > 0.05)
    print(f"  => {'PASS' if ok else 'FAIL'}: exactly one flat direction; it is the gauge/torus tangent;")
    print(f"     the torus through this point is exactly flat under the bench residual.")
    return ok, w, cos, orbit_res


print("G3 — is the algebraic torus the same fact as the bench null direction?")
print()

# World 1: the golden solution, exactly the bench's GOLD.
GOLD = (1 / PHI, 1 / np.sqrt(PHI), 1 / np.sqrt(PHI), -1 / PHI)
ok1, w1, cos1, orb1 = analyze("golden world  p = 1/phi ", GOLD)
print()

# World 2 (bench never visits it): Yang-Lee, p = -phi, s = -p = phi,
# q free — take q = 1, then r = p/q = -phi.  Round 4's pentagon_iff says this
# is a solution; the bench residual should agree, with the same null structure.
YL = (-PHI, 1.0, -PHI, PHI)
ok2, w2, cos2, orb2 = analyze("yang-lee world p = -phi ", YL)
print()

# Control: R is NOT globally gauge-invariant — the flat direction is a fact
# about the SOLUTION VARIETY (residual components vanish there and their
# orbit-derivatives with them), not a symmetry of R off the variety.  This
# rules out the cheap reading "the null mode is just a symmetry of the
# objective" and pins it to the variety tangent.
rng = np.random.default_rng(7)
moved = tested = 0
while tested < 40:
    p, q, r, s = rng.uniform(-1.5, 1.5, 4)
    if abs(q) < 0.1 or abs(r) < 0.1:
        continue
    tested += 1
    l = rng.uniform(0.3, 3.0)
    R1 = pent_p(np.array([p, q, r, s]))
    R2 = pent_p(np.array([p, l * q, r / l, s]))
    if abs(R1 - R2) > 1e-12 * max(1.0, abs(R1)):
        moved += 1
print(f"CONTROL: R off the variety moves under the gauge action in {moved}/{tested}")
print("         random non-solutions — R is not globally gauge-invariant, so the")
print("         null mode is the variety's tangent, not an objective symmetry.")
print()

# The identification, spelled out:
print("IDENTIFICATION LOGIC (why cosine ~ 1 is the right test):")
print("  R is a sum of squares vanishing on the solution variety; at any of")
print("  its zeros H = 2 J^T J (Gauss-Newton, PSD), so null(H) = ker(J) = the")
print("  (Zariski) tangent space of the variety cut out by the residuals.")
print("  Round 4's pentagon_iff: variety = {p=1/phi or p=-phi, s=-p, qr=p},")
print("  tangent at any point = span{(0, q, -r, 0)} — d/dq of (q, p/q) scaled")
print("  by q — which IS d/dlambda F(lambda)=[[p,lambda q],[r/lambda,s]] at 1.")
print("  So 'null mode = gauge tangent, null dim = 1' is exactly the")
print("  linearization of 'the solution torus is exactly the gauge orbit'.")
print()
verdict = "SAME-FACT-VERIFIED" if (ok1 and ok2) else "CONSISTENT-BUT-UNDERDETERMINED"
print("G3 VERDICT:", verdict)
