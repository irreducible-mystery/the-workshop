#!/usr/bin/env python3
"""r5_gift_certificates.py — builder round-5 gifts G1 + G2, certified before shipping.

G1  THE MOD-11 CLOSURE of the sigma2-lift hole.
    Claim: no element of K = Z[zeta5][t]/(t^2 - phi) squares to -invPhi = -1/phi,
    hence sigma2 (zeta -> zeta^2) admits NO multiplicative lift to K at all
    (round 4's lift_forces_sqrt_neg_invPhi says any lift must send t to such a
    square root).  Closes the round-4 Q2 soft label for the cost of ONE
    evaluation K -> F11, no descent.

G2  THE ORDER ON Z[phi] — pos(m,n) deciding m + n*phi > 0 by integer
    arithmetic only, the road to quantum dimension d_tau = phi in round 5
    (Perron-Frobenius by decide-able order, no analysis).

Every load-bearing check is exact integer arithmetic.  Floats appear only in
G2(a), which is BY DESIGN a float-agreement check with an exact fallback for
near-zero values.  One PASS/FAIL line per check; any FAIL aborts with exit 1.

Standalone: python3 r5_gift_certificates.py
"""
import itertools
import math
import random

random.seed(1313)

FAILED = []


def check(name, ok):
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok:
        FAILED.append(name)


# ═══════════════════════════════════════════════════════════════════════
#  Shared algebra (fixed since round 1, matches round-3 Anyon.lean)
#  Z5 = Z[zeta5] as 4-tuples (a0,a1,a2,a3), z^4 = -(1+z+z^2+z^3), z^5 = 1.
# ═══════════════════════════════════════════════════════════════════════

def red(c):
    """Reduce a degree-<=6 coefficient list to the 4-tuple basis."""
    out = [0] * 4
    for i, v in enumerate(c):
        if v == 0:
            continue
        e = i % 5
        if e < 4:
            out[e] += v
        else:  # z^4 -> -(1+z+z^2+z^3)
            for k in range(4):
                out[k] -= v
    return tuple(out)


def zmul(a, b):
    c = [0] * 7
    for i in range(4):
        for j in range(4):
            c[i + j] += a[i] * b[j]
    return red(c)


def zadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def zneg(a):
    return tuple(-x for x in a)


Z5_ZERO = (0, 0, 0, 0)
Z5_ONE = (1, 0, 0, 0)
ZETA = (0, 1, 0, 0)
PHI5 = zneg(zadd(zmul(ZETA, ZETA), zmul(zmul(ZETA, ZETA), ZETA)))   # -z^2-z^3
INVPHI5 = (-1, 0, -1, -1)

assert PHI5 == (0, 0, -1, -1)
assert zmul(PHI5, INVPHI5) == Z5_ONE  # phi * invPhi = 1, the anchor

# KK = pairs (x, y) of Z5 meaning x + y*t with t^2 = phi.
def kadd(u, v):
    return (zadd(u[0], v[0]), zadd(u[1], v[1]))


def kmul(u, v):
    return (zadd(zmul(u[0], v[0]), zmul(PHI5, zmul(u[1], v[1]))),
            zadd(zmul(u[0], v[1]), zmul(u[1], v[0])))


def kneg(u):
    return (zneg(u[0]), zneg(u[1]))


K_ONE = (Z5_ONE, Z5_ZERO)
K_T = (Z5_ZERO, Z5_ONE)
K_PHI = (PHI5, Z5_ZERO)
K_INVPHI = (INVPHI5, Z5_ZERO)
K_B = kmul(K_T, K_INVPHI)

assert K_B == (Z5_ZERO, INVPHI5)          # b = (0, invPhi), as shipped
assert kmul(K_T, K_B) == K_ONE            # t*b = 1
assert kmul(K_T, K_T) == K_PHI            # t^2 = phi


def rnd5():
    return tuple(random.randint(-999, 999) for _ in range(4))


def rndK():
    return (rnd5(), rnd5())


# ═══════════════════════════════════════════════════════════════════════
#  G1 — THE MOD-11 CLOSURE
# ═══════════════════════════════════════════════════════════════════════
print("── G1: mod-11 closure of the sigma2-lift hole ──────────────────────")

P = 11

# (a) the four fifth-roots of unity mod 11 are exactly {3,9,5,4}:
#     Phi5(x) = x^4+x^3+x^2+x+1 = 0 mod 11 iff x in {3,9,5,4} — an iff over
#     ALL 11 residues.
phi5_roots = [x for x in range(P) if (x**4 + x**3 + x**2 + x + 1) % P == 0]
check("G1a: Phi5(x)=0 mod 11 iff x in {3,9,5,4} (all 11 residues scanned)",
      sorted(phi5_roots) == [3, 4, 5, 9] and set(phi5_roots) == {3, 9, 5, 4})
check("G1a: each of {3,9,5,4} satisfies x^5 = 1 mod 11 (and x != 1)",
      all(pow(x, 5, P) == 1 and x != 1 for x in [3, 9, 5, 4]))

# (b) at zeta -> 9: phi-bar = -(9^2 + 9^3) mod 11 = 4, and t -> 2 has 2^2 = 4.
phibar9 = (-(9**2 + 9**3)) % P
check("G1b: phi-bar at zeta->9 is -(81+729) mod 11 = 4", phibar9 == 4)
check("G1b: t -> 2 satisfies t^2 = phi-bar (4 = 4)", (2 * 2) % P == phibar9)


# (c) the evaluation hom e : K -> F11, e(zeta) = 9, e(t) = 2 — BUILT, and its
#     hom laws verified on random exact KK pairs.
def make_e(z, tval):
    """Evaluation K -> F11 with zeta -> z, t -> tval."""
    def e5(a):
        return (a[0] + a[1] * z + a[2] * z * z + a[3] * z**3) % P

    def e(u):
        return (e5(u[0]) + e5(u[1]) * tval) % P
    return e5, e


e5_9, e_9 = make_e(9, 2)

# Well-definedness receipts: the two defining relations survive evaluation.
check("G1c: reduction rule holds at z=9: 9^4 = -(1+9+9^2+9^3) mod 11",
      pow(9, 4, P) == (-(1 + 9 + 81 + 729)) % P)
check("G1c: 9^5 = 1 mod 11", pow(9, 5, P) == 1)

pairs = [(rndK(), rndK()) for _ in range(300)]
check("G1c: e additive on 300 random exact KK pairs",
      all(e_9(kadd(u, v)) == (e_9(u) + e_9(v)) % P for u, v in pairs))
check("G1c: e multiplicative on 300 random exact KK pairs",
      all(e_9(kmul(u, v)) == (e_9(u) * e_9(v)) % P for u, v in pairs))
check("G1c: e(1) = 1", e_9(K_ONE) == 1)
check("G1c: receipt e(phi) = 4", e_9(K_PHI) == 4)
check("G1c: receipt e(t)^2 = 4", (e_9(K_T)**2) % P == 4)
eb = e_9(K_B)
check("G1c: receipt e(b) = 6 and e(t)*e(b) = 1 (e(b) = e(t)^{-1})",
      eb == 6 and (e_9(K_T) * eb) % P == 1)

# (d) e(-invPhi) = 8, and 8 is NOT a square mod 11 (exhaustive).
squares11 = sorted({(k * k) % P for k in range(P)})
check("G1d: squares mod 11 are exactly {0,1,3,4,5,9} (all 11 residues)",
      squares11 == [0, 1, 3, 4, 5, 9])
check("G1d: invPhi-bar = phi-bar - 1 = 3, so e(-invPhi) = -3 = 8",
      (phibar9 - 1) % P == 3 and (-3) % P == 8)
check("G1d: e(-invPhi) computed through the hom is 8", e_9(kneg(K_INVPHI)) == 8)
check("G1d: 8 is not among the squares mod 11", 8 not in squares11)

# (e) CONCLUSION: s^2 = -invPhi in K would give e(s)^2 = 8 in F11 — impossible.
#     The two machine facts that carry it: e is a ring hom (G1c) and 8 is a
#     nonsquare (G1d).  The hinge that makes this close the LIFT question —
#     any multiplicative lift of sigma2 sends t to a sqrt of sigma2(phi) and
#     sigma2(phi) = -invPhi — is one line of exact Z5 arithmetic from the
#     round-1-fixed definitions, certified here (the round-4 .lean did not
#     arrive, so lift_forces_sqrt_neg_invPhi's arithmetic content is re-proved
#     rather than trusted).  Corroboration: no sampled s squares to -invPhi,
#     and the three obvious candidates t, -t, b all fail exactly (round 4's
#     no_obvious_sqrt_neg_invPhi).
def sig2(a):
    """sigma2 : zeta -> zeta^2 on Z5, via re-reduction (independent of the
    closed form, which is then checked against it)."""
    c = [0] * 7
    c[0] += a[0]; c[2] += a[1]; c[4] += a[2]; c[6] += a[3]
    return red(c)


check("G1e: hinge — sigma2(phi) = -invPhi exactly in Z5 (= (1,0,1,1)), and "
      "the closed form (a0-a2, a3-a2, a1-a2, -a2) agrees; so any "
      "multiplicative lift of sigma2 to K must send t to a sqrt of -invPhi",
      sig2(PHI5) == zneg(INVPHI5) == (1, 0, 1, 1)
      and sig2(PHI5) == (PHI5[0] - PHI5[2], PHI5[3] - PHI5[2],
                         PHI5[1] - PHI5[2], -PHI5[2]))
neg_invphi = kneg(K_INVPHI)
samples = [rndK() for _ in range(300)]
check("G1e: e(s)^2 lands in the square set for 300 random s (hom sanity)",
      all((e_9(s)**2) % P in squares11 for s in samples))
check("G1e: no sampled s in K has s^2 = -invPhi (300 exact squares)",
      all(kmul(s, s) != neg_invphi for s in samples))
check("G1e: the obvious candidates fail exactly: t^2 = phi != -invPhi, "
      "(-t)^2 = phi, b^2 = invPhi != -invPhi",
      kmul(K_T, K_T) == K_PHI and kmul(kneg(K_T), kneg(K_T)) == K_PHI
      and kmul(K_B, K_B) == K_INVPHI and K_PHI != neg_invphi
      and K_INVPHI != neg_invphi)
check("G1e: CONCLUSION armed — a hom to F11 exists and e(-invPhi) = 8 is a "
      "nonsquare, so NO element of K squares to -invPhi; with round 4's "
      "lift_forces_sqrt_neg_invPhi, sigma2 has no multiplicative lift to K",
      True)  # carried entirely by the PASSes above; recorded as the verdict line

# (f) Negative control: the same test must NOT refute sqrt(invPhi), which
#     exists (b^2 = invPhi).  invPhi-bar = 3 IS a square mod 11.
check("G1f: control — b^2 = invPhi exactly in K (a square root that exists)",
      kmul(K_B, K_B) == K_INVPHI)
check("G1f: control — e(invPhi) = 3 IS a square mod 11 (5^2 = 25 = 3)",
      e_9(K_INVPHI) == 3 and 3 in squares11 and (5 * 5) % P == 3)
check("G1f: control — e(b)^2 = e(invPhi) (6^2 = 36 = 3): instrument "
      "distinguishes the existing root from the impossible one",
      (eb * eb) % P == e_9(K_INVPHI))

# (g) The second usable place zeta -> 5, and the two unusable ones.
phibar5 = (-(5**2 + 5**3)) % P
check("G1g: phi-bar at zeta->5 is -(25+125) mod 11 = 4 as well", phibar5 == 4)
e5_5, e_5 = make_e(5, 2)
check("G1g: reduction rule holds at z=5 and 5^5 = 1 mod 11",
      pow(5, 4, P) == (-(1 + 5 + 25 + 125)) % P and pow(5, 5, P) == 1)
check("G1g: second hom e' (zeta->5, t->2) add+mul on 300 random KK pairs",
      all(e_5(kadd(u, v)) == (e_5(u) + e_5(v)) % P
          and e_5(kmul(u, v)) == (e_5(u) * e_5(v)) % P for u, v in pairs))
check("G1g: same conclusion at the second place: e'(-invPhi) = 8, nonsquare",
      e_5(kneg(K_INVPHI)) == 8 and 8 not in squares11)
phibar3 = (-(3**2 + 3**3)) % P
phibar4 = (-(4**2 + 4**3)) % P
check("G1g: at zeta->3 and zeta->4, phi-bar = 8 — a nonsquare, so t has no "
      "image mod 11 there (no c in F11 with c^2 = 8): the hom NEEDS the "
      "split places {9, 5}",
      phibar3 == 8 and phibar4 == 8
      and all((c * c) % P != 8 for c in range(P)))

# ═══════════════════════════════════════════════════════════════════════
#  G2 — THE ORDER ON Z[phi]
# ═══════════════════════════════════════════════════════════════════════
print("── G2: the decide-able order on Z[phi] ─────────────────────────────")


def pos(m, n):
    """m + n*phi > 0, by integer arithmetic.  u = 2m + n, so the value is
    (u + n*sqrt5)/2."""
    u = 2 * m + n
    if n >= 0 and u >= 0:
        return (m, n) != (0, 0)
    if n >= 0:                       # u < 0
        return 5 * n * n > u * u
    if u >= 0:                       # n < 0
        return u * u > 5 * n * n
    return False                     # n < 0 and u < 0


def zp_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def zp_mul(a, b):
    m1, n1 = a
    m2, n2 = b
    return (m1 * m2 + n1 * n2, m1 * n2 + n1 * m2 + n1 * n2)


def zp_neg(a):
    return (-a[0], -a[1])


ZP_PHI = (0, 1)
ZP_INVPHI = (-1, 1)
ZP_ONE = (1, 0)
assert zp_mul(ZP_PHI, ZP_PHI) == zp_add(ZP_PHI, ZP_ONE)     # phi^2 = phi+1
assert zp_mul(ZP_PHI, ZP_INVPHI) == ZP_ONE                  # phi*invPhi = 1

SQRT5 = math.sqrt(5.0)
GOLD = (1.0 + SQRT5) / 2.0

# (a) agreement with floating point on 20000 random pairs, |m|,|n| <= 10^6.
#     Float error here is <= ~|n|*eps ~ 2e-10, far below the 1e-6 flag line,
#     so any |value| >= 1e-6 has a trustworthy float sign.
N_SAMPLES = 20000
BOUND = 10**6
sample = [(random.randint(-BOUND, BOUND), random.randint(-BOUND, BOUND))
          for _ in range(N_SAMPLES)]
flagged = []
disagree = 0
for (m, n) in sample:
    val = m + n * GOLD
    if abs(val) < 1e-6:
        flagged.append((m, n))
        continue
    if (val > 0) != pos(m, n) or (val < 0) != pos(-m, -n):
        disagree += 1
check("G2a: float sign of m + n*(1+sqrt5)/2 agrees with pos on all %d "
      "pairs with |value| >= 1e-6 (0 disagreements)" % (N_SAMPLES - len(flagged)),
      disagree == 0)
# Near-zero pairs get the exact treatment: value = 0 iff 5n^2 = u^2 iff (0,0).
exact_zero_bad = [(m, n) for (m, n) in flagged
                 if 5 * n * n == (2 * m + n)**2 and (m, n) != (0, 0)]
check("G2a: %d pair(s) flagged within 1e-6 of zero; exact check: none is a "
      "true zero except possibly (0,0)" % len(flagged), exact_zero_bad == [])
# The impossibility itself, in two finite certificates:
check("G2a: mod-5 descent step — u^2 = 0 mod 5 iff u = 0 mod 5 "
      "(exhaustive over the 5 residues), so 5n^2 = u^2 forces 5|u, then "
      "25|u^2 = 5n^2 forces 5|n: infinite descent kills any nonzero solution",
      [u for u in range(5) if (u * u) % 5 == 0] == [0])
check("G2a: bounded exhaustive — no nonzero |u|,|n| <= 2000 with 5n^2 = u^2",
      all(5 * n * n != u * u
          for u in range(1, 2001) for n in range(0, 2001)) )
# (the u=0,n!=0 corner: 5n^2 = 0 forces n = 0 — immediate; checked:)
check("G2a: u = 0 corner — 5n^2 = 0 iff n = 0 (n in 1..2000 scanned)",
      all(5 * n * n != 0 for n in range(1, 2001)))

# (b) trichotomy: exactly one of pos(x), x = 0, pos(-x).
tri_sample = sample + [(0, 0)]
check("G2b: trichotomy — exactly one of {pos(x), x=0, pos(-x)} on all %d "
      "sampled pairs incl. (0,0)" % len(tri_sample),
      all(sum([pos(m, n), (m, n) == (0, 0), pos(-m, -n)]) == 1
          for (m, n) in tri_sample))

# (c) closure under + and * on 5000 random positive pairs (by rejection).
positives = []
while len(positives) < 10000:
    m = random.randint(-1000, 1000)
    n = random.randint(-1000, 1000)
    if pos(m, n):
        positives.append((m, n))
pos_pairs = list(zip(positives[:5000], positives[5000:]))
check("G2c: pos closed under addition on 5000 random positive pairs",
      all(pos(*zp_add(x, y)) for x, y in pos_pairs))
check("G2c: pos closed under multiplication on 5000 random positive pairs",
      all(pos(*zp_mul(x, y)) for x, y in pos_pairs))

# (d) receipts.
check("G2d: phi > 0, 1/phi > 0, -phi < 0, -1/phi < 0, 1 > 0",
      pos(0, 1) and pos(-1, 1) and not pos(0, -1) and not pos(1, -1)
      and pos(1, 0))
worlds = [ZP_INVPHI, zp_neg(ZP_PHI)]           # the two pentagon worlds
check("G2d: of the two pentagon worlds p in {invPhi, -phi} exactly one is "
      "positive (it is invPhi)",
      [pos(*w) for w in worlds] == [True, False])

# (e) the fusion matrix [[0,1],[1,1]] over Zp.
ZP_ZERO = (0, 0)
M = [[ZP_ZERO, ZP_ONE], [ZP_ONE, ZP_ONE]]


def mat_apply(M, v):
    return (zp_add(zp_mul(M[0][0], v[0]), zp_mul(M[0][1], v[1])),
            zp_add(zp_mul(M[1][0], v[0]), zp_mul(M[1][1], v[1])))


v_phi = (ZP_ONE, ZP_PHI)
check("G2e: M(1, phi) = phi*(1, phi) exactly in Z[phi]",
      mat_apply(M, v_phi) == (zp_mul(ZP_PHI, v_phi[0]),
                              zp_mul(ZP_PHI, v_phi[1])))
lam2 = zp_neg(ZP_INVPHI)
v_yl = (ZP_ONE, lam2)
check("G2e: M(1, -invPhi) = (-invPhi)*(1, -invPhi) exactly in Z[phi]",
      mat_apply(M, v_yl) == (zp_mul(lam2, v_yl[0]), zp_mul(lam2, v_yl[1])))
# char poly x^2 - x - 1 factors as (x - phi)(x + invPhi): coefficient check.
sum_roots = zp_add(ZP_PHI, lam2)          # phi + (-invPhi) should be 1
prod_roots = zp_mul(ZP_PHI, lam2)         # phi * (-invPhi) should be -1
check("G2e: char poly x^2 - x - 1 = (x - phi)(x - (-invPhi)): root sum = 1, "
      "root product = -1, exact coefficients",
      sum_roots == ZP_ONE and prod_roots == (-1, 0))
# In a domain a monic quadratic has at most two roots; Zp is a domain BECAUSE
# of the order itself (trichotomy + multiplicative closure): nonzero a, b have
# +-a, +-b positive, so +-(a*b) is positive, so a*b != 0.  Corroborated:
nz = [(random.randint(-500, 500), random.randint(-500, 500))
      for _ in range(4000)]
nz = [v for v in nz if v != (0, 0)]
check("G2e: domain-from-order corroborated — %d random nonzero products "
      "are nonzero" % (len(nz) // 2),
      all(zp_mul(a, b) != (0, 0) for a, b in zip(nz[::2], nz[1::2])))
check("G2e: exactly one eigenvalue is positive: pos(phi) and not pos(-invPhi)",
      pos(*ZP_PHI) and not pos(*lam2))
check("G2e: the positive eigenvalue phi and the positive pentagon world "
      "invPhi are exact inverses: phi * invPhi = 1",
      zp_mul(ZP_PHI, ZP_INVPHI) == ZP_ONE)

# (f) the round-5 theorem this design supports, in one sentence:
print("NOTE  G2f: round-5 theorem supported: the fusion matrix [[0,1],[1,1]]"
      " has exactly two eigenvalues in Z[phi] (the roots of"
      " x^2 - x - 1 = (x - phi)(x + 1/phi), at most two because the order"
      " makes Z[phi] a domain), exactly one of them is positive under the"
      " decide-able pos, and the positive one is phi = d_tau —"
      " Perron-Frobenius by decision procedure, no analysis.")

print()
if FAILED:
    print("RESULT: %d check(s) FAILED:" % len(FAILED))
    for f in FAILED:
        print("  - " + f)
    raise SystemExit(1)
print("RESULT: all G1+G2 certificates PASS (exact integer arithmetic; floats "
      "only in the G2a agreement check, by design).")
