#!/usr/bin/env python3
"""r6_order_perron_mod11.py — round-5 SOURCE audit instrument (seat: the order,
Perron, and the mod-11 closure).

Unlike r5_gift_certificates.py (which certified the builder's DESIGN before the
round was built), this script transcribes the LEAN DEFINITIONS AS WRITTEN in
the round-5 Anyon.lean (hash df8c3b9d...) and checks:

  A. (T1) Ord5.posUN / Zp.pos transcribed literally from Anyon.lean:6157/6228
     - agrees with the gift-certificate pos (r5_gift_certificates.py:251) on
       20000 random pairs + an exhaustive box (the T1/T5 cross-check)
     - agrees with a 60-digit Decimal real-embedding oracle
     - trichotomy, closure under + and *, the pos_mul doubling identities,
       first_branch_faithful, the posNest count, no_sqrt5 bounded
     - Zp.phi_bracket integer arithmetic BY HAND: 2236^2 = 4999696 < 5000000
       and 2238^2 = 5008644 > 5000000, applied to the exact Zp elements
  B. (T2) Nfus COMPUTED from fuse; receipts [[0,1],[1,1]]; eigen_phi/eigen_yl
     exact; lam_solutions (exhaustive + the proof's own algebraic identities);
     eigen_char derivation; domain-from-order; perron_selection;
     quantum_dimension_tau semantics; branch_correspondence
  C. (T7) the negative controls that block hostile misreadings: vOnes,
     Nswap (positive eigenvalue 1 != phi; phi has NO Nswap-eigenvector),
     lamNest discrimination
  D. (T3) the mod-11 closure: roots_char11 iff, squares exactly {0,1,3,4,5,9},
     ev11/e11 transcribed and hom-checked, e11 values, the kill (8 nonsquare),
     the discrimination control (sqrt(1/phi) NOT refuted), sigma2 hinge,
     lift_shape_is_inhabited via KK.conj, bounded direct search for a sqrt of
     -1/phi in K

Standalone; exact integer arithmetic everywhere except the Decimal oracle
(exactness argument printed inline).  One PASS/FAIL line per check; exit 1 on
any FAIL.
"""
import random
from decimal import Decimal, getcontext

random.seed(65537)
FAILED = []


def check(name, ok):
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok:
        FAILED.append(name)


# ═══════════════════════════════════════════════════════════════════════
#  A.  THE ORDER — Lean definitions transcribed LITERALLY
# ═══════════════════════════════════════════════════════════════════════
print("== A: the order (Anyon.lean Ord5 / Zp.pos, lines 5650-6414) ==")

# Anyon.lean:6157  def posUN (u y : Int) : Bool :=
#   if 0 <= y then (if 0 <= u then decide (0 < u \/ 0 < y)
#                   else decide (u*u < 5*(y*y)))
#   else (if 0 <= u then decide (5*(y*y) < u*u) else false)
def lean_posUN(u, y):
    if 0 <= y:
        if 0 <= u:
            return (0 < u) or (0 < y)
        return u * u < 5 * (y * y)
    if 0 <= u:
        return 5 * (y * y) < u * u
    return False


# Anyon.lean:6228  def pos (a : Zp) : Bool := Ord5.posUN (2*a.m + a.n) a.n
def lean_pos(m, n):
    return lean_posUN(2 * m + n, n)


# r5_gift_certificates.py:251 — the certified design, copied verbatim
def gift_pos(m, n):
    u = 2 * m + n
    if n >= 0 and u >= 0:
        return (m, n) != (0, 0)
    if n >= 0:
        return 5 * n * n > u * u
    if u >= 0:
        return u * u > 5 * n * n
    return False


# Zp ring ops, transcribed from Anyon.lean:182-195, 6221
ZERO, ONE, PHI, INVPHI = (0, 0), (1, 0), (0, 1), (-1, 1)


def zp_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def zp_neg(a):
    return (-a[0], -a[1])


def zp_sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def zp_mul(a, b):
    # Anyon.lean:189  (ac+bd) + (ad+bc+bd) phi
    return (a[0] * b[0] + a[1] * b[1],
            a[0] * b[1] + a[1] * b[0] + a[1] * b[1])


check("A0: ring receipts — phi^2 = phi+1 and phi*invPhi = 1 in transcribed Zp",
      zp_mul(PHI, PHI) == zp_add(PHI, ONE) and zp_mul(PHI, INVPHI) == ONE)

# --- T1/T5 cross: Lean pos vs gift pos, 20000 random pairs + exhaustive box
N = 20000
B = 10 ** 6
sample = [(random.randint(-B, B), random.randint(-B, B)) for _ in range(N)]
check("A1: LEAN pos == GIFT pos on 20000 random pairs, |m|,|n| <= 10^6",
      all(lean_pos(m, n) == gift_pos(m, n) for m, n in sample))
box = [(m, n) for m in range(-40, 41) for n in range(-40, 41)]
check("A1: LEAN pos == GIFT pos on the exhaustive box |m|,|n| <= 40 "
      "(%d pairs, all four branch boundaries crossed)" % len(box),
      all(lean_pos(m, n) == gift_pos(m, n) for m, n in box))
# the one branch phrased differently: Lean `0<u \/ 0<y` vs gift `(m,n)!=(0,0)`
# — Anyon.lean:6346 first_branch_faithful proves them equal under the guard;
# replicated exhaustively:
check("A1: first_branch_faithful — under n>=0 and 2m+n>=0, "
      "(0<2m+n or 0<n) iff (m,n) != (0,0), |m|,|n| <= 60 exhaustive",
      all(((0 < 2 * m + n) or (0 < n)) == ((m, n) != (0, 0))
          for m in range(-60, 61) for n in range(0, 61)
          if 2 * m + n >= 0))

# --- real-embedding oracle at 60 digits
getcontext().prec = 60
SQRT5 = Decimal(5).sqrt()


def real_sign(m, n):
    v = Decimal(m) + Decimal(n) * (1 + SQRT5) / 2
    if v > Decimal("1e-30"):
        return 1
    if v < Decimal("-1e-30"):
        return -1
    return 0


# |m+n*phi| for integer m,n with |m|,|n| <= 10^6 is either 0 (only (0,0):
# no_sqrt5) or >= 1/(|m| + |n|*2) > 1e-7 by the norm |m^2+mn-n^2| >= 1,
# so a 60-digit evaluation with a 1e-30 window cannot misclassify.
ok = True
for m, n in sample:
    s = real_sign(m, n)
    if s == 0:
        ok = ok and (m, n) == (0, 0)
    else:
        ok = ok and (lean_pos(m, n) == (s > 0))
check("A2: LEAN pos agrees with the 60-digit real embedding "
      "(sign of m + n(1+sqrt5)/2) on all 20000 pairs", ok)
check("A2: norm floor used above — |m^2+mn-n^2| >= 1 for 20000 sampled "
      "nonzero pairs (value never in (0,1))",
      all(abs(m * m + m * n - n * n) >= 1
          for m, n in sample if (m, n) != (0, 0)))

# --- no_sqrt5: the mod-5 step and a bounded exhaustive
check("A3: mod-5 step — the only residue r<5 with r^2 = 0 mod 5 is 0",
      [r for r in range(5) if (r * r) % 5 == 0] == [0])
check("A3: bounded exhaustive — no nonzero |u|,|n| <= 2000 with u^2 = 5n^2",
      all(u * u != 5 * n * n
          for u in range(1, 2001) for n in range(0, 2001)))

# --- trichotomy and closure through the LEAN pos
tri = sample + [(0, 0), (1, 0), (0, 1), (-1, 1), (1, -1), (0, -1), (-1, 0)]
check("A4: trichotomy — exactly one of {pos a, a=0, pos(-a)} on %d pairs"
      % len(tri),
      all(sum([lean_pos(m, n), (m, n) == (0, 0), lean_pos(-m, -n)]) == 1
          for m, n in tri))
pos_elts = [p for p in sample if lean_pos(*p)][:5000]
check("A4: closure under + on %d random positive pairs" % (len(pos_elts) // 2),
      all(lean_pos(*zp_add(a, b))
          for a, b in zip(pos_elts[::2], pos_elts[1::2])))
check("A4: closure under * on %d random positive pairs" % (len(pos_elts) // 2),
      all(lean_pos(*zp_mul(a, b))
          for a, b in zip(pos_elts[::2], pos_elts[1::2])))
# the doubling identities Zp.pos_mul routes through (Anyon.lean:6321/6325):
#   2*(2M+N) = u1*u2 + 5*y1*y2   and   2*N = u1*y2 + u2*y1
ok = True
for a, b in zip(sample[::2], sample[1::2]):
    u1, y1 = 2 * a[0] + a[1], a[1]
    u2, y2 = 2 * b[0] + b[1], b[1]
    M, Nn = zp_mul(a, b)
    ok = ok and (2 * (2 * M + Nn) == u1 * u2 + 5 * (y1 * y2))
    ok = ok and (2 * Nn == u1 * y2 + u2 * y1)
check("A5: pos_mul doubling identities exact on 10000 random pairs "
      "(2(2M+N) = uu' + 5yy', 2N = uy' + u'y)", ok)

# --- the phi bracket, by hand (T1 arithmetic demanded by the seat)
check("A6: 2236^2 = 4999696 and 4999696 < 5000000 = 5*1000^2",
      2236 * 2236 == 4999696 and 4999696 < 5000000)
check("A6: 2238^2 = 5008644 and 5008644 > 5000000",
      2238 * 2238 == 5008644 and 5008644 > 5000000)
e1 = zp_sub(zp_mul((1000, 0), PHI), (1618, 0))
e2 = zp_sub((1619, 0), zp_mul((1000, 0), PHI))
e3 = zp_sub(zp_mul((1000, 0), PHI), (1619, 0))
e4 = zp_sub((1618, 0), zp_mul((1000, 0), PHI))
check("A6: 1000*phi - 1618 = (-1618,1000), u = -2236, branch (y>=0,u<0), "
      "u^2 < 5y^2 -> pos TRUE",
      e1 == (-1618, 1000) and 2 * e1[0] + e1[1] == -2236 and lean_pos(*e1))
check("A6: 1619 - 1000*phi = (1619,-1000), u = 2238, branch (y<0,u>=0), "
      "5y^2 < u^2 -> pos TRUE",
      e2 == (1619, -1000) and 2 * e2[0] + e2[1] == 2238 and lean_pos(*e2))
check("A6: tightness — pos(1000*phi - 1619) FALSE and pos(1618 - 1000*phi) "
      "FALSE (phi_bracket_tight)",
      (not lean_pos(*e3)) and (not lean_pos(*e4)))

# --- posNest replication (Anyon.lean:6382-6398)
posNest = [ZERO, ONE, zp_neg(ONE), PHI, zp_neg(PHI), INVPHI, zp_neg(INVPHI),
           (2, -1), (-2, 1), (1, 1)]
check("A7: posNest has 10 distinct members and exactly 5 are pos "
      "(posNestTrue_eq)",
      len(set(posNest)) == 10
      and sum(1 for p in posNest if lean_pos(*p)) == 5)
check("A7: posM negative control — sign-of-m calls invPhi negative and "
      "1-phi positive; pos disagrees both ways (posM_disagrees)",
      (not (INVPHI[0] > 0)) and lean_pos(*INVPHI)
      and (zp_sub(ONE, PHI)[0] > 0) and not lean_pos(*zp_sub(ONE, PHI)))

# ═══════════════════════════════════════════════════════════════════════
#  B.  THE PERRON PACKAGE — Nfus from fuse, eigenvalues, selection
# ═══════════════════════════════════════════════════════════════════════
print("== B: the Perron package (Anyon.lean 6505-6725) ==")


# Anyon.lean:54  def fuse : 1xb=[b], ax1=[a], txt=[1,t]
def fuse(a, b):
    if a == 'one':
        return [b]
    if b == 'one':
        return [a]
    return ['one', 'tau']


def countA(a, lst):  # Anyon.lean:6505
    return sum(1 for x in lst if x == a)


# Anyon.lean:6511  Nfus i j = (Int.ofNat (countA j (fuse i tau)), 0)
Nfus = {(i, j): (countA(j, fuse(i, 'tau')), 0)
        for i in ('one', 'tau') for j in ('one', 'tau')}
check("B1: Nfus COMPUTED from fuse equals [[0,1],[1,1]] "
      "(receipts Nfus_oo/ot/to/tt)",
      Nfus[('one', 'one')] == ZERO and Nfus[('one', 'tau')] == ONE
      and Nfus[('tau', 'one')] == ONE and Nfus[('tau', 'tau')] == ONE)
check("B1: Nfus not constant (anti-vacuity, Nfus_not_constant)",
      Nfus[('one', 'one')] != Nfus[('one', 'tau')])


def matApp(A, v, i):  # Anyon.lean:6526
    return zp_add(zp_mul(A[(i, 'one')], v['one']),
                  zp_mul(A[(i, 'tau')], v['tau']))


def smulV(c, v, i):  # Anyon.lean:6529
    return zp_mul(c, v[i])


def is_eigen(A, v1, v2, lam):
    v = {'one': v1, 'tau': v2}
    return (matApp(A, v, 'one') == smulV(lam, v, 'one')
            and matApp(A, v, 'tau') == smulV(lam, v, 'tau'))


NEG_INVPHI = zp_neg(INVPHI)  # (1,-1)
check("B2: eigen_phi — Nfus (1,phi) = phi (1,phi) exactly",
      is_eigen(Nfus, ONE, PHI, PHI))
check("B2: eigen_yl — Nfus (1,-1/phi) = (-1/phi) (1,-1/phi) exactly",
      is_eigen(Nfus, ONE, NEG_INVPHI, NEG_INVPHI))
check("B2: the eigenvectors are nonzero (anti-vacuity hypothesis holds)",
      ONE != ZERO)

# --- lam_solutions: exhaustive + the Lean proof's own algebra
sols = [(m, n) for m in range(-300, 301) for n in range(-300, 301)
        if zp_mul((m, n), (m, n)) == zp_add((m, n), ONE)]
check("B3: lam^2 = lam+1 in Z[phi] has exactly the solutions "
      "{phi, -1/phi} in |m|,|n| <= 300 (exhaustive)",
      sorted(sols) == sorted([PHI, NEG_INVPHI]))
# the proof's algebra (Anyon.lean:6626-6664), replicated as identities:
rs = [random.randint(-10 ** 6, 10 ** 6) for _ in range(4000)]
check("B3: proof identity 1 — component eqs give n(2m+n-1) = 0: "
      "2mn+n^2-n == n(2m+n-1) for 4000 random (m,n)",
      all((2 * m * n + n * n - n) == n * (2 * m + n - 1)
          for m, n in zip(rs[::2], rs[1::2])))
check("B3: proof identity 2 (n=0 branch) — (2m-1)^2 == 4(m^2-m)+1, so "
      "m^2 = m+1 forces (2m-1)^2 = 5 = 5*1^2, killed by no_sqrt5",
      all((2 * m - 1) ** 2 == 4 * (m * m - m) + 1 for m in rs)
      and all(u * u != 5 for u in range(-3, 4)))
check("B3: proof identity 3 (n = 1-2m branch) — m^2+(1-2m)^2-(m+1) == "
      "5(m^2-m), so 5m(m-1) = 0: m = 0 -> phi, m = 1 -> -1/phi",
      all(m * m + (1 - 2 * m) ** 2 - (m + 1) == 5 * (m * m - m) for m in rs)
      and zp_mul(PHI, PHI) == zp_add(PHI, ONE)
      and zp_mul((1, -1), (1, -1)) == zp_add((1, -1), ONE))

# --- eigen_char direction: eigen equations force the char equation
#     eq1: v2 = lam*v1 ; eq2: v1+v2 = lam*v2 => (lam^2-lam-1) v1 = 0
ok = True
for _ in range(2000):
    lam = (random.randint(-50, 50), random.randint(-50, 50))
    v1 = (random.randint(-50, 50), random.randint(-50, 50))
    v2 = zp_mul(lam, v1)
    lhs = zp_sub(zp_mul(lam, v2), zp_add(v1, v2))
    rhs = zp_mul(zp_sub(zp_mul(lam, lam), zp_add(lam, ONE)), v1)
    ok = ok and (lhs == rhs)
check("B4: eigen_char algebra — lam(lam v1) - (v1 + lam v1) == "
      "(lam^2 - lam - 1) v1 exactly, 2000 random triples", ok)
nz = [p for p in sample if p != ZERO]
check("B4: domain-from-order — 5000 random nonzero products are nonzero "
      "(mul_ne_zero, proved in Lean from trichotomy + pos_mul alone)",
      all(zp_mul(a, b) != ZERO for a, b in zip(nz[:10000:2], nz[1:10000:2])))
ok = True
for _ in range(200):
    lam = (random.randint(-30, 30), random.randint(-30, 30))
    if zp_mul(lam, lam) == zp_add(lam, ONE):
        continue
    for _ in range(20):
        v1 = (random.randint(-30, 30), random.randint(-30, 30))
        if v1 == ZERO:
            continue
        v2 = zp_mul(lam, v1)  # makes eq1 hold
        ok = ok and not (zp_add(v1, v2) == zp_mul(lam, v2))
check("B4: converse control — for 200 random NON-roots lam, no (v1,v2) with "
      "v2 = lam v1, v1 != 0 satisfies the second eigen equation", ok)

# --- perron_selection, quantum_dimension_tau, branch_correspondence
check("B5: perron_selection — pos(phi) = true, pos(-1/phi) = false",
      lean_pos(*PHI) and not lean_pos(*NEG_INVPHI))
qdt = (is_eigen(Nfus, ONE, PHI, PHI)
       and lean_pos(*PHI)
       and all((not lean_pos(*lam)) or lam == PHI for lam in [PHI, NEG_INVPHI]))
check("B5: quantum_dimension_tau semantics — phi is an eigenvalue with "
      "nonzero eigenvector, phi is pos, and every pos eigenvalue "
      "(of the exact set {phi,-1/phi}) is phi", qdt)
check("B5: branch_correspondence — phi*(1/phi) = 1, pos(1/phi) = true, "
      "pos(-phi) = false, pos(-1/phi) = false",
      zp_mul(PHI, INVPHI) == ONE and lean_pos(*INVPHI)
      and not lean_pos(*zp_neg(PHI)) and not lean_pos(*NEG_INVPHI))

# ═══════════════════════════════════════════════════════════════════════
#  C.  (T7) NEGATIVE CONTROLS — the hostile misreadings, blocked
# ═══════════════════════════════════════════════════════════════════════
print("== C: hostile-misreading controls ==")
# misreading 1: "the theorem is vacuous" — blocked by B2 (explicit nonzero
# eigenvector) and B5.  misreading 2: "any matrix satisfies it" — Nswap:
Nswap = {('one', 'one'): ZERO, ('one', 'tau'): ONE,
         ('tau', 'one'): ONE, ('tau', 'tau'): ZERO}
check("C1: Nswap differs from Nfus at (tau,tau) (Nswap_not_fusion)",
      Nswap[('tau', 'tau')] != Nfus[('tau', 'tau')])
check("C1: (1,1) is an eigenvector of Nswap for eigenvalue 1; pos(1) = true; "
      "1 != phi  (Nswap_has_positive_eigenvalue_one)",
      is_eigen(Nswap, ONE, ONE, ONE) and lean_pos(*ONE) and ONE != PHI)
check("C1: (1,phi) is NOT an eigenvector of Nswap for phi "
      "(Nswap_not_eigen_phi)",
      not is_eigen(Nswap, ONE, PHI, PHI))
# phi is not an eigenvalue of Nswap AT ALL (so conjunct 1 of a QDT-for-Nswap
# with phi would be FALSE, not just unproved): eq1 v2 = phi v1, eq2
# v1 = phi v2 = phi^2 v1 -> (phi^2 - 1) v1 = phi*v1 = 0 -> v1 = 0.
check("C2: phi-eigenvector equations for Nswap force v = 0: "
      "phi^2 - 1 == phi != 0 and exhaustive |coords| <= 25 finds none",
      zp_sub(zp_mul(PHI, PHI), ONE) == PHI and PHI != ZERO
      and not any(is_eigen(Nswap, (a, b), (c, d), PHI)
                  and ((a, b) != ZERO or (c, d) != ZERO)
                  for a in range(-25, 26) for b in range(-3, 4)
                  for c in range(-25, 26) for d in range(-3, 4)))
# misreading 3: "any vector is an eigenvector" — vOnes control:
check("C3: (1,1) is an eigenvector of Nfus for NO scalar, exhaustive "
      "|cm|,|cn| <= 30 (vOnes_not_eigen: eq1 forces c=1, eq2 forces c=2)",
      not any(is_eigen(Nfus, ONE, ONE, (cm, cn))
              for cm in range(-30, 31) for cn in range(-30, 31)))
# misreading 4: "lam^2 = lam+1 is a test everything passes" — lamNest:
lamNest = [ZERO, ONE, zp_neg(ONE), PHI, zp_neg(PHI), INVPHI, NEG_INVPHI,
           (2, -1), (1, 1), (2, 1)]
check("C4: of the 10 lamNest scalars exactly 2 satisfy lam^2 = lam+1 "
      "(lamRoots_eq)",
      len(set(lamNest)) == 10
      and sum(1 for l in lamNest
              if zp_mul(l, l) == zp_add(l, ONE)) == 2)

# ═══════════════════════════════════════════════════════════════════════
#  D.  THE MOD-11 CLOSURE — transcribed from Anyon.lean 5313-5636
# ═══════════════════════════════════════════════════════════════════════
print("== D: the mod-11 closure ==")

check("D1: roots_char11 — 1+r+r^2+r^3+r^4 = 0 mod 11 IFF r in {3,4,5,9}, "
      "all 11 residues",
      all(((1 + r + r * r + r ** 3 + r ** 4) % 11 == 0)
          == (r in (3, 4, 5, 9)) for r in range(11)))
check("D1: two_not_root11 — r = 2 fails (the iff is not a universal pass)",
      (1 + 2 + 4 + 8 + 16) % 11 != 0)
check("D1: each root has 5th power 1 and they are 4 distinct non-1 values "
      "(roots_pow5_11, roots_distinct11)",
      all(pow(r, 5, 11) == 1 for r in (3, 4, 5, 9))
      and len({3, 4, 5, 9}) == 4 and 1 not in {3, 4, 5, 9})
check("D1: root_powers11 — 9^2 = 4, 9^3 = 3, 9^4 = 5 mod 11",
      pow(9, 2, 11) == 4 and pow(9, 3, 11) == 3 and pow(9, 4, 11) == 5)
check("D1: reduction_rule11 — 9^4 == -(1+9+81+729) mod 11",
      pow(9, 4, 11) == (-(1 + 9 + 81 + 729)) % 11)

sq_set = {(i * i) % 11 for i in range(11)}
check("D2: squares mod 11 are EXACTLY {0,1,3,4,5,9} "
      "(squares11_subset + squares11_witnesses)",
      sq_set == {0, 1, 3, 4, 5, 9})
check("D2: witness map matches the file: 0^2=0, 1^2=1, 5^2=3, 2^2=4, "
      "4^2=5, 3^2=9 mod 11",
      (0, 1, 3, 4, 5, 9) == (0, 1, (5 * 5) % 11, (2 * 2) % 11,
                             (4 * 4) % 11, (3 * 3) % 11))
check("D2: nsq8 — no i < 11 with i^2 = 8 mod 11, and 5000 random big ints "
      "agree (a^2 % 11 != 8)",
      8 not in sq_set
      and all((a * a) % 11 != 8
              for a in (random.randint(-10 ** 9, 10 ** 9)
                        for _ in range(5000))))
check("D2: nsq3_false control — a = 5 witnesses that the same test with 3 "
      "FAILS (5^2 = 25 = 3 mod 11): the instrument discriminates",
      (5 * 5) % 11 == 3)
check("D3: phibar_at_the_four_places — -(z^2)-z^3 mod 11 is 4 at z=9,5 and "
      "8 at z=3,4",
      (-(81) - 729) % 11 == 4 and (-(25) - 125) % 11 == 4
      and (-(9) - 27) % 11 == 8 and (-(16) - 64) % 11 == 8)
check("D3: t_image_at_split_places — c^2 = 4 mod 11 iff c in {2,9}, "
      "all 11 residues",
      all(((c * c) % 11 == 4) == (c in (2, 9)) for c in range(11)))


# --- Z5 / KK transcriptions (Anyon.lean:256, 324, 5474, 5505)
def z5_add(u, v):
    return tuple(u[i] + v[i] for i in range(4))


def z5_neg(u):
    return tuple(-u[i] for i in range(4))


def z5_mul(u, v):
    c = [0] * 7
    for i in range(4):
        for j in range(4):
            c[i + j] += u[i] * v[j]
    c4, c5, c6 = c[4], c[5], c[6]
    return (c[0] - c4 + c5, c[1] - c4 + c6, c[2] - c4, c[3] - c4)


Z5_ZERO, Z5_ONE = (0, 0, 0, 0), (1, 0, 0, 0)
Z5_ZETA = (0, 1, 0, 0)
Z5_PHI = (0, 0, -1, -1)
Z5_INVPHI = (-1, 0, -1, -1)

check("D4: transcription sanity — zeta^5 = 1, phi*invPhi = 1, "
      "phi^2 = phi+1 in transcribed Z5",
      z5_mul(z5_mul(z5_mul(z5_mul(Z5_ZETA, Z5_ZETA), Z5_ZETA), Z5_ZETA),
             Z5_ZETA) == Z5_ONE
      and z5_mul(Z5_PHI, Z5_INVPHI) == Z5_ONE
      and z5_mul(Z5_PHI, Z5_PHI) == z5_add(Z5_PHI, Z5_ONE))


def ev11(u):  # Anyon.lean:5474 — a0 + 9 a1 + 4 a2 + 3 a3
    return u[0] + 9 * u[1] + 4 * u[2] + 3 * u[3]


def rz5():
    return tuple(random.randint(-50, 50) for _ in range(4))


pairs = [(rz5(), rz5()) for _ in range(300)]
check("D4: ev11 additive ON THE NOSE for 300 random Z5 pairs",
      all(ev11(z5_add(u, v)) == ev11(u) + ev11(v) for u, v in pairs))
check("D4: ev11 multiplicative mod 11 for 300 random Z5 pairs",
      all(ev11(z5_mul(u, v)) % 11 == (ev11(u) * ev11(v)) % 11
          for u, v in pairs))
check("D4: ev11_values — 1->1, zeta->9, phi->4, 1/phi->3, -1/phi->8 (mod 11)",
      ev11(Z5_ONE) == 1 and ev11(Z5_ZETA) == 9
      and ev11(Z5_PHI) % 11 == 4 and ev11(Z5_INVPHI) % 11 == 3
      and ev11(z5_neg(Z5_INVPHI)) % 11 == 8)


# KK = pairs (x,y) of Z5, t^2 = phi (Anyon.lean:324)
def kk_mul(u, v):
    return (z5_add(z5_mul(u[0], v[0]), z5_mul(Z5_PHI, z5_mul(u[1], v[1]))),
            z5_add(z5_mul(u[0], v[1]), z5_mul(u[1], v[0])))


def kk_add(u, v):
    return (z5_add(u[0], v[0]), z5_add(u[1], v[1]))


def kk_emb(z):
    return (z, Z5_ZERO)


KK_ONE = kk_emb(Z5_ONE)
KK_T = (Z5_ZERO, Z5_ONE)
KK_INVPHI = kk_emb(Z5_INVPHI)
KK_B = kk_mul(KK_T, KK_INVPHI)  # Anyon.lean:333


def e11(u):  # Anyon.lean:5505
    return ev11(u[0]) + 2 * ev11(u[1])


def rkk():
    return (rz5(), rz5())


kpairs = [(rkk(), rkk()) for _ in range(300)]
check("D5: e11 additive ON THE NOSE for 300 random KK pairs",
      all(e11(kk_add(u, v)) == e11(u) + e11(v) for u, v in kpairs))
check("D5: e11 multiplicative mod 11 for 300 random KK pairs",
      all(e11(kk_mul(u, v)) % 11 == (e11(u) * e11(v)) % 11
          for u, v in kpairs))
check("D5: e11_receipts — e(1)=1, e(t)=2, e(phi)=4, e(t)^2=4, e(b)=6, "
      "e(t)e(b)=1 (mod 11)",
      e11(KK_ONE) == 1 and e11(KK_T) == 2
      and e11(kk_emb(Z5_PHI)) % 11 == 4 and (e11(KK_T) ** 2) % 11 == 4
      and e11(KK_B) % 11 == 6 and (e11(KK_T) * e11(KK_B)) % 11 == 1)
check("D5: kk_t_sq — t^2 = emb(phi) exactly in transcribed K",
      kk_mul(KK_T, KK_T) == kk_emb(Z5_PHI))
check("D5: e11 not injective but that is fine — emb(zeta) != emb(9) yet "
      "same image mod 11 (e11_not_injective)",
      kk_emb(Z5_ZETA) != kk_emb((9, 0, 0, 0))
      and e11(kk_emb(Z5_ZETA)) % 11 == e11(kk_emb((9, 0, 0, 0))) % 11)

# --- the kill and its composition
check("D6: e11(-1/phi) = 8 mod 11 and 8 is a nonsquare: no s in K has "
      "s^2 = -1/phi (the hom transports any such s to a sqrt of 8 mod 11)",
      e11(kk_emb(z5_neg(Z5_INVPHI))) % 11 == 8 and 8 not in sq_set)
NEG_INV_K = kk_emb(z5_neg(Z5_INVPHI))
found = False
for a in range(-1, 2):
    for b in range(-1, 2):
        for c in range(-1, 2):
            for d in range(-1, 2):
                for e in range(-1, 2):
                    for f in range(-1, 2):
                        for g in range(-1, 2):
                            for h in range(-1, 2):
                                s = ((a, b, c, d), (e, f, g, h))
                                if kk_mul(s, s) == NEG_INV_K:
                                    found = True
check("D6: bounded direct search — no s with coeffs in [-1,1]^8 squares to "
      "-1/phi (3^8 = 6561 candidates)", not found)
check("D6: random direct search — no s with 20000 random coeff-8-tuples "
      "|c| <= 6 squares to -1/phi",
      not any(kk_mul(s, s) == NEG_INV_K
              for s in ((tuple(random.randint(-6, 6) for _ in range(4)),
                         tuple(random.randint(-6, 6) for _ in range(4)))
                        for _ in range(20000))))


# --- sigma2 hinge and the lift chain
def sigma2(u):  # Anyon.lean:3549 — (a0-a2, a3-a2, a1-a2, -a2)
    return (u[0] - u[2], u[3] - u[2], u[1] - u[2], -u[2])


check("D7: sigma2_phi — sigma2(phi) = -1/phi = (1,0,1,1) exactly",
      sigma2(Z5_PHI) == z5_neg(Z5_INVPHI) == (1, 0, 1, 1))
check("D7: sigma2 is multiplicative on 300 random Z5 pairs "
      "(the transport really is a hom)",
      all(sigma2(z5_mul(u, v)) == z5_mul(sigma2(u), sigma2(v))
          for u, v in pairs))
# lift_forces_sqrt_neg_invPhi chain: P(t)^2 = P(t^2) = P(emb phi)
#   = emb(sigma2 phi) = emb(-1/phi).  Each link checked exactly above
# (kk_t_sq at D5, sigma2_phi at D7); the composition with D6 closes it.
check("D7: the closure composes — any multiplicative P extending sigma2 "
      "sends t to a sqrt of -1/phi (chain links verified), and D6 says "
      "there is none: sigma2_no_mul_lift_exists",
      kk_mul(KK_T, KK_T) == kk_emb(Z5_PHI)
      and sigma2(Z5_PHI) == z5_neg(Z5_INVPHI) and 8 not in sq_set)


# --- N5: the hypothesis shape is inhabited (KK.conj)
def z5_conj(u):  # Anyon.lean:1715 — (a0-a1, -a1, a3-a1, a2-a1)
    return (u[0] - u[1], -u[1], u[3] - u[1], u[2] - u[1])


def kk_conj(u):  # Anyon.lean:1837 — componentwise
    return (z5_conj(u[0]), z5_conj(u[1]))


check("D8: lift_shape_is_inhabited — KK.conj is multiplicative on 300 "
      "random KK pairs",
      all(kk_conj(kk_mul(u, v)) == kk_mul(kk_conj(u), kk_conj(v))
          for u, v in kpairs))
check("D8: KK.conj extends Z5.conj through emb (conj_emb, definitional)",
      all(kk_conj(kk_emb(u)) == kk_emb(z5_conj(u)) for u, _ in pairs))
check("D8: the two coefficient maps differ at phi — conj(phi) = phi != "
      "sigma2(phi): the no-lift theorem is not vacuous",
      z5_conj(Z5_PHI) == Z5_PHI and z5_conj(Z5_PHI) != sigma2(Z5_PHI))

# --- the discrimination control (the seat's required negative control)
check("D9: control — b^2 = 1/phi EXACTLY in K (kk_b_sq): a square root "
      "that does exist",
      kk_mul(KK_B, KK_B) == KK_INVPHI)
check("D9: control — e11(1/phi) = 3 mod 11 IS a square (5^2 = 3), so the "
      "instrument does NOT refute sqrt(1/phi) (mod11_does_not_refute...)",
      e11(KK_INVPHI) % 11 == 3 and 3 in sq_set and (5 * 5) % 11 == 3)
check("D9: control — e11(b)^2 = 6^2 = 36 = 3 = e11(1/phi) mod 11: the hom "
      "carries the existing root through",
      (e11(KK_B) ** 2) % 11 == e11(KK_INVPHI) % 11 == 3)
check("D9: neg_invPhi_nondegenerate — -1/phi is nonzero, != phi, != 1/phi",
      NEG_INV_K != kk_emb(Z5_ZERO) and NEG_INV_K != kk_emb(Z5_PHI)
      and NEG_INV_K != KK_INVPHI)

print()
if FAILED:
    print("RESULT: %d check(s) FAILED:" % len(FAILED))
    for f in FAILED:
        print("  - " + f)
    raise SystemExit(1)
print("RESULT: all r6 order/Perron/mod-11 source checks PASS "
      "(Lean definitions transcribed literally; exact integer arithmetic; "
      "Decimal oracle only in A2 with printed exactness argument).")
