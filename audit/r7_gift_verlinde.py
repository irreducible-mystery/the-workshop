#!/usr/bin/env python3
"""r7_gift_verlinde.py — round-7 GIFT certification: Verlinde — the theater
computes its own occupancy.

CANDIDATE (seat): formalize the Fibonacci modular data and prove the fusion
rules are RE-DERIVED from the S-matrix — grammar -> braiding -> dimension ->
back to grammar, with d_tau = S_0tau/S_00 tying to round 5's
quantum_dimension_tau (Anyon.lean 6737).

BENCH GROUND TRUTH (conventions): workshop/modular_data.py ("Bench 7, THE
IDENTITY CARD"): PHI = (1+sqrt5)/2, D = sqrt(1+PHI^2), DIMS = (1, phi),
THETA = (1, e^{-4 pi i/5}) i.e. theta_tau = zeta5^3 ("our chirality"),
S = (1/D)[[1,phi],[phi,-1]], (ST)^3 = lambda S^2 with lambda = p+/D and
c = -14/5 (mod 8); Verlinde N_ab^c = sum_x S_ax S_bx S*_cx / S_0x.
Twist provenance: workshop/grammar_hexagon.py line 148: theta_t = r1/phi + rt,
asserted equal to e^{-4 pi i/5} = zeta5^3.

EXACT ARITHMETIC in every load-bearing check (int / Fraction).  Floats appear
only as clearly-labelled non-load-bearing sanity prints and in the W6 bench
co-sign (the bench itself is float; the co-sign compares its floats to the
exact values).

TRANSCRIPTIONS (verbatim from the tree, sources named per house norm):
  Zp  (Z[phi] pairs, mul (m1m2+n1n2, m1n2+n1m2+n1n2))  Anyon.lean 175-197
  Z5  (Z[zeta5] 4-tuples, reduction c-vector)           Anyon.lean 240-279
  Z5.conj (zeta -> zeta^4)                              Anyon.lean 1732
  fuse / countA                                         Anyon.lean 54-57, 6545
  quadratic-pair pattern (radicand as one constant):
    KK = Z5 pairs, t^2 = phi                            Anyon.lean 303-315
    Ep = Zp pairs, s^2 = phi                            Rigidity.lean 2107-2126

RING TOWER built here (all exact):
  Q5  = Q(sqrt5) as Fraction pairs a + b*sqrt5
  QD  = Q5(D) as pairs x + y*D with D^2 = phi + 2      (the THIRD radicand)
  C20 = Z[zeta20] as int 8-vectors mod Phi20 = x^8 - x^6 + x^4 - x^2 + 1

Sections: W1 ring, W2 S-matrix, W3 dims-from-S, W4 Verlinde (+ the cleared
Z[phi] form a Lean `decide` would check), W5 T-layer and modular relation
costed, W6 bench co-sign, W7 calibration measurements on the tree.
"""
import sys, os, random, cmath
from fractions import Fraction as Fr
from math import isqrt, pi

random.seed(20260723)
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, ".."))
WORKSHOP = os.path.normpath(os.path.join(HERE, "..", ".."))

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def info(msg):
    print(f"      {msg}")

def is_rational_square(q):
    """Exact: q in Q is a square in Q iff num and den (lowest terms) are
    perfect squares and q >= 0."""
    if q < 0: return False
    n, d = q.numerator, q.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d

# ======================================================================
# W1 — THE RING.  Q5 = Q(sqrt5), QD = Q5(D) with D^2 = phi+2.
# ======================================================================
print("=" * 72)
print("W1 — the ring: D^2 = phi+2 = sqrt5*phi; QD = Q(sqrt5)(D), third radicand")
print("=" * 72)

class Q5:
    """a + b*sqrt5, a,b in Q (Fraction)."""
    __slots__ = ('a', 'b')
    def __init__(self, a=0, b=0): self.a = Fr(a); self.b = Fr(b)
    def __add__(self, o): return Q5(self.a + o.a, self.b + o.b)
    def __sub__(self, o): return Q5(self.a - o.a, self.b - o.b)
    def __neg__(self):    return Q5(-self.a, -self.b)
    def __mul__(self, o):
        if isinstance(o, int): o = Q5(o)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__
    def __eq__(self, o):  return self.a == o.a and self.b == o.b
    def is_zero(self):    return self.a == 0 and self.b == 0
    def norm(self):       return self.a * self.a - 5 * self.b * self.b   # to Q
    def inv(self):
        n = self.norm()
        return Q5(self.a / n, -self.b / n)
    def fl(self):         return float(self.a) + float(self.b) * 5 ** 0.5
    def __repr__(self):
        return f"({self.a}{'+' if self.b >= 0 else ''}{self.b}*sqrt5)"

PHI5   = Q5(Fr(1, 2), Fr(1, 2))          # phi
SQRT5  = Q5(0, 1)
R_GOOD = PHI5 + Q5(2)                    # phi + 2, the radicand for D

# W1a: phi^2 = phi+1 in Q5 (the ring is the right one)
check("W1a_phi_sq", PHI5 * PHI5 == PHI5 + Q5(1), "phi^2 = phi+1 in Q(sqrt5)")

# W1b: the pretty identity phi+2 = sqrt5*phi, in Q5 AND in Zp = Z[phi] pairs
zp_mul = lambda u, v: (u[0]*v[0] + u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])
zp_add = lambda u, v: (u[0]+v[0], u[1]+v[1])
ZP_PHI, ZP_ONE, ZP_SQRT5 = (0, 1), (1, 0), (-1, 2)     # sqrt5 = 2phi-1
ZP_PHIP2 = (2, 1)                                        # phi+2
check("W1b_pretty_identity",
      SQRT5 * PHI5 == R_GOOD and zp_mul(ZP_SQRT5, ZP_PHI) == ZP_PHIP2,
      "phi+2 = sqrt5*phi holds in Q(sqrt5) AND as Z[phi] pairs "
      "(2phi-1)*phi = (2,1) — a Zp `decide` [Zp mul verbatim Anyon.lean 189]")

# W1c: phi+2 is NOT a square in Q(sqrt5): N(phi+2) = 5, not a rational square.
n_r = R_GOOD.norm()
check("W1c_radicand_not_square",
      n_r == 5 and not is_rational_square(Fr(5)),
      f"N_(Q5/Q)(phi+2) = {n_r}; a square in Q5 has square norm; 5 is not "
      "a rational square => x^2 = phi+2 has no root in Q(sqrt5)")

# W1d: the third radicand is genuinely third: D not in E = Q(sqrt5)(sqrt(phi)).
#  z = x + y*sqrt(phi), z^2 = (x^2+phi y^2) + 2xy sqrt(phi) = phi+2 forces
#  xy = 0.  Branch y=0: x^2 = phi+2, killed by W1c.  Branch x=0:
#  y^2 = (phi+2)/phi = sqrt5 (exact division below), and N(sqrt5) = -5 < 0
#  while N(y^2) = N(y)^2 >= 0 in Q — impossible.
quot = R_GOOD * PHI5.inv()
check("W1d_D_not_in_E",
      quot == SQRT5 and SQRT5.norm() == -5,
      "(phi+2)/phi = sqrt5 exactly; N(sqrt5) = -5 < 0 = impossible for N(y)^2; "
      "with W1c both branches die => sqrt(phi+2) is not in Q(sqrt5)(sqrt(phi)): "
      "a genuinely NEW quadratic layer (third radicand after t^2=phi [KK], "
      "s^2=phi [Ep])")

class QD:
    """x + y*D over Q5, D^2 = RAD (class variable — wrong-radicand control
    swaps it).  Same two-layer pair pattern as KK (Anyon.lean 303) and Ep
    (Rigidity.lean 2107): the radicand is one constant in `mul`."""
    RAD = R_GOOD
    __slots__ = ('x', 'y')
    def __init__(self, x=None, y=None):
        self.x = x if isinstance(x, Q5) else Q5(0 if x is None else x)
        self.y = y if isinstance(y, Q5) else Q5(0 if y is None else y)
    def __add__(self, o): return type(self)(self.x + o.x, self.y + o.y)
    def __sub__(self, o): return type(self)(self.x - o.x, self.y - o.y)
    def __neg__(self):    return type(self)(-self.x, -self.y)
    def __mul__(self, o):
        if isinstance(o, int): o = type(self)(o)
        return type(self)(self.x * o.x + type(self).RAD * (self.y * o.y),
                          self.x * o.y + self.y * o.x)
    __rmul__ = __mul__
    def __eq__(self, o):  return self.x == o.x and self.y == o.y
    def is_zero(self):    return self.x.is_zero() and self.y.is_zero()
    def nrm(self):        return self.x * self.x - type(self).RAD * (self.y * self.y)
    def inv(self):
        n = self.nrm().inv()
        return type(self)(self.x * n, -(self.y * n))
    def fl(self):
        return self.x.fl() + self.y.fl() * (R_GOOD.fl() ** 0.5)
    def __repr__(self):
        return f"[{self.x} + {self.y}*D]"

def qd_of(q5elem):
    """Q5 -> QD embedding (x-slot)."""
    z = QD(0); z.x = q5elem; z.y = Q5(0)
    return z

DD  = QD(Q5(0), Q5(1))                  # D itself
ONE_D = QD(1)

# W1e: D^2 = phi+2 (the rad_sq receipt, same shape as Ep.rad_sq)
D_sq = DD * DD
check("W1e_D_sq", D_sq.y.is_zero() and D_sq.x == R_GOOD,
      "D*D = phi+2 exactly (pair-pattern rad_sq; cf. Ep.rad_sq Rigidity 2129)")

# W1f: QD is a field where we use it: exact inverses, seeded random + S entries
ok_inv = (DD * DD.inv() == ONE_D)
for _ in range(60):
    z = QD(Q5(Fr(random.randint(-9, 9), random.randint(1, 7)),
              Fr(random.randint(-9, 9), random.randint(1, 7))),
           Q5(Fr(random.randint(-9, 9), random.randint(1, 7)),
              Fr(random.randint(-9, 9), random.randint(1, 7))))
    if z.is_zero() or z.nrm().is_zero(): continue
    ok_inv = ok_inv and (z * z.inv() == ONE_D)
check("W1f_field_inverses", ok_inv,
      "z*z^-1 = 1 exactly for D and 60 seeded random elements "
      "(norm x^2-(phi+2)y^2 to Q5, then Q5 norm to Q — the two-layer descent)")

# W1g: ring sanity — assoc/comm/distrib exact on seeded random triples
ok_ring = True
rand_qd = lambda: QD(Q5(Fr(random.randint(-5, 5), random.randint(1, 4)),
                        Fr(random.randint(-5, 5), random.randint(1, 4))),
                     Q5(Fr(random.randint(-5, 5), random.randint(1, 4)),
                        Fr(random.randint(-5, 5), random.randint(1, 4))))
for _ in range(50):
    a, b, c = rand_qd(), rand_qd(), rand_qd()
    ok_ring = ok_ring and ((a * b) * c == a * (b * c)) and (a * b == b * a) \
              and (a * (b + c) == a * b + a * c)
check("W1g_ring_laws", ok_ring, "assoc/comm/distrib exact, 50 seeded triples")

# ======================================================================
# W2 — THE S-MATRIX.  S = (1/D)[[1,phi],[phi,-1]].
# ======================================================================
print("=" * 72)
print("W2 — S-matrix: symmetric, S^2 = I, det = -1, rows orthonormal")
print("=" * 72)

UHAT = [[Q5(1), PHI5], [PHI5, -Q5(1)]]                 # Shat, unnormalized
INV_D = QD(Q5(0), R_GOOD.inv())                        # 1/D = D/(phi+2)
S = [[INV_D * qd_of(UHAT[i][j]) for j in (0, 1)] for i in (0, 1)]

check("W2a_symmetric", S[0][1] == S[1][0], "S_01 = S_10 exactly")

S2 = [[sum((S[i][k] * S[k][j] for k in (0, 1)), QD(0)) for j in (0, 1)]
      for i in (0, 1)]
check("W2b_S_squared_I",
      S2[0][0] == ONE_D and S2[1][1] == ONE_D and
      S2[0][1].is_zero() and S2[1][0].is_zero(),
      "S^2 = I exactly in QD — S is an involution; real+involution+symmetric "
      "=> unitary; charge conjugation C = S^2 = I (trivial)")

detS = S[0][0] * S[1][1] - S[0][1] * S[1][0]
check("W2c_det_report", detS == -ONE_D,
      "det S = -1 exactly (REPORT: S is a reflection, in O(2)\\SO(2); "
      "trace S = 0, eigenvalues +1,-1; consistent with S^2 = I)")

dots = [sum((S[i][k] * S[j][k] for k in (0, 1)), QD(0)) for i, j in
        ((0, 0), (0, 1), (1, 1))]
check("W2d_rows_orthonormal",
      dots[0] == ONE_D and dots[1].is_zero() and dots[2] == ONE_D,
      "row_0.row_0 = 1, row_0.row_1 = 0, row_1.row_1 = 1 (real => this IS "
      "unitarity; same content as W2b since S symmetric)")

# W2e: NEGATIVE CONTROL — wrong radicand D^2 = phi+1 (= phi^2, collapses).
class QDbad(QD):
    RAD = PHI5 + Q5(1)
def qdbad_of(q5elem):
    z = QDbad(0); z.x = q5elem; z.y = Q5(0)
    return z
INV_D_BAD = QDbad(Q5(0), (PHI5 + Q5(1)).inv())
Sb = [[INV_D_BAD * qdbad_of(UHAT[i][j]) for j in (0, 1)] for i in (0, 1)]
S2b = [[sum((Sb[i][k] * Sb[k][j] for k in (0, 1)), QDbad(0)) for j in (0, 1)]
       for i in (0, 1)]
bad_broke = not (S2b[0][0] == QDbad(1) and S2b[1][1] == QDbad(1)
                 and S2b[0][1].is_zero() and S2b[1][0].is_zero())
check("W2e_CONTROL_wrong_radicand", bad_broke,
      "with D^2 = phi+1 the same S fails S^2 = I (S^2 = ((phi+2)/(phi+1))I) "
      "— the radicand phi+2 is load-bearing")

# ======================================================================
# W3 — QUANTUM DIMENSIONS FROM S: d_1 = 1, d_tau = phi, D^2 = sum d^2
# ======================================================================
print("=" * 72)
print("W3 — dims from modular data: d_tau = S_0tau/S_00 = phi EXACTLY")
print("=" * 72)

d1 = S[0][0] * S[0][0].inv()
dt = S[0][1] * S[0][0].inv()
phi_in_QD = QD(0); phi_in_QD.x = PHI5
check("W3a_d1", d1 == ONE_D, "d_1 = S_00/S_00 = 1 exactly")
check("W3b_dtau_phi", dt == phi_in_QD and dt.y.is_zero(),
      "d_tau = S_0tau/S_00 = phi EXACTLY, with ZERO D-part — the ratio lands "
      "in Q(sqrt5); round 5's d_tau = phi (quantum_dimension_tau, Anyon.lean "
      "6737) arriving from modular data; cleared form: Shat_0tau = Zp.phi")
sum_d2 = Q5(1) + PHI5 * PHI5
check("W3c_total_dim", sum_d2 == R_GOOD and sum_d2 == D_sq.x,
      "sum d_a^2 = 1 + phi^2 = phi+2 = D^2 exactly (phi^2 = phi+1 used)")

# ======================================================================
# W4 — VERLINDE: the S-matrix re-derives the fusion rules, over Z
# ======================================================================
print("=" * 72)
print("W4 — Verlinde: N_ab^c = sum_x S_ax S_bx S*_cx / S_0x, all 8, exact")
print("=" * 72)

# fuse / countA transcribed from Anyon.lean 54-57 / 6545 (0 = one, 1 = tau)
def fuse(a, b):
    if a == 0: return [b]
    if b == 0: return [a]
    return [0, 1]
def countA(c, lst): return sum(1 for u in lst if u == c)
NFIB = {(a, b, c): countA(c, fuse(a, b))
        for a in (0, 1) for b in (0, 1) for c in (0, 1)}

# S is real: conj(S_cx) = S_cx (state it once; the bench's formula has S*).
all_ok, term_in_Q5, sum_in_Z, table = True, True, True, {}
for a in (0, 1):
    for b in (0, 1):
        for c in (0, 1):
            tot = QD(0)
            for x in (0, 1):
                t = S[a][x] * S[b][x] * S[c][x] * S[0][x].inv()
                term_in_Q5 = term_in_Q5 and t.y.is_zero()   # D-degree cancels per term
                tot = tot + t
            # the x-sum rationalizes all the way to Z:
            v = tot.x
            in_Z = tot.y.is_zero() and v.b == 0 and v.a.denominator == 1
            sum_in_Z = sum_in_Z and in_Z
            table[(a, b, c)] = v.a if in_Z else v
            all_ok = all_ok and in_Z and v.a == NFIB[(a, b, c)]

names = {0: "1", 1: "t"}
info("the 8 Verlinde numbers, exact: " + ", ".join(
    f"N_{names[a]}{names[b]}^{names[c]}={table[(a,b,c)]}"
    for a in (0, 1) for b in (0, 1) for c in (0, 1)))
check("W4a_verlinde_equals_fuse", all_ok,
      "all 8 sums are exact INTEGERS equal to countA c (fuse a b): "
      "1,0,0,1,0,1,1,1 — the S-matrix hands back the grammar")
check("W4b_terms_land_in_Q5", term_in_Q5,
      "STRUCTURAL: every per-x term has zero D-part — each term is "
      "(u_a u_b u_c/u_0)*D^-2 = (units of Z[phi])/(phi+2), net D-degree "
      "-3+1 = -2, and D^2 = phi+2 is rational over Q5")
check("W4c_sums_land_in_Z", sum_in_Z,
      "STRUCTURAL: the x-sum kills the sqrt5-part too — the sum "
      "rationalizes; no radical survives in any of the 8 values")

# W4d: THE CLEARED FORM a Lean `decide` checks, entirely in Zp = Z[phi] pairs:
#   sum_x Shat_ax Shat_bx Shat_cx w_x = N_ab^c * (phi+2),  w = (1, 1/phi),
#   Shat = [[1,phi],[phi,-1]], 1/phi = invPhi = (-1,1)  [units of Z[phi]!].
SHAT_ZP = [[(1, 0), (0, 1)], [(0, 1), (-1, 0)]]
W_ZP = [(1, 0), (-1, 1)]                     # 1/Shat_00 = 1, 1/Shat_01 = invPhi
cleared_ok = True
cleared_rows = []
for a in (0, 1):
    for b in (0, 1):
        for c in (0, 1):
            lhs = (0, 0)
            for x in (0, 1):
                t = zp_mul(zp_mul(SHAT_ZP[a][x], SHAT_ZP[b][x]),
                           zp_mul(SHAT_ZP[c][x], W_ZP[x]))
                lhs = zp_add(lhs, t)
            rhs = zp_mul((NFIB[(a, b, c)], 0), ZP_PHIP2)
            cleared_ok = cleared_ok and lhs == rhs
            cleared_rows.append(f"{names[a]}{names[b]}{names[c]}:{lhs}={rhs}")
info("cleared Zp equations (m,n) = m+n*phi: " + "; ".join(cleared_rows))
check("W4d_cleared_over_Zp", cleared_ok,
      "all 8 hold as INTEGER-PAIR identities in Z[phi] — no radical, no D, "
      "no zeta in the statement; each is one Lean `decide` over the file's "
      "existing Zp (precedent: Nfus_tt := by decide, Anyon.lean 6557); "
      "the weight w_x = 1/Shat_0x is a UNIT of Z[phi] (invPhi), which is "
      "why clearing needs only one factor phi+2, not a localization")

# W4e-g: NEGATIVE CONTROLS
noW = {}
for a in (0, 1):
    for b in (0, 1):
        for c in (0, 1):
            tot = QD(0)
            for x in (0, 1):
                tot = tot + S[a][x] * S[b][x] * S[c][x]       # weight dropped
            noW[(a, b, c)] = tot
bad1 = sum(1 for k in NFIB if not (noW[k].y.is_zero() and noW[k].x.b == 0
                                   and noW[k].x.a == NFIB[k]))
check("W4e_CONTROL_weight_load_bearing", bad1 >= 1,
      f"dropping 1/S_0x breaks the table in {bad1}/8 cells — the Verlinde "
      "weight is load-bearing, the check can fail")

Sw = [[S[0][0], S[0][1]], [S[1][0], -S[1][1]]]     # S_tt flipped to +1/D
bad2 = 0
for a in (0, 1):
    for b in (0, 1):
        for c in (0, 1):
            tot = QD(0)
            for x in (0, 1):
                tot = tot + Sw[a][x] * Sw[b][x] * Sw[c][x] * Sw[0][x].inv()
            if not (tot.y.is_zero() and tot.x.b == 0 and tot.x.a == NFIB[(a, b, c)]):
                bad2 += 1
check("W4f_CONTROL_sign_load_bearing", bad2 >= 1,
      f"flipping S_tt from -1/D to +1/D breaks {bad2}/8 cells — the -1 "
      "is load-bearing")

NZ2 = {(a, b, c): 1 if (a + b) % 2 == c else 0
       for a in (0, 1) for b in (0, 1) for c in (0, 1)}   # Z2 fusion table
diff_cells = [k for k in NFIB if NFIB[k] != NZ2[k]]
check("W4g_CONTROL_discriminates_Z2",
      diff_cells == [(1, 1, 1)] and table[(1, 1, 1)] == 1 and NZ2[(1, 1, 1)] == 0,
      "the computed table differs from the Z2/semion fusion table in exactly "
      "the (t,t,t) cell (1 vs 0): tau x tau = 1 + TAU is what Verlinde "
      "returns — the match to Fibonacci is not vacuous")

# ======================================================================
# W5 — THE T-LAYER AND THE MODULAR RELATIONS, COSTED HONESTLY
# ======================================================================
print("=" * 72)
print("W5 — T = diag(1, zeta5^3); (ShatT)^3 = (phi+2) p+ I over Z[zeta5];")
print("      lambda = p+/D identified in Z[zeta20]; the ring bill, measured")
print("=" * 72)

# --- Z5 = Z[zeta5], transcribed VERBATIM from Anyon.lean 240-279 ---
def z5_mul(u, v):
    c0 = u[0]*v[0]
    c1 = u[0]*v[1] + u[1]*v[0]
    c2 = u[0]*v[2] + u[1]*v[1] + u[2]*v[0]
    c3 = u[0]*v[3] + u[1]*v[2] + u[2]*v[1] + u[3]*v[0]
    c4 = u[1]*v[3] + u[2]*v[2] + u[3]*v[1]
    c5 = u[2]*v[3] + u[3]*v[2]
    c6 = u[3]*v[3]
    return (c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4)
z5_add = lambda u, v: tuple(a + b for a, b in zip(u, v))
z5_neg = lambda u: tuple(-a for a in u)
z5_conj = lambda u: (u[0] - u[1], -u[1], u[3] - u[1], u[2] - u[1])  # A.lean 1732
Z5_ZERO, Z5_ONE = (0, 0, 0, 0), (1, 0, 0, 0)
Z5_Z, Z5_Z2, Z5_Z3, Z5_Z4 = (0,1,0,0), (0,0,1,0), (0,0,0,1), (-1,-1,-1,-1)
Z5_PHI, Z5_INVPHI = (0, 0, -1, -1), (-1, 0, -1, -1)
z5_fl = lambda u: sum(u[k] * cmath.exp(2j * pi * k / 5) for k in range(4))

rec = (z5_mul(Z5_Z3, Z5_Z) == Z5_Z4 and z5_mul(Z5_Z4, Z5_Z) == Z5_ONE and
       z5_mul(Z5_PHI, Z5_PHI) == z5_add(Z5_PHI, Z5_ONE) and
       z5_mul(Z5_PHI, Z5_INVPHI) == Z5_ONE and
       z5_conj(Z5_Z) == Z5_Z4 and z5_conj(z5_conj(Z5_Z2)) == Z5_Z2 and
       z5_conj(Z5_PHI) == Z5_PHI)
hom_ok = True
for _ in range(200):
    u = tuple(random.randint(-9, 9) for _ in range(4))
    v = tuple(random.randint(-9, 9) for _ in range(4))
    hom_ok = hom_ok and z5_conj(z5_mul(u, v)) == z5_mul(z5_conj(u), z5_conj(v))
check("W5a_Z5_transcription", rec and hom_ok,
      "Z5 receipts re-verified: zeta3*zeta = zeta4, zeta4*zeta = 1, "
      "phi^2 = phi+1, phi*invPhi = 1, conj = zeta->zeta^4 involution fixing "
      "phi, conj multiplicative on 200 seeded pairs (exact)")

THETA = Z5_Z3
check("W5b_twist_is_zeta3",
      abs(z5_fl(THETA) - cmath.exp(-4j * pi / 5)) < 1e-12,
      "theta_tau = zeta5^3 = e^{-4 pi i/5} — the bench's THETA[1] "
      "(modular_data.py 37) and the hexagon's twist (grammar_hexagon.py "
      "148-151, theta_t = r1/phi + rt); 'our chirality'")

# Shat and T over Z5; M = Shat*T; M^3 = (phi+2) * p+ * I
SHAT5 = [[Z5_ONE, Z5_PHI], [Z5_PHI, z5_neg(Z5_ONE)]]
TMAT = [[Z5_ONE, Z5_ZERO], [Z5_ZERO, THETA]]
def matmul5(A, B):
    return [[z5_add(z5_mul(A[i][0], B[0][j]), z5_mul(A[i][1], B[1][j]))
             for j in (0, 1)] for i in (0, 1)]
M = matmul5(SHAT5, TMAT)
M3 = matmul5(matmul5(M, M), M)
PPLUS = z5_add(Z5_ONE, z5_mul(z5_mul(Z5_PHI, Z5_PHI), THETA))   # 1 + phi^2 theta
check("W5c_gauss_sum_form",
      PPLUS == z5_add(Z5_Z3, z5_neg(Z5_Z)) and PPLUS == (0, -1, 0, 1),
      "p+ = 1 + phi^2 zeta^3 = zeta^3 - zeta = (0,-1,0,1) in the file's "
      "basis — a Z5 numeral")
Z5_PHIP2 = z5_add(Z5_PHI, z5_add(Z5_ONE, Z5_ONE))               # phi+2 in Z5
SC = z5_mul(Z5_PHIP2, PPLUS)
check("W5d_cleared_modular_relation",
      M3[0][0] == SC and M3[1][1] == SC and
      M3[0][1] == Z5_ZERO and M3[1][0] == Z5_ZERO,
      "(Shat T)^3 = (phi+2) p+ I EXACTLY in Z[zeta5] — the (ST)^3 = "
      "lambda S^2 relation with all D-degrees cleared (D^3 lambda = "
      "(phi+2) p+), entirely inside the file's EXISTING Z5; entrywise a "
      "`decide`")
PMINUS = z5_conj(PPLUS)
check("W5e_gauss_duality",
      z5_mul(PPLUS, PMINUS) == Z5_PHIP2 and
      PMINUS == z5_add(Z5_ONE, z5_mul(z5_mul(Z5_PHI, Z5_PHI), Z5_Z2)),
      "p+ conj(p+) = phi+2 = D^2 in Z5 (so |lambda| = 1 in cleared form), "
      "and conj(p+) = 1 + phi^2 zeta^2 = p- — the mirror Gauss sum; "
      "conj is the file's PROVED ring map (Anyon.lean 1732ff)")

# mirror chirality + wrong-pairing control
TM = [[Z5_ONE, Z5_ZERO], [Z5_ZERO, Z5_Z2]]
Mm3 = matmul5(matmul5(matmul5(SHAT5, TM), matmul5(SHAT5, TM)), matmul5(SHAT5, TM))
SCm = z5_mul(Z5_PHIP2, PMINUS)
mirror_ok = (Mm3[0][0] == SCm and Mm3[1][1] == SCm and
             Mm3[0][1] == Z5_ZERO and Mm3[1][0] == Z5_ZERO)
wrong_pair = not (M3[0][0] == SCm and M3[1][1] == SCm)
check("W5f_mirror_and_CONTROL", mirror_ok and wrong_pair and SC != SCm,
      "theta' = zeta^2 gives (Shat T')^3 = (phi+2) p- I (the mirror "
      "chirality, conjugate scalar); pairing theta = zeta^3 with p- FAILS "
      "— chirality and Gauss sum must match, the relation has teeth")

# --- Z[zeta20]: the lambda identification, exact ---
def c20_mul(u, v):
    c = [0] * 15
    for i in range(8):
        if u[i] == 0: continue
        for j in range(8):
            c[i + j] += u[i] * v[j]
    for k in range(14, 7, -1):       # zeta^k = z^{k-2} - z^{k-4} + z^{k-6} - z^{k-8}
        t = c[k]
        if t:
            c[k - 2] += t; c[k - 4] -= t; c[k - 6] += t; c[k - 8] -= t
        c[k] = 0
    return tuple(c[:8])
C20_ONE = (1, 0, 0, 0, 0, 0, 0, 0)
Z20 = (0, 1, 0, 0, 0, 0, 0, 0)
pw = [C20_ONE]
for _ in range(20):
    pw.append(c20_mul(pw[-1], Z20))
c20_neg = lambda u: tuple(-a for a in u)
c20_add = lambda u, v: tuple(a + b for a, b in zip(u, v))
c20_fl = lambda u: sum(u[k] * cmath.exp(1j * pi * k / 10) for k in range(8))
prim = all(pw[j] != C20_ONE for j in range(1, 20))
check("W5g_C20_ring",
      pw[20] == C20_ONE and pw[10] == c20_neg(C20_ONE) and prim and
      abs(c20_fl(Z20) - cmath.exp(1j * pi / 10)) < 1e-12,
      "Z[zeta20] as 8-vectors mod Phi20 = x^8-x^6+x^4-x^2+1: zeta^20 = 1, "
      "zeta^10 = -1, order exactly 20 (primitive), float embedding e^{i pi/10} "
      "matches; degree = EulerPhi(20) = 8 over Z — same Z-rank as KK")
# wrong-fold control: flipping the fold signs must break zeta^10 = -1
def c20_mul_wrong(u, v):
    c = [0] * 15
    for i in range(8):
        for j in range(8):
            c[i + j] += u[i] * v[j]
    for k in range(14, 7, -1):
        t = c[k]
        if t:
            c[k - 2] -= t; c[k - 4] += t; c[k - 6] -= t; c[k - 8] += t
        c[k] = 0
    return tuple(c[:8])
pww = C20_ONE
for _ in range(10): pww = c20_mul_wrong(pww, Z20)
check("W5h_CONTROL_fold_signs", pww != c20_neg(C20_ONE),
      "with the Phi20 fold signs flipped, zeta^10 = -1 fails — the "
      "reduction rule is load-bearing")

emb5 = lambda u: tuple(sum(u[i] * pw[4 * i][k] for i in range(4)) for k in range(8))
hom20 = emb5(Z5_ONE) == C20_ONE and \
        c20_add(c20_add(C20_ONE, c20_add(pw[4], pw[8])),
                c20_add(pw[12], pw[16])) == (0,) * 8
for _ in range(100):
    u = tuple(random.randint(-9, 9) for _ in range(4))
    v = tuple(random.randint(-9, 9) for _ in range(4))
    hom20 = hom20 and emb5(z5_mul(u, v)) == c20_mul(emb5(u), emb5(v))
check("W5i_zeta5_embeds", hom20,
      "zeta5 := zeta20^4: 1+z^4+z^8+z^12+z^16 = 0 and the map Z5 -> C20 is "
      "multiplicative on 100 seeded pairs (exact) — Q(zeta20) contains "
      "Q(zeta5)")

D20 = c20_add(pw[1], pw[19])                         # D = zeta + zeta^-1
D20sq = c20_mul(D20, D20)
D20_4 = c20_mul(D20sq, D20sq)
minpoly = c20_add(c20_add(D20_4, c20_neg(tuple(5 * a for a in D20sq))),
                  tuple(5 * a for a in C20_ONE))
conj20 = lambda u: tuple(sum(u[j] * pw[(19 * j) % 20][k] for j in range(8))
                         for k in range(8))
check("W5j_D_in_zeta20",
      D20sq == emb5(Z5_PHIP2) and minpoly == (0,) * 8 and conj20(D20) == D20,
      "D = zeta20 + zeta20^-1 = 2cos(pi/10): D^2 = phi+2 exactly, "
      "D^4 - 5D^2 + 5 = 0 (min poly, deg 4), conj-fixed (real) — so "
      "Q(zeta20) = Q(zeta5)(D): ANOTHER pair-layer over Z5 with radicand "
      "phi+2 instead of phi (KK's literal template), NOT a new 8-tuple ring")

LAM = pw[13]                                          # e^{-7 pi i/10} = zeta20^13
acc, lam_ord = LAM, 1
while acc != C20_ONE:
    acc = c20_mul(acc, LAM); lam_ord += 1
check("W5k_lambda_identified",
      c20_mul(LAM, D20) == emb5(PPLUS) and lam_ord == 20 and
      abs(c20_fl(LAM) - cmath.exp(-7j * pi / 10)) < 1e-12,
      "lambda := zeta20^13 = e^{-7 pi i/10} satisfies lambda*D = p+ EXACTLY "
      "in Z[zeta20] (an INTEGRAL identity — lambda is a unit, a primitive "
      "20th root, order 20 verified); hence lambda = p+/D and "
      "e^{2 pi i c/8} = zeta20^13 reads 5c = 26 (mod 40): c = 26/5 = "
      "-14/5 (mod 8) — the bench's chirality")
check("W5l_CONTROL_mirror_index",
      c20_mul(pw[7], D20) == emb5(PMINUS) and c20_mul(pw[7], D20) != emb5(PPLUS),
      "zeta20^7 * D = p- (the mirror, c = +14/5), and NOT p+ — the index 13 "
      "is load-bearing, the two chiralities are distinguished exactly")

# The half-integer coordinate fact: zeta20 in the basis zeta5^i D^j
def solve_zeta20_coords():
    basis = [c20_mul(emb5(z), d) for j, d in ((0, C20_ONE), (1, D20))
             for z in (Z5_ONE, Z5_Z, Z5_Z2, Z5_Z3)]
    # solve sum x_k basis_k = zeta20 over Q, exact Gauss
    A = [[Fr(basis[k][r]) for k in range(8)] + [Fr(Z20[r])] for r in range(8)]
    for col in range(8):
        piv = next(r for r in range(col, 8) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [e / pv for e in A[col]]
        for r in range(8):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [er - f * ec for er, ec in zip(A[r], A[col])]
    return [A[r][8] for r in range(8)]
coords = solve_zeta20_coords()
dens = sorted({c.denominator for c in coords})
recon = (0,) * 8
for k, c in enumerate(coords):
    j, i = divmod(k, 4)
    base = c20_mul(emb5([Z5_ONE, Z5_Z, Z5_Z2, Z5_Z3][i]), [C20_ONE, D20][j])
    recon = c20_add(recon, tuple(c * b for b in base))
# integral closed form implied by the solved coordinates:
closed = c20_mul(emb5((2, -1, 1, -2)), D20) == tuple(5 * a for a in Z20)
check("W5m_index_measured",
      recon == tuple(Fr(a) for a in Z20) and dens == [1, 5] and closed,
      f"zeta20 in the basis zeta5^i * D^j has denominators {dens}: "
      "5*zeta20 = D*(2 - zeta + zeta^2 - 2 zeta^3) EXACTLY (verified "
      "integrally) — zeta20 is NOT in the order Z[zeta5][D], coordinate "
      "denominator 5, so a KK-template pair-ring can state lambda only "
      "through 5-cleared identities; the honest integral home for lambda "
      "as an ELEMENT is the 8-tuple Z[zeta20]. [NB: the first draft of "
      "this check predicted denominator 2 and FAILED — the measurement "
      "corrected the model; kept per norm 7]")
info(f"zeta20 = sum coords * zeta5^i D^j, coords = "
     f"{[str(c) for c in coords]}")
info("RING BILL, measured: cleared core needs NOTHING beyond Zp (exists) "
     "+ Z5 (exists); lambda-as-element needs Z[zeta20] (deg 8; the field is "
     "the KK-template Q(zeta5)(D), but zeta20's coordinates there carry a "
     "denominator 5) and 1/D needs 1/5 (N_(Z[phi])(phi+2) = 5, not a unit) "
     "— literal S is non-integral in EVERY ring; clearing is unavoidable "
     "anyway, so buy the cleared statements.")

# float sanity, NON-LOAD-BEARING
Sf = [[1 / R_GOOD.fl() ** 0.5, PHI5.fl() / R_GOOD.fl() ** 0.5],
      [PHI5.fl() / R_GOOD.fl() ** 0.5, -1 / R_GOOD.fl() ** 0.5]]
Tf = [[1, 0], [0, cmath.exp(-4j * pi / 5)]]
def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)]
            for i in range(2)]
ST3 = mm(mm(mm(Sf, Tf), mm(Sf, Tf)), mm(Sf, Tf))
lamf = cmath.exp(-7j * pi / 10)
res = max(abs(ST3[i][j] - lamf * (1 if i == j else 0))
          for i in range(2) for j in range(2))
info(f"FLOAT SANITY (non-load-bearing): |(ST)^3 - e^(-7 pi i/10) S^2| = "
     f"{res:.2e}; c = {cmath.phase(lamf) * 8 / (2 * pi) % 8:.10f} = 26/5")

# ======================================================================
# W6 — BENCH CO-SIGN: modular_data.py agrees with the exact values
# ======================================================================
print("=" * 72)
print("W6 — bench co-sign: workshop/modular_data.py vs the exact tower")
print("=" * 72)
sys.path.insert(0, WORKSHOP)
try:
    import numpy as np
    import modular_data as bench
    lines = []
    bench.demonstrate(lines.append)          # its own asserts all run
    check("W6a_bench_runs", len(lines) >= 8,
          f"modular_data.demonstrate ran clean ({len(lines)} say-lines, "
          "every internal assert passed)")
    ok_const = (abs(bench.PHI - PHI5.fl()) < 1e-15 and
                abs(bench.D - R_GOOD.fl() ** 0.5) < 1e-15 and
                abs(bench.THETA[1] - z5_fl(THETA)) < 1e-12 and
                abs(bench.DIMS[1] - PHI5.fl()) < 1e-15)
    check("W6b_bench_constants", ok_const,
          "bench PHI, D, THETA[1] = zeta5^3, DIMS = (1, phi) all match the "
          "exact tower to < 1e-12")
    # bench S from twists vs exact S
    Sb = np.zeros((2, 2), dtype=complex)
    for a in range(2):
        for b in range(2):
            Sb[a, b] = sum(bench.N(a, b, c) * bench.DIMS[c] * bench.THETA[c]
                           / (bench.THETA[a] * bench.THETA[b])
                           for c in range(2)) / bench.D
    dev = max(abs(Sb[i, j] - S[i][j].fl()) for i in range(2) for j in range(2))
    check("W6c_bench_S", dev < 1e-12,
          f"bench S (from fusion+dims+twists formula) matches exact S to "
          f"{dev:.1e}")
    # bench lambda and c vs zeta20^13
    Tb = np.diag(bench.THETA)
    Mb = np.linalg.matrix_power(Sb.real @ Tb, 3)
    lamb = np.trace(Mb) / 2
    cb = np.angle(lamb) * 8 / (2 * pi) % 8
    check("W6d_bench_lambda_c",
          abs(lamb - c20_fl(LAM)) < 1e-12 and abs(cb - 26 / 5) < 1e-9,
          f"bench lambda = {lamb:.6f} = zeta20^13 to {abs(lamb - c20_fl(LAM)):.1e}; "
          f"c = {cb:.6f} = 26/5 = -14/5 (mod 8)")
    # bench Verlinde vs exact integers
    worst = max(abs(sum(Sb.real[a, x] * Sb.real[b, x] * Sb.real[c, x]
                        / Sb.real[0, x] for x in range(2)) - NFIB[(a, b, c)])
                for a in range(2) for b in range(2) for c in range(2))
    check("W6e_bench_verlinde", worst < 1e-12,
          f"bench Verlinde numbers match the exact integers to {worst:.1e}")
    # bench claim (1) 'imaginary parts cancel' UPGRADED to an exact Z5 identity:
    THI = [Z5_ONE, Z5_Z2]                 # theta^-1: (zeta^3)^-1 = zeta^2
    DIM5 = [Z5_ONE, Z5_PHI]
    s_tw_ok = z5_mul(THETA, THI[1]) == Z5_ONE
    for a in (0, 1):
        for b in (0, 1):
            tot = Z5_ZERO
            for c in (0, 1):
                if NFIB[(a, b, c)]:
                    t = z5_mul(z5_mul(DIM5[c], [Z5_ONE, THETA][c]),
                               z5_mul(THI[a], THI[b]))
                    tot = z5_add(tot, t)
            s_tw_ok = s_tw_ok and tot == SHAT5[a][b]
    check("W6f_S_from_twists_EXACT", s_tw_ok,
          "S_ab * D = sum_c N_ab^c d_c theta_c/(theta_a theta_b) holds "
          "EXACTLY in Z[zeta5] for all 4 entries — the bench's 'imaginary "
          "parts cancel to 1e-16' is a ring identity (theta^-1 = zeta^2, a "
          "Z5 numeral; 4 more decides if wanted)")
    import grammar_hexagon
    hx = []
    grammar_hexagon.demonstrate(hx.append)
    check("W6g_hexagon_twist_cosign", len(hx) > 0,
          "grammar_hexagon ran clean — its assert theta_t = r1/phi + rt = "
          "e^{-4 pi i/5} (= zeta5^3) co-signs the T convention")
except Exception as e:
    check("W6_bench_cosign", False, f"bench import/run failed: {e!r}")

# ======================================================================
# W7 — CALIBRATION, measured on the tree (facts for the cost estimate)
# ======================================================================
print("=" * 72)
print("W7 — calibrators + reusable machinery, measured (grep the fact)")
print("=" * 72)
try:
    src = open(os.path.join(LEAN, "Anyon.lean"), encoding="utf-8").read().splitlines()
    # -1: include each section's `/-! ═══` opener line, matching the census cut
    L1 = next(i for i, l in enumerate(src) if "## 9.11  THE MOD-11 CLOSURE" in l) - 1
    L2 = next(i for i, l in enumerate(src) if "## ROUND 5 — THE DECIDABLE ORDER" in l) - 1
    b1 = src[L1:L2]; b2 = src[L2:]
    t1 = sum(1 for l in b1 if l.startswith("theorem "))
    d1_ = sum(1 for l in b1 if l.startswith("def "))
    t2 = sum(1 for l in b2 if l.startswith("theorem "))
    d2_ = sum(1 for l in b2 if l.startswith("def "))
    check("W7a_calibrators_measured",
          (len(b1), t1, d1_) == (386, 47, 2) and (len(b2), t2, d2_) == (1140, 102, 16),
          f"mod-11 block: {len(b1)} lines, {t1} theorems, {d1_} defs "
          f"(lines {L1+1}-{L2}); order/d_tau block: {len(b2)} lines, {t2} "
          f"theorems, {d2_} defs (lines {L2+1}-{len(src)})")
    whole = "\n".join(src)
    needed = ["def Nfus", "def countA", "theorem quantum_dimension_tau",
              "theorem zp_invPhi_mul", "def matApp", "def matMul",
              "def conj (u : Z5)", "theorem Nfus_tt", "def phi : Z5",
              "def zeta3"]
    missing = [n for n in needed if n not in whole]
    rig = open(os.path.join(LEAN, "Rigidity.lean"), encoding="utf-8").read()
    pat3 = ("structure KK" in whole and "structure Ep" in rig
            and "theorem rad_sq" in rig)
    check("W7b_reusable_machinery_exists", not missing and pat3,
          "grepped in-tree: Nfus, countA, quantum_dimension_tau, "
          "zp_invPhi_mul, matApp/matMul, Z5.conj, Nfus_tt (decide-on-Zp "
          "precedent), Z5.phi, zeta3 all present in Anyon.lean; the "
          "quadratic-pair pattern present twice in Lean (KK, Ep.rad_sq) — "
          f"missing: {missing or 'none'}")
except Exception as e:
    check("W7_calibration", False, f"tree measurement failed: {e!r}")

info("COST ESTIMATE (calibrated): W1-W4 cleared core over Zp — 1-2 defs "
     "(Shat, w) + ~25-40 theorems (~300-450 lines): pretty identity, "
     "Shat^2 = (phi+2)I, det, symmetry, d_1/d_tau pointers to "
     "quantum_dimension_tau, Verlinde all-8 as one `decide` forall + per-"
     "cell receipts, anti-vacuity + 3 controls; mod-11-shaped (47 thm/386 "
     "ln) but LIGHTER (no hom assembly, no new ring). Z5 T-layer add-on "
     "((ShatT)^3 = (phi+2)p+I, p+ = zeta^3-zeta, Gauss duality, mirror + "
     "2 controls): +12-18 theorems, +150-250 lines, still no new ring. "
     "TOTAL ~40-58 theorems, ~450-700 lines — one comfortable round, under "
     "the d_tau block (102 thm/1140 ln). The zeta20 layer (lambda as "
     "element, c = -14/5 as a Lean sentence): a NEW deg-8 ring + the "
     "denominator-5 coordinate defect (W5m) + 1/5 for literal S — a "
     "d_tau-block-sized round on its own; PARK IT, content already pinned "
     "by W5d/W5e + this certificate.")

# ======================================================================
print("=" * 72)
npass = sum(1 for _, ok in results if ok)
nfail = len(results) - npass
print(f"RESULT: {npass}/{len(results)} PASS" + (f", {nfail} FAIL" if nfail else ""))
sys.exit(0 if nfail == 0 else 1)
