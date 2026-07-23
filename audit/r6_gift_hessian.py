#!/usr/bin/env python3
"""r6_gift_hessian.py — round-6 GIFT certification: Hessian rigidity as a theorem.

CANDIDATE (seat): make grammar_stone5's asserted signature {0,+,+,+} of the 4x4
Hessian of the pentagon sum-of-squares residual a Lean theorem — positive
semidefinite with null space EXACTLY the gauge-torus tangent — at BOTH pentagon
worlds, using the file's decidable-order technology (PosP: sign of u + y*sqrt5
by comparing u^2 vs 5y^2; Anyon.lean lines 5639-6777, 102 theorems + 16 defs)
extended one square root: sign of x + y*sqrt(phi) for x,y in Q(sqrt5), decided
by comparing x^2 vs phi*y^2 with the existing sign.

EXACT ARITHMETIC ONLY in load-bearing checks (Fraction / int).  Floats appear
solely as cross-instrument sanity (verifying the exact sign procedures, tying
the exact Hessian to the bench's central-difference object); every PASS/FAIL
that certifies the gift is exact.

Pentagon machinery transcribed from audit/r3_pentagon_poly.py (instrument A,
itself transcribed from Anyon.lean's Fs/pentagonValid/pentagonCheck and
verified against the file's own PentPoly algorithm in round 3).
Residual convention: residual = LHS - RHS per pentagonCheck.
Variables 0=p, 1=q, 2=r, 3=sPar (sPar = the F-matrix (tau,tau) entry,
renamed from the task's `s` to avoid clashing with the radical s = sqrt(phi)).

Points (F = [[p,q],[r,sPar]]):
  golden  : p = 1/phi = phi-1, q = r = 1/s = (phi-1)*s, sPar = -(phi-1)
  yang-lee: (-phi, 1, -phi, phi)   [exactly r5_g3_hessian_gauge.py line 138]
  strict  : (1, 1, 1, 1)           [proposed control — see V3e: REFUTES the
                                    task's expectation; it IS PSD-with-null-
                                    exactly-tangent despite being a non-solution]
  control : (1, 2, 3, -1)          [the WORKING negative control, q != r]
"""
import sys, random
from fractions import Fraction as Fr
from itertools import product
from math import isqrt, sqrt

random.seed(20260721)
results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def info(msg):
    print(f"      {msg}")

# ======================================================================
# V1 — the ring: Qs5 = Q(sqrt5) as Fraction pairs, E = Qs5(sqrt(phi))
# ======================================================================
class Q5:
    """a + b*sqrt5, a,b Fraction."""
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
    def __hash__(self):   return hash((self.a, self.b))
    def is_zero(self):    return self.a == 0 and self.b == 0
    def inv(self):
        n = self.a * self.a - 5 * self.b * self.b
        return Q5(self.a / n, -self.b / n)
    def conj(self):       return Q5(self.a, -self.b)
    def fl(self):         return float(self.a) + float(self.b) * sqrt(5.0)
    def __repr__(self):
        return f"({self.a}{'+' if self.b >= 0 else ''}{self.b}√5)"

def sign5(x, cmp_const=5):
    """Exact sign of a + b*sqrt5.  cmp_const=5 is load-bearing (negative
    control below uses a wrong constant to show the comparison matters)."""
    a, b = x.a, x.b
    if a == 0 and b == 0: return 0
    if a >= 0 and b >= 0: return 1
    if a <= 0 and b <= 0: return -1
    c = a * a - cmp_const * b * b          # compare a^2 vs 5 b^2
    if c == 0:
        if cmp_const == 5: raise AssertionError("sqrt5 rational?!")
        return 0
    return (1 if c > 0 else -1) if a > 0 else (-1 if c > 0 else 1)

PHI5   = Q5(Fr(1, 2), Fr(1, 2))            # phi as a Qs5 element
PHIM1  = PHI5 - Q5(1)                      # phi - 1 = 1/phi
assert PHI5 * PHI5 == PHI5 + Q5(1)         # phi^2 = phi + 1
assert PHI5 * PHIM1 == Q5(1)               # phi * (phi-1) = 1

class EE:
    """x + y*s with s = sqrt(phi), x,y in Qs5; s^2 = phi."""
    __slots__ = ('x', 'y')
    def __init__(self, x=None, y=None):
        self.x = x if isinstance(x, Q5) else Q5(0 if x is None else x)
        self.y = y if isinstance(y, Q5) else Q5(0 if y is None else y)
    def __add__(self, o): return EE(self.x + o.x, self.y + o.y)
    def __sub__(self, o): return EE(self.x - o.x, self.y - o.y)
    def __neg__(self):    return EE(-self.x, -self.y)
    def __mul__(self, o):
        if isinstance(o, int): o = EE(o)
        return EE(self.x * o.x + self.y * o.y * PHI5,
                  self.x * o.y + self.y * o.x)
    __rmul__ = __mul__
    def __eq__(self, o):  return self.x == o.x and self.y == o.y
    def __hash__(self):   return hash((self.x, self.y))
    def is_zero(self):    return self.x.is_zero() and self.y.is_zero()
    def inv(self):
        n = self.x * self.x - PHI5 * (self.y * self.y)      # in Qs5
        ni = n.inv()
        return EE(self.x * ni, -(self.y * ni))
    def fl(self):         return self.x.fl() + self.y.fl() * sqrt((1 + sqrt(5.0)) / 2)
    def __repr__(self):
        if self.y.is_zero(): return f"{self.x}"
        return f"[{self.x} + {self.y}·s]"

E0, E1 = EE(0), EE(1)

def signE(x, wrong_radicand=False):
    """Exact sign of x + y*s (s = sqrt(phi) > 0): the two-layer decision a
    Lean file would run — Qs5 signs of x and y, mixed case via
    sign5(x^2 - phi*y^2).  wrong_radicand replaces phi by phi-1 (control)."""
    sx, sy = sign5(x.x), sign5(x.y)
    if sx == 0 and sy == 0: return 0
    if sx >= 0 and sy >= 0: return 1
    if sx <= 0 and sy <= 0: return -1
    rad = PHIM1 if wrong_radicand else PHI5
    c = x.x * x.x - rad * (x.y * x.y)
    sc = sign5(c)
    if sc == 0: raise AssertionError("sqrt(phi) in Q(sqrt5)?!")
    return (1 if sc > 0 else -1) if sx > 0 else (-1 if sc > 0 else 1)

print("== V1: exact sign on Qs5 = Q(sqrt5) and on E = Qs5(sqrt(phi)) ==")

def rand_fr():  return Fr(random.randint(-60, 60), random.randint(1, 40))
def rand_q5():  return Q5(rand_fr(), rand_fr())
def rand_E():   return EE(rand_q5(), rand_q5())

# float agreement, 5000 elements each ring
n_bad5 = n_skip5 = 0
for _ in range(5000):
    x = rand_q5(); f = x.fl()
    if abs(f) < 1e-8: n_skip5 += 1; continue
    if sign5(x) != (1 if f > 0 else -1): n_bad5 += 1
check("V1.sign5_float_5000", n_bad5 == 0,
      f"exact vs float sign, 5000 random Qs5 elements: {n_bad5} mismatch, {n_skip5} skipped(<1e-8)")
n_badE = n_skipE = 0
for _ in range(5000):
    x = rand_E(); f = x.fl()
    if abs(f) < 1e-8: n_skipE += 1; continue
    if signE(x) != (1 if f > 0 else -1): n_badE += 1
check("V1.signE_float_5000", n_badE == 0,
      f"exact vs float sign, 5000 random E elements: {n_badE} mismatch, {n_skipE} skipped(<1e-8)")

# trichotomy: sign==0 iff element==0; sign(-x) = -sign(x); values in {-1,0,1}
tri_ok = True
for _ in range(1500):
    x = rand_q5(); e = rand_E()
    for v, s, z in ((x, sign5(x), x.is_zero()), (e, signE(e), e.is_zero())):
        if s not in (-1, 0, 1): tri_ok = False
        if (s == 0) != z: tri_ok = False
    if sign5(-x) != -sign5(x) or signE(-e) != -signE(e): tri_ok = False
    if sign5(x - x) != 0 or signE(e - e) != 0: tri_ok = False
check("V1.trichotomy_1500", tri_ok,
      "sign in {-1,0,1}; sign=0 iff zero; sign(-x)=-sign(x); sign(x-x)=0 — both rings")

# multiplicativity on samples
mul_ok = True
for _ in range(1500):
    x, y = rand_q5(), rand_q5()
    if sign5(x * y) != sign5(x) * sign5(y): mul_ok = False
    u, v = rand_E(), rand_E()
    if signE(u * v) != signE(u) * signE(v): mul_ok = False
check("V1.sign_multiplicative_1500", mul_ok, "sign(ab)=sign(a)sign(b), both rings")

# exact zero + Pell near-zero controls, cross-checked by an isqrt instrument
S5 = Q5(0, 1)
check("V1.zero_sqrt5_sq", sign5(S5 * S5 - Q5(5)) == 0, "sign(sqrt5^2 - 5) = 0")
sE = EE(Q5(0), Q5(1))                                   # the radical s
check("V1.zero_s_sq", signE(sE * sE - EE(PHI5)) == 0, "sign(s^2 - phi) = 0")
# Pell: 51841^2 - 5*23184^2 = 1  =>  51841 - 23184*sqrt5 is POSITIVE, ~ +9.6e-6
assert 51841**2 - 5 * 23184**2 == 1
pell = Q5(51841, -23184)
D = 40
SQRT5_SC = isqrt(5 * 10**(2 * D))                        # floor(sqrt5 * 10^D)
lhs, rhs = 51841 * 10**D, 23184 * SQRT5_SC
assert abs(lhs - rhs) > 23184 + 1, "isqrt instrument not decisive"
check("V1.pell_nearzero", sign5(pell) == 1 and lhs > rhs,
      f"51841-23184·√5 ≈ {pell.fl():.2e}: exact sign +1, isqrt(40 digits) agrees; float alone is at 1e-6 scale")
# E near-zero: best rational p/q ~ s with q <= 10^6, sign of p/q - s
SQ5_2D = isqrt(5 * 10**(4 * D))                          # floor(sqrt5 * 10^(2D))
S_SC = isqrt((10**(2 * D) + SQ5_2D) // 2)                # floor(s * 10^D): s^2*10^(2D) = phi*10^(2D)
apx = Fr(sqrt((1 + sqrt(5.0)) / 2)).limit_denominator(10**6)
elt = EE(Q5(apx), Q5(0)) - sE                            # p/q - s, ~1e-13
got = signE(elt)
ind = 1 if apx.numerator * 10**D > apx.denominator * S_SC else -1  # decisive: gap >> q
assert abs(apx.numerator * 10**D - apx.denominator * S_SC) > 2 * apx.denominator
check("V1.E_nearzero", got == ind,
      f"sign({apx} - s), value ≈ {elt.fl():.1e}: exact procedure = {got}, isqrt instrument = {ind}")
# NEGATIVE CONTROL (family V1): wrong comparison constants flip verdicts
nc1 = sign5(Q5(-2, 1), cmp_const=4)                      # sqrt5-2 > 0 truly
nc2 = signE(EE(Q5(Fr(-5, 4)), Q5(1)), wrong_radicand=True)  # s - 5/4 > 0 truly
check("V1.negctrl_wrong_radicand", sign5(Q5(-2, 1)) == 1 and nc1 != 1
      and signE(EE(Q5(Fr(-5, 4)), Q5(1))) == 1 and nc2 == -1,
      f"a² vs 4b² miscalls sqrt5-2 ({nc1}); x² vs (phi-1)y² miscalls s-5/4 ({nc2}): the constants 5 and phi are load-bearing")

# ======================================================================
# V2 — pentagon residuals, gradients, Jacobian, H = 2 JᵀJ at golden point
# ======================================================================
print()
print("== V2: the 11 residual polynomials, J (11x4), H = 2·JᵀJ in E ==")

ONE, TAU = 0, 1
LABELS = (ONE, TAU)
def fuse(a, b):
    if a == ONE: return (b,)
    if b == ONE: return (a,)
    return (ONE, TAU)

# sparse poly ring Z[p,q,r,sPar]: monomial = sorted tuple of var indices
def pconst(c): return {(): c} if c else {}
PZERO, PONE = {}, pconst(1)
def pvar(i): return {(i,): 1}
def padd(u, v):
    w = dict(u)
    for m, c in v.items():
        t = w.get(m, 0) + c
        if t: w[m] = t
        else: w.pop(m, None)
    return w
def pneg(u): return {m: -c for m, c in u.items()}
def psub(u, v): return padd(u, pneg(v))
def pmul(u, v):
    w = {}
    for m1, c1 in u.items():
        for m2, c2 in v.items():
            m = tuple(sorted(m1 + m2)); t = w.get(m, 0) + c1 * c2
            if t: w[m] = t
            else: w.pop(m, None)
    return w
RingA = dict(zero=PZERO, one=PONE, add=padd, mul=pmul)
FgA = {(ONE, ONE): pvar(0), (ONE, TAU): pvar(1), (TAU, ONE): pvar(2), (TAU, TAU): pvar(3)}

def Fs(K, F, a, b, c, d, x, y):
    if x in fuse(a, b) and d in fuse(x, c) and y in fuse(b, c) and d in fuse(a, y):
        if a == ONE or b == ONE or c == ONE: return K['one']
        if d == ONE:
            return K['one'] if x != ONE and y != ONE else K['zero']
        return F[(x, y)]
    return K['zero']

def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (x in fuse(a, b) and y in fuse(x, c) and t in fuse(y, dd) and
            w in fuse(c, dd) and v in fuse(b, w) and t in fuse(a, v))

def pent_residual_poly(tp):
    a, b, c, dd, x, y, t, w, v = tp
    lhs = PZERO
    for u in fuse(b, c):
        lhs = padd(lhs, pmul(pmul(Fs(RingA, FgA, a, b, c, y, x, u),
                                  Fs(RingA, FgA, a, u, dd, t, y, v)),
                             Fs(RingA, FgA, b, c, dd, v, u, w)))
    rhs = pmul(Fs(RingA, FgA, x, c, dd, t, y, w), Fs(RingA, FgA, a, b, w, t, x, v))
    return psub(lhs, rhs)

ALL = list(product(LABELS, repeat=9))
VALID = [tp for tp in ALL if pentagonValid(*tp)]
resid = {tp: pent_residual_poly(tp) for tp in VALID}
nonzero_t = [tp for tp in VALID if resid[tp]]
FILE11 = [(ONE,TAU,ONE,ONE,TAU),(ONE,TAU,ONE,TAU,TAU),(ONE,TAU,TAU,ONE,TAU),
          (ONE,TAU,TAU,TAU,ONE),(ONE,TAU,TAU,TAU,TAU),(TAU,ONE,TAU,ONE,TAU),
          (TAU,ONE,TAU,TAU,ONE),(TAU,TAU,ONE,ONE,TAU),(TAU,TAU,ONE,TAU,TAU),
          (TAU,TAU,TAU,ONE,TAU),(TAU,TAU,TAU,TAU,TAU)]
FILE11 = [(TAU,TAU,TAU,TAU) + t for t in FILE11]
check("V2.census_512_50_11", len(ALL) == 512 and len(VALID) == 50 and len(nonzero_t) == 11,
      f"total={len(ALL)}, live={len(VALID)}, nonzero-residual={len(nonzero_t)} (ties to round-3 P1)")
check("V2.indexing_matches_file", nonzero_t == FILE11,
      "the 11 in nest order == pent_at_01..11 tuples (round-3 P1.indexing)")
RES = [resid[tp] for tp in FILE11]                       # r_1..r_11

def pdiff(poly, i):
    out = {}
    for m, c in poly.items():
        k = m.count(i)
        if k:
            mm = list(m); mm.remove(i); mm = tuple(mm)
            t = out.get(mm, 0) + c * k
            if t: out[mm] = t
            else: out.pop(mm, None)
    return out

def peval(poly, pt):
    tot = E0
    for m, c in poly.items():
        v = EE(c)
        for i in m: v = v * pt[i]
        tot = tot + v
    return tot

# the golden point in E
pG  = EE(PHIM1)                       # p = phi - 1 = 1/phi
qG  = EE(Q5(0), PHIM1)                # q = (phi-1)*s
sPG = EE(-PHIM1)                      # sPar = -(phi-1)
GOLD = (pG, qG, qG, sPG)
check("V2.golden_q_is_inv_s", qG == sE.inv() and qG * qG == EE(PHIM1),
      "q = 1/s exactly (q = (phi-1)·s, q² = phi-1 = 1/phi)")
check("V2.golden_on_variety_shape", qG * qG == pG and sPG == -pG,
      "q·r = p and sPar = -p at the golden point (pentagon_iff shape)")
rvals = [peval(R, GOLD) for R in RES]
check("V2.golden_all_residuals_zero", all(v.is_zero() for v in rvals),
      "all 11 residuals vanish EXACTLY at the golden point (so 2JᵀJ is the true Hessian there)")

J = [[peval(pdiff(RES[i], j), GOLD) for j in range(4)] for i in range(11)]
H = [[sum((J[i][a] * J[i][b] for i in range(11)), E0) * 2 for b in range(4)] for a in range(4)]

# full symbolic Hessian of R = sum r_i^2, then equality with 2 JᵀJ
RSUM = PZERO
for R in RES: RSUM = padd(RSUM, pmul(R, R))
def full_hessian(pt):
    return [[peval(pdiff(pdiff(RSUM, a), b), pt) for b in range(4)] for a in range(4)]
HFULL_G = full_hessian(GOLD)
check("V2.hessian_is_2JtJ_golden",
      all(HFULL_G[a][b] == H[a][b] for a in range(4) for b in range(4)),
      "symbolic ∂²(Σrᵢ²) at golden == 2JᵀJ entrywise, exactly (no meta-step left)")
gradR = [peval(pdiff(RSUM, a), GOLD) for a in range(4)]
check("V2.golden_critical_point", all(g.is_zero() for g in gradR),
      "∇(Σrᵢ²) = 0 exactly at golden (it is a critical point)")

# float tie to the bench's own construction (informational, non-load-bearing)
def pent_p_float(pv):
    F = {(ONE, ONE): pv[0], (ONE, TAU): pv[1], (TAU, ONE): pv[2], (TAU, TAU): pv[3]}
    Kf = dict(zero=0.0, one=1.0, add=lambda x, y: x + y, mul=lambda x, y: x * y)
    tot = 0.0
    for tp in VALID:
        a, b, c, dd, x, y, t, w, v = tp
        lhs = sum(Fs(Kf, F, a, b, c, y, x, u) * Fs(Kf, F, a, u, dd, t, y, v)
                  * Fs(Kf, F, b, c, dd, v, u, w) for u in fuse(b, c))
        rhs = Fs(Kf, F, x, c, dd, t, y, w) * Fs(Kf, F, a, b, w, t, x, v)
        tot += (lhs - rhs) ** 2
    return tot
def hess_float(p0, h=1e-4):
    Hf = [[0.0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            def at(di, dj):
                pp = list(p0); pp[i] += di * h; pp[j] += dj * h
                return pent_p_float(pp)
            Hf[i][j] = (at(1, 1) - at(1, -1) - at(-1, 1) + at(-1, -1)) / (4 * h * h)
    return Hf
G_FL = [x.fl() for x in GOLD]
HF = hess_float(G_FL)
dev = max(abs(HF[a][b] - H[a][b].fl()) for a in range(4) for b in range(4))
check("V2.float_tie_to_bench", dev < 1e-4,
      f"bench-style central-difference Hessian vs exact H: max |Δ| = {dev:.2e} (float sanity only)")

# ======================================================================
# V3 — the theorem-shape facts, all exact
# ======================================================================
print()
print("== V3: theorem-shape facts (exact) ==")
VARN = ('p', 'q', 'r', 'sPar')

def show_H(Hm, tag):
    n_qs5 = 0; n_s = 0
    print(f"      H entries at {tag} (upper triangle, x + y·s form):")
    for a in range(4):
        for b in range(a, 4):
            e = Hm[a][b]
            kind = "Qs5" if e.y.is_zero() else "needs s"
            if e.y.is_zero(): n_qs5 += 1
            else: n_s += 1
            print(f"        H[{VARN[a]},{VARN[b]}] = {e}   [{kind}]")
    return n_qs5, n_s

# (a) symmetric, entries printed and classified
sym_ok = all(H[a][b] == H[b][a] for a in range(4) for b in range(4))
nq, ns = show_H(H, "GOLDEN")
check("V3a.symmetric_golden", sym_ok, "H = Hᵀ entrywise, exact")
pure = all((H[a][b].y.is_zero() if (a in (0, 3)) == (b in (0, 3)) else H[a][b].x.is_zero())
           for a in range(4) for b in range(4))
check("V3a.entry_fields_golden", nq + ns == 10 and pure,
      f"{nq} entries in Qs5, {ns} genuinely need s; exact block pattern: (p,sPar)x(p,sPar) and (q,r)x(q,r) in Qs5, cross block in Qs5·s")

# (b) torus tangent (0, q, -r, 0) is null
def matvec(M, v): return [sum((M[a][b] * v[b] for b in range(4)), E0) for a in range(4)]
vG = [E0, GOLD[1], -GOLD[2], E0]
check("V3b.tangent_null_golden", all(c.is_zero() for c in matvec(H, vG)),
      "H·(0, q, -r, 0)ᵀ = 0 exactly (gauge-torus tangent is null)")

# (c) rank exactly 3
def det(M):
    n = len(M)
    if n == 1: return M[0][0]
    tot = E0
    for j in range(n):
        sub = [row[:j] + row[j + 1:] for row in M[1:]]
        t = M[0][j] * det(sub)
        tot = tot + t if j % 2 == 0 else tot - t
    return tot
def minor(M, rows, cols): return [[M[a][b] for b in cols] for a in rows]
d4G = det(H)
m3G = det(minor(H, (0, 1, 3), (0, 1, 3)))
check("V3c.rank3_golden", d4G.is_zero() and not m3G.is_zero() and signE(m3G) == 1,
      f"det H = 0 and principal minor (p,q,sPar) = {m3G} > 0  ⇒ rank H = 3 exactly")

# (d) Sylvester on a complement: B = {e1, (0,q,r,0), e4}
def gram(Hm, B):
    return [[sum((sum((B[i][a] * Hm[a][b] for a in range(4)), E0) * B[j][b]
                  for b in range(4)), E0) for j in range(len(B))] for i in range(len(B))]
def sylvester(Hm, pt, tag):
    B = [[E1, E0, E0, E0], [E0, pt[1], pt[2], E0], [E0, E0, E0, E1]]
    G = gram(Hm, B)
    m1 = G[0][0]
    m2 = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    m3 = det(G)
    comp = det([[B[0][a], B[1][a], B[2][a], [E0, pt[1], -pt[2], E0][a]] for a in range(4)])
    print(f"      {tag} leading principal minors of G = BᵀHB:")
    print(f"        m1 = {m1}\n        m2 = {m2}\n        m3 = {m3}")
    print(f"        det[B|v] = {comp} (complement certificate)")
    # exact LDL of G — the sum-of-squares certificate a Lean proof would state
    d1 = m1; l21 = G[0][1] * m1.inv(); l31 = G[0][2] * m1.inv()
    d2 = m2 * m1.inv(); l32 = (G[1][2] - l31 * G[0][1]) * d2.inv()
    d3 = m3 * m2.inv()
    L = [[E1, E0, E0], [l21, E1, E0], [l31, l32, E1]]
    Dd = [d1, d2, d3]
    rec = [[sum((L[i][k] * Dd[k] * L[j][k] for k in range(3)), E0) for j in range(3)]
           for i in range(3)]
    ldl_ok = all(rec[i][j] == G[i][j] for i in range(3) for j in range(3))
    return G, (m1, m2, m3), comp, (Dd, (l21, l31, l32)), ldl_ok

G_G, minsG, compG, ldlG, ldlokG = sylvester(H, GOLD, "GOLDEN")
check("V3d.sylvester_golden",
      all(signE(m) == 1 for m in minsG) and not compG.is_zero(),
      "all three leading principal minors of BᵀHB POSITIVE by exact sign; {B, v} spans (det ≠ 0): H is PD on the complement")
check("V3d.ldl_golden", ldlokG and all(signE(d) == 1 for d in ldlG[0]),
      f"exact LDL: G = L·diag(d)·Lᵀ with d = {[str(d) for d in ldlG[0]]} all positive")

# end-to-end statement check: wᵀHw ≥ 0 with equality iff w ∈ span{(0,q,-r,0)}
def qform(Hm, w): return sum((sum((w[a] * Hm[a][b] for a in range(4)), E0) * w[b]
                              for b in range(4)), E0)
def in_span_tangent(w, pt):
    return (w[0].is_zero() and w[3].is_zero()
            and (w[1] * pt[2] + w[2] * pt[1]).is_zero())
def psd_kernel_probe(Hm, pt, nrand=40):
    ok = True
    tests = []
    for _ in range(nrand):
        w = [EE(Q5(rand_fr(), rand_fr()), Q5(rand_fr(), rand_fr())) for _ in range(4)]
        tests.append(w)
    v = [E0, pt[1], -pt[2], E0]
    tests += [[E0 + 3 * c for c in v], v,
              [v[0] + E1, v[1], v[2], v[3]],
              [E0, pt[1], pt[2], E0]]
    for w in tests:
        val = qform(Hm, w); s = signE(val)
        if s < 0: ok = False
        if (s == 0) != in_span_tangent(w, pt): ok = False
    return ok, len(tests)
okp, ntest = psd_kernel_probe(H, GOLD)
check("V3d.psd_kernel_statement_golden", okp,
      f"{ntest} exact probes (random E-vectors + planted): wᵀHw ≥ 0, and = 0 exactly on span of the tangent")

# (computed here because (e) compares golden/YL row structure)
YL = (EE(-PHI5), EE(1), EE(-PHI5), EE(PHI5))
JY = [[peval(pdiff(RES[i], j), YL) for j in range(4)] for i in range(11)]
HY = [[sum((JY[i][a] * JY[i][b] for i in range(11)), E0) * 2 for b in range(4)] for a in range(4)]

# (e) the control study.  FINDING (refutes the task's expected certificate):
#     the strict associator is PSD-with-null-exactly-tangent DESPITE being a
#     non-solution.  Root cause: the residual sum is q<->r swap-symmetric, so
#     at ANY q = r point rows q and r of H coincide and (0,q,-r,0) is null for
#     free.  A q != r non-solution, (1,2,3,-1), supplies the working control.
print()
def swapqr_poly(poly):
    out = {}
    for m, c in poly.items():
        mm = tuple(sorted(({1: 2, 2: 1}.get(i, i)) for i in m))
        out[mm] = out.get(mm, 0) + c
    return {m: c for m, c in out.items() if c}
rows_qr_same_gold = all(H[1][b] == H[2][b] for b in range(4))
rows_qr_same_yl = all(HY[1][b] == HY[2][b] for b in range(4))
check("V3e.swap_symmetry", swapqr_poly(RSUM) == RSUM and rows_qr_same_gold
      and not rows_qr_same_yl,
      "Σrᵢ² is q↔r swap-invariant (symbolic); hence at ANY q=r point rows q,r of H coincide "
      "and (0,q,-r,0) is null FOR FREE — true at golden (rows equal), not at Yang–Lee (rows differ): "
      "at YL 'null = gauge tangent' carries independent content")

STRICT = tuple(EE(1) for _ in range(4))
rstr = [peval(R, STRICT) for R in RES]
n_nonzero_str = sum(0 if v.is_zero() else 1 for v in rstr)
HS = full_hessian(STRICT)                                # honest full Hessian, integer
JS = [[peval(pdiff(RES[i], j), STRICT) for j in range(4)] for i in range(11)]
H2S = [[sum((JS[i][a] * JS[i][b] for i in range(11)), E0) * 2 for b in range(4)] for a in range(4)]
gauss_newton_differs = any(HS[a][b] != H2S[a][b] for a in range(4) for b in range(4))
gradS = [peval(pdiff(RSUM, a), STRICT) for a in range(4)]
vS = [E0, STRICT[1], -STRICT[2], E0]
HvS_zero = all(c.is_zero() for c in matvec(HS, vS))
d4S = det(HS); m3S = det(minor(HS, (0, 1, 3), (0, 1, 3)))
G_S, minsS, compS, ldlS, ldlokS = sylvester(HS, STRICT, "STRICT (1,1,1,1)")
strict_is_psd_null_tangent = (HvS_zero and d4S.is_zero() and signE(m3S) == 1
                              and all(signE(m) == 1 for m in minsS)
                              and not compS.is_zero())
info(f"strict point facts: {n_nonzero_str}/11 residuals NONZERO (values {[str(v.x.a) for v in rstr]}),")
info(f"grad = {[str(g.x.a) for g in gradS]} ≠ 0, full Hessian ≠ 2JᵀJ: {gauss_newton_differs} "
     f"(Gauss–Newton gap nonzero) — yet the signature battery PASSES there:")
check("V3e.strict_REFUTES_expected_control", n_nonzero_str == 8 and gauss_newton_differs
      and strict_is_psd_null_tangent,
      "REFUTATION (exact): at the strict associator H IS PSD with null EXACTLY span(0,1,-1,0) "
      "— H·v = 0, det=0, minor>0, Sylvester minors positive.  Both certificates the task "
      "expected (negative direction / H·v ≠ 0) FAIL.  The signature does NOT detect "
      "solutionhood; the theorem's 'all residuals vanish' hypothesis is load-bearing")

# the WORKING negative control: q != r non-solution (1, 2, 3, -1)
CTRL = (EE(1), EE(2), EE(3), EE(-1))
rctl = [peval(R, CTRL) for R in RES]
HC = full_hessian(CTRL)
vC = [E0, CTRL[1], -CTRL[2], E0]                          # (0, 2, -3, 0)
HvC = matvec(HC, vC)
wneg = [EE(-3), EE(-3), EE(3), EE(-1)]                    # found by exact search
wval = qform(HC, wneg)
check("V3e.negctrl_working", sum(0 if v.is_zero() else 1 for v in rctl) > 0
      and not all(c.is_zero() for c in HvC) and signE(wval) == -1,
      f"at (1,2,3,-1): H·(0,q,-r,0) = {[str(c.x.a) for c in HvC]} ≠ 0 AND "
      f"w = (-3,-3,3,-1) gives wᵀHw = {wval} < 0 (exact) — NOT PSD, null ≠ tangent: "
      "the construction genuinely fails off the variety once the q=r symmetry crutch is removed")

# (f) the Yang–Lee point (-phi, 1, -phi, phi) — same structure, exact
print()
check("V3f.yl_matches_r5_instrument", [x.fl() for x in YL] ==
      [-(1 + sqrt(5)) / 2, 1.0, -(1 + sqrt(5)) / 2, (1 + sqrt(5)) / 2],
      "point == r5_g3_hessian_gauge.py line 138: YL = (-PHI, 1.0, -PHI, PHI)")
check("V3f.yl_on_variety_shape", YL[1] * YL[2] == YL[0] and YL[3] == -YL[0],
      "q·r = p and sPar = -p at Yang–Lee")
rylv = [peval(R, YL) for R in RES]
check("V3f.yl_all_residuals_zero", all(v.is_zero() for v in rylv),
      "all 11 residuals vanish EXACTLY at Yang–Lee")
HFULL_Y = full_hessian(YL)
check("V3f.hessian_is_2JtJ_yl",
      all(HFULL_Y[a][b] == HY[a][b] for a in range(4) for b in range(4)),
      "symbolic Hessian == 2JᵀJ at Yang–Lee, exact")
nqY, nsY = show_H(HY, "YANG-LEE")
check("V3f.yl_entries_in_Qs5", all(HY[a][b].y.is_zero() for a in range(4) for b in range(4))
      and all(HY[a][b] == HY[b][a] for a in range(4) for b in range(4)),
      f"symmetric; ALL {nqY + nsY} entries in Qs5 — no radical at Yang–Lee (q = 1 rational)")
vY = [E0, YL[1], -YL[2], E0]                             # = (0, 1, phi, 0)
check("V3f.tangent_null_yl", all(c.is_zero() for c in matvec(HY, vY)),
      "H·(0, q, -r, 0)ᵀ = H·(0, 1, φ, 0)ᵀ = 0 exactly")
d4Y = det(HY); m3Y = det(minor(HY, (0, 1, 3), (0, 1, 3)))
check("V3f.rank3_yl", d4Y.is_zero() and not m3Y.is_zero() and signE(m3Y) == 1,
      f"det H = 0, principal minor (p,q,sPar) = {m3Y} > 0 ⇒ rank 3")
G_Y, minsY, compY, ldlY, ldlokY = sylvester(HY, YL, "YANG-LEE")
check("V3f.sylvester_yl", all(signE(m) == 1 for m in minsY) and not compY.is_zero(),
      "three leading principal minors of BᵀHB positive, complement spans — PSD with null exactly the tangent")
check("V3f.ldl_yl", ldlokY and all(signE(d) == 1 for d in ldlY[0]), "exact LDL positive at YL")
okpY, ntestY = psd_kernel_probe(HY, YL)
check("V3f.psd_kernel_statement_yl", okpY,
      f"{ntestY} exact probes: wᵀHw ≥ 0 with equality exactly on span(0,1,φ,0)")
# swap-confound control: at YL q ≠ r, and the SWAP direction (0,1,-1,0) is NOT null
swap = [E0, E1, -E1, E0]
Hswap = matvec(HY, swap)
check("V3f.negctrl_swap_not_null", YL[1] != YL[2] and not all(c.is_zero() for c in Hswap)
      and signE(qform(HY, swap)) == 1,
      "at YL the q↔r swap direction (0,1,-1,0) has H·w ≠ 0 and wᵀHw > 0: the null mode is the GAUGE tangent, not the swap symmetry")

# informational float eigenvalues (signature {0,+,+,+} as the bench states it)
try:
    import numpy as np
    for tag, Hm in (("golden", H), ("yang-lee", HY)):
        w = np.linalg.eigvalsh(np.array([[Hm[a][b].fl() for b in range(4)] for a in range(4)]))
        info(f"float eigenvalues at {tag}: {[round(float(x), 6) for x in w]}  (bench signature {{0,+,+,+}}, w1 > 0.05: {abs(w[0]) < 1e-9 and w[1] > 0.05})")
except Exception as ex:
    info(f"numpy unavailable ({ex}); float eigen display skipped (informational only)")

# ======================================================================
# V4 — Lean-cost estimate, honest
# ======================================================================
print()
print("== V4: Lean cost — constants, cleared-denominator integer forms, decide route ==")

from math import gcd
def clear_den(e):
    """E element -> (A,B,C,D,L): ((A+B√5)+(C+D√5)s)/L, ints, L>0 minimal."""
    fr = (e.x.a, e.x.b, e.y.a, e.y.b)
    L = 1
    for f in fr:
        L = L * f.denominator // gcd(L, f.denominator)
    return tuple(int(f * L) for f in fr) + (L,)

consts_G = {H[a][b] for a in range(4) for b in range(4)}
consts_Y = {HY[a][b] for a in range(4) for b in range(4)}
nzG = {c for c in consts_G if not c.is_zero()}
nzY = {c for c in consts_Y if not c.is_zero()}
info(f"distinct H entries: golden {len(consts_G)} ({len(nzG)} nonzero), yang-lee {len(consts_Y)} ({len(nzY)} nonzero), union {len(consts_G | consts_Y)}")

LOAD = [("golden.m1", minsG[0]), ("golden.m2", minsG[1]), ("golden.m3", minsG[2]),
        ("golden.minor3", m3G), ("golden.det4", d4G), ("golden.comp", compG),
        ("yl.m1", minsY[0]), ("yl.m2", minsY[1]), ("yl.m3", minsY[2]),
        ("yl.minor3", m3Y), ("yl.det4", d4Y), ("yl.comp", compY)]
maxbits = 0; maxden = 1
print("      cleared-denominator integer forms  ((A+B√5)+(C+D√5)·s)/L :")
for name, e in LOAD:
    A, B, C, Dc, L = clear_den(e)
    bits = max(abs(x).bit_length() for x in (A, B, C, Dc, L))
    maxbits = max(maxbits, bits); maxden = max(maxden, L)
    print(f"        {name:14s} A={A} B={B} C={C} D={Dc} L={L}   ({bits} bits)")
allbits = [max(abs(x).bit_length() for x in clear_den(H[a][b])) for a in range(4) for b in range(4)]
allbitsY = [max(abs(x).bit_length() for x in clear_den(HY[a][b])) for a in range(4) for b in range(4)]
info(f"H entries: max coordinate bit length golden {max(allbits)}, yang-lee {max(allbitsY)}; largest denominator over all load-bearing objects: {maxden}")
check("V4.small_integers", maxbits <= 24 and maxden == 1,
      f"every load-bearing object is ALREADY INTEGRAL in the basis (1,√5)⊕(1,√5)·s (all L = {maxden}, no clearing needed), "
      f"coordinates ≤ {maxbits} bits — the squares the sign procedure compares stay under {2 * maxbits + 3} bits: decide-sized")

# the decide route itself, integers only (no Fractions) — the Lean simulation
def sign_q5_int(a, b):
    if a == 0 and b == 0: return 0
    if a >= 0 and b >= 0: return 1
    if a <= 0 and b <= 0: return -1
    c = a * a - 5 * b * b
    assert c != 0
    return (1 if c > 0 else -1) if a > 0 else (-1 if c > 0 else 1)
def sign_E_int(A, B, C, Dc):
    sx, sy = sign_q5_int(A, B), sign_q5_int(C, Dc)
    if sx == 0 and sy == 0: return 0
    if sx >= 0 and sy >= 0: return 1
    if sx <= 0 and sy <= 0: return -1
    xa, xb = A * A + 5 * B * B, 2 * A * B                 # x² in Z[√5]
    ya, yb = C * C + 5 * Dc * Dc, 2 * C * Dc              # y²
    ca, cb = 2 * xa - (ya + 5 * yb), 2 * xb - (ya + yb)   # 2x² - (1+√5)y²
    sc = sign_q5_int(ca, cb)
    assert sc != 0
    return (1 if sc > 0 else -1) if sx > 0 else (-1 if sc > 0 else 1)
dec_ok = True
for name, e in LOAD:
    A, B, C, Dc, L = clear_den(e)
    if sign_E_int(A, B, C, Dc) != signE(e): dec_ok = False
check("V4.integer_decide_route", dec_ok,
      "pure-Int two-layer sign (a² vs 5b², then 2x² vs (1+√5)y²) agrees with the Fraction instrument on all 12 load-bearing objects — exactly the chain a Lean `decide`/`omega` proof runs")

info("calibration: Anyon.lean round-5 order block (lines 5639-6777) = 102 theorems + 16 defs for ONE square root (PosP over Int pairs).")
info("estimate for the round-6 gift, zero-imports file style, reusing Ord5/PosP verbatim:")
info("  (1) E as Int 4-tuples (cleared denominators) + ring ops:            ~8 defs")
info("  (2) sqrt(phi) ∉ Q(√5) analog (x² = φy² ⇒ 0) via conjugate + PosP:  ~6-10 thms")
info("  (3) PosE closure (add/mul/trichotomy, mixed case via PosP):        ~30-40 thms (mirrors posP block)")
info("  (4) per-world certificates (entries, Hv=0, 3 minors, det4, minor3): ~12-16 decides × 2 worlds")
info("  (5) PSD+kernel assembly (LDL identity, span decomposition):         ~10-15 thms")
info("  (6) negative controls — the q≠r point (1,2,3,-1) is ALL-INTEGER (Hv≠0 and wᵀHw<0 are Int decides, ~3 thms);")
info("      plus the strict-associator PSD surprise as a named remark/lemma (~2): ~5 thms")
info("  TOTAL ≈ 90-130 theorems, ~1,100-1,600 lines — one round of work at the file's cadence, same order as the d_τ block.")
info("assumptions: H is DEFINED as 2JᵀJ of formal PentPoly gradients (derivative def is structural recursion, ~3 defs; V2 above")
info("checked full-Hessian == 2JᵀJ exactly, so nothing analytic is smuggled); statement quantifies over E⁴ 4-tuples;")
info("no reals, no analysis — every inequality lands on PosP over Int.")

# ======================================================================
# V5 — the sentence for the charge
# ======================================================================
print()
print("== V5: what the round-6 theorem would and would not say ==")
V5 = """  THE THEOREM WOULD SAY: at each of the two pentagon worlds (golden
  p = 1/φ and Yang–Lee p = -φ), the exact 4x4 matrix H = 2JᵀJ — the
  Hessian, computed exactly, of the pentagon sum-of-squares residual that
  grammar_stone5.py measures numerically — is positive semidefinite over
  the ordered field Q(√5)(√φ), and its null space is EXACTLY the span of
  the gauge-torus tangent (0, q, -r, 0): every direction that moves off
  the gauge orbit has strictly positive quadratic cost, and the one flat
  direction is precisely the gauge reparameterization pentagon_iff already
  names.  The bench's asserted signature {0,+,+,+} and its null-vector
  overlap test become kernel-checked facts AT the two exact solutions: the
  dial's stiffness and its one flat direction are theorems, decided by
  integer arithmetic through the same PosP order that named d_τ = φ, and
  the Yang–Lee half (q ≠ r) is where 'the flat direction is the GAUGE
  tangent, not the q↔r swap' carries content beyond symmetry.
  IT WOULD NOT SAY: anything about basins, gradient dynamics, convergence
  of any search, global minimality, or behaviour anywhere off the two
  solution points — it is the second-order germ at the exact solutions
  ONLY.  And it would NOT say the signature detects solutionhood: this
  audit's V3e finding is that the strict associator (1,1,1,1), a
  non-solution with 8/11 residuals alive, ALSO has H exactly PSD with null
  exactly the would-be tangent (a q↔r symmetry freebie).  The 'point is a
  solution' hypothesis is load-bearing and must stay in the statement."""
print(V5)

print()
nfail = sum(1 for _, ok in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  ({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
