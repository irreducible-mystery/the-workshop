#!/usr/bin/env python3
"""r6s_jets_check.py — round-6 SEAT: INDEPENDENT JET RECOMPUTATION.

The strongest cross-check available this round: implement Rigidity.lean's own
second-order jet ring J2 (15 fields), its SS (pentagon sum-of-squares over all
512 label tuples) and pentResid IN PYTHON, transcribed EXACTLY — same field
layout (v, d0..d3, e00,e01,e02,e03,e11,e12,e13,e22,e23,e33), same truncated
Leibniz products (diagonal slot eII gets ONE dI*dI term; off-diagonal eIJ gets
dI*dJ + dJ*dI), same diagonal convention (hessOf doubles diagonals: the eps_i^2
coefficient is (1/2)*d2f/dxi^2) — and RACE it against the builder certificate
pack audit/r6_gift_hessian.py, whose route is symbolic polynomial
differentiation of RSUM = sum of the 11 residual squares (a route that knows
nothing about jets).

TWO INDEPENDENT ROUTES, ENTRY BY ENTRY:
  route A  = the Lean file's jets, transcribed from Rigidity.lean §0+§3
             (source pinned by sha256 d67d6437... and by definitional anchors);
  route B  = the builder's sparse-poly d2(RSUM), copied from r6_gift_hessian.py
             V2 (pconst/pvar/padd/pmul/pdiff/peval + the Q5/EE exact field
             classes — the E = Q(sqrt5)(sqrt phi) layer is implemented exactly
             as in that pack, per the seat instruction).

POINTS RACED: golden (1/phi, 1/sqrt(phi), 1/sqrt(phi), -1/phi) over E (twice:
the pack's EE Fraction arithmetic AND the Lean file's Ep = Z[phi][sqrt phi]
integer-pair arithmetic); Yang-Lee (-phi, 1, -phi, phi) over Zp = Z[phi];
strict (1,1,1,1) and control (1,2,3,-1) over plain Python ints (the jet ring
is generic over any Rng record, exactly as in the file).

CHECKS: J1 transcription + germ literals (GY/GG/GC/GS); J2 entrywise race at
golden/YL/control incl. the quoted certificate values (26-4sqrt5 ... , 40+10sqrt5
... , Hv=(-20,-212,138,40), wHw=-400); J3 the swap value 34+52phi = 60+26sqrt5;
J4 gradient receipts (zero at both worlds, nonzero at control and strict
(24,20,20,26)); J5 the ten golden gg_e values against certificate H entries
with the convention mapping H_ii = 2*e_ii, H_ij = e_ij (i != j), verified to be
the one the file documents; J6 negative controls (perturbed jet seed, wrong
Leibniz, undoubled diagonal, wrong Zp multiplication, random non-critical
points).  EXACT ARITHMETIC ONLY (int / Fraction).  No third-party deps.
"""
import sys, os, random, hashlib
from fractions import Fraction as Fr
from itertools import product

random.seed(20260723)
results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
def info(msg):
    print(f"      {msg}")

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "Rigidity.lean")

# ======================================================================
# S0 — pin the source this transcription was made from
# ======================================================================
print("== S0: source pin ==")
LEDGER_SHA = "d67d643778a3140554b47293f7177ddaab256851ecd52317d77ce69927748dcd"
try:
    src = open(LEAN, "rb").read()
    sha = hashlib.sha256(src).hexdigest()
    check("r6s.pin.source_hash", sha == LEDGER_SHA,
          f"sha256(Rigidity.lean) = {sha[:16]}... == PROOFS.md round-6 ledger value: {sha == LEDGER_SHA}")
    txt = src.decode("utf-8")
except OSError as ex:
    check("r6s.pin.source_hash", False, f"cannot read {LEAN}: {ex}")
    txt = ""

# definitional anchors: the exact lines the transcription below copies
ANCHORS = {
    "J2 fields (layout)": "structure J2 (R : Type) where",
    "diagonal Leibniz e00 (ONE d0*d0 term)":
        "K.add (K.add (K.mul u.v w.e00) (K.mul u.e00 w.v)) (K.mul u.d0 w.d0)",
    "off-diagonal Leibniz e01 (d0*d1 + d1*d0)":
        "K.add (K.mul u.d0 w.d1) (K.mul u.d1 w.d0)",
    "hessOf doubling docstring": "Diagonal entries are doubled because the",
    "convention line (1/2 factor)": "coefficient of a function is",
    "documented convention Hii=2eii":
        "∂²/∂xᵢ² = 2·eᵢᵢ",
    "documented convention Hij=eij":
        "∂²/∂xᵢ∂xⱼ = eᵢⱼ",
    "seed jp (dK = one)": "if k == 0 then K.one else K.zero",
    "Zp mul (phi^2 = phi + 1)":
        "u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n",
    "Ep mul (s^2 = phi)":
        "Zp.add (Zp.mul u.x v.x) (Zp.mul Zp.phi (Zp.mul u.y v.y))",
}
miss = [k for k, v in ANCHORS.items() if v not in txt]
check("r6s.pin.anchor_definitions", not miss,
      "10/10 definitional anchor strings found verbatim in Rigidity.lean"
      if not miss else f"MISSING anchors: {miss}")

# ======================================================================
# ROUTE-B FIELD LAYER — Q5 = Q(sqrt5), EE = Q5(sqrt phi), copied exactly
# from audit/r6_gift_hessian.py V1 (the pack's E-layer implementation)
# ======================================================================
class Q5:
    """a + b*sqrt5, a,b Fraction.  [= r6_gift_hessian.py class Q5]"""
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
    def __repr__(self):
        return f"({self.a}{'+' if self.b >= 0 else ''}{self.b}~5)"

def sign5(x):
    a, b = x.a, x.b
    if a == 0 and b == 0: return 0
    if a >= 0 and b >= 0: return 1
    if a <= 0 and b <= 0: return -1
    c = a * a - 5 * b * b
    if c == 0: raise AssertionError("sqrt5 rational?!")
    return (1 if c > 0 else -1) if a > 0 else (-1 if c > 0 else 1)

PHI5  = Q5(Fr(1, 2), Fr(1, 2))
PHIM1 = PHI5 - Q5(1)
assert PHI5 * PHI5 == PHI5 + Q5(1)

class EE:
    """x + y*s with s = sqrt(phi); s^2 = phi.  [= r6_gift_hessian.py class EE]"""
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
    def __repr__(self):
        if self.y.is_zero(): return f"{self.x}"
        return f"[{self.x} + {self.y}*s]"

EE0, EE1 = EE(0), EE(1)

def signE(x):
    sx, sy = sign5(x.x), sign5(x.y)
    if sx == 0 and sy == 0: return 0
    if sx >= 0 and sy >= 0: return 1
    if sx <= 0 and sy <= 0: return -1
    c = x.x * x.x - PHI5 * (x.y * x.y)
    sc = sign5(c)
    if sc == 0: raise AssertionError("sqrt(phi) in Q(sqrt5)?!")
    return (1 if sc > 0 else -1) if sx > 0 else (-1 if sc > 0 else 1)

# basis conversions: Lean's Zp (m,n) means m + n*phi; phi = (1+sqrt5)/2
def zp2q5(z):
    m, n = z
    return Q5(Fr(2 * m + n, 2), Fr(n, 2))
def ep2ee(e):
    (xm, xn), (ym, yn) = e
    return EE(zp2q5((xm, xn)), zp2q5((ym, yn)))

# ======================================================================
# ROUTE A — the Lean file's pentagon machinery + J2 jets, transcribed EXACTLY
# (Rigidity.lean §0 and §3; every formula follows the source text)
# ======================================================================
ONE, TAU = 0, 1
allA = [ONE, TAU]                                # allA : List Anyon = [.one, .tau]

def fuse(a, b):                                  # fuse
    if a == ONE: return [b]
    if b == ONE: return [a]
    return [ONE, TAU]

def memA(a, lst):                                # memA (Boolean member)
    for x in lst:
        if a == x: return True
    return False

def isOne(a):                                    # isOne
    return a == ONE

class Rng:                                       # structure Rng (zero one add neg mul)
    __slots__ = ('zero', 'one', 'add', 'neg', 'mul')
    def __init__(self, zero, one, add, neg, mul):
        self.zero, self.one, self.add, self.neg, self.mul = zero, one, add, neg, mul

def sumOver(K, f, lst):                          # sumOver: f u + sumOver us (right fold)
    if not lst: return K.zero
    return K.add(f(lst[0]), sumOver(K, f, lst[1:]))

def Fs(K, F, a, b, c, d, x, y):                  # Fs — the F-move
    if (memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and
            memA(y, fuse(b, c)) and memA(d, fuse(a, y))):
        if isOne(a) or isOne(b) or isOne(c): return K.one
        if isOne(d):
            return K.one if ((not isOne(x)) and (not isOne(y))) else K.zero
        return F(x, y)
    return K.zero

def pentagonValid(a, b, c, dd, x, y, t, w, v):   # pentagonValid
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and memA(t, fuse(y, dd)) and
            memA(w, fuse(c, dd)) and memA(v, fuse(b, w)) and memA(t, fuse(a, v)))

def Fg(p, q, r, sp):                             # Fg — generic associator [[p,q],[r,s]]
    tbl = {(ONE, ONE): p, (ONE, TAU): q, (TAU, ONE): r, (TAU, TAU): sp}
    return lambda x, y: tbl[(x, y)]

def pentResid(K, F, a, b, c, dd, x, y, t, w, v):  # pentResid = LHS - RHS
    lhs = sumOver(K, lambda u: K.mul(K.mul(Fs(K, F, a, b, c, y, x, u),
                                           Fs(K, F, a, u, dd, t, y, v)),
                                     Fs(K, F, b, c, dd, v, u, w)), fuse(b, c))
    return K.add(lhs, K.neg(K.mul(Fs(K, F, x, c, dd, t, y, w),
                                  Fs(K, F, a, b, w, t, x, v))))

def sqResid(K, F, a, b, c, dd, x, y, t, w, v):   # sqResid (guard, then square)
    if pentagonValid(a, b, c, dd, x, y, t, w, v):
        R = pentResid(K, F, a, b, c, dd, x, y, t, w, v)   # Lean writes the call twice;
        return K.mul(R, R)                                # same pure value, computed once
    return K.zero

def SS(K, F):                                    # SS — nine nested sums, order a b c dd x y t w v
    return sumOver(K, lambda a:
           sumOver(K, lambda b:
           sumOver(K, lambda c:
           sumOver(K, lambda dd:
           sumOver(K, lambda x:
           sumOver(K, lambda y:
           sumOver(K, lambda t:
           sumOver(K, lambda w:
           sumOver(K, lambda v: sqResid(K, F, a, b, c, dd, x, y, t, w, v),
                   allA), allA), allA), allA), allA), allA), allA), allA), allA)

# --- the coefficient rings, exactly as in the file --------------------
# Zp = Z[phi] as (m,n) meaning m + n*phi, phi^2 = phi + 1
def zadd(u, v): return (u[0] + v[0], u[1] + v[1])
def zneg(u):    return (-u[0], -u[1])
def zmul(u, v):                                  # (ac+bd, ad+bc+bd)
    return (u[0] * v[0] + u[1] * v[1],
            u[0] * v[1] + u[1] * v[0] + u[1] * v[1])
ZP0, ZP1, ZPHI = (0, 0), (1, 0), (0, 1)
zpRng = Rng(ZP0, ZP1, zadd, zneg, zmul)

# Ep = Z[phi][s]/(s^2 - phi) as (x,y) of Zp, meaning x + y*s
def eadd(u, v): return (zadd(u[0], v[0]), zadd(u[1], v[1]))
def eneg(u):    return (zneg(u[0]), zneg(u[1]))
def emul(u, v):                                  # (x1x2 + phi*(y1y2), x1y2 + y1x2)
    return (zadd(zmul(u[0], v[0]), zmul(ZPHI, zmul(u[1], v[1]))),
            zadd(zmul(u[0], v[1]), zmul(u[1], v[0])))
EP0, EP1 = (ZP0, ZP0), (ZP1, ZP0)
epRng = Rng(EP0, EP1, eadd, eneg, emul)

intRng = Rng(0, 1, lambda a, b: a + b, lambda a: -a, lambda a, b: a * b)
eeRng  = Rng(EE0, EE1, lambda a, b: a + b, lambda a: -a, lambda a, b: a * b)

# --- J2, the 15-field second-order jet ring (§3), field layout as source ---
# index:  0  1  2  3  4   5   6   7   8   9  10  11  12  13  14
# field:  v d0 d1 d2 d3 e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
FIELD = ('v','d0','d1','d2','d3','e00','e01','e02','e03','e11','e12','e13','e22','e23','e33')

def j2Rng(K, wrong_leibniz_e01=False):
    zero = tuple([K.zero] * 15)
    one  = tuple([K.one] + [K.zero] * 14)
    def add(u, w): return tuple(K.add(u[i], w[i]) for i in range(15))
    def neg(u):    return tuple(K.neg(u[i]) for i in range(15))
    def mul(u, w):
        A, M = K.add, K.mul
        v   = M(u[0], w[0])
        d0  = A(M(u[0], w[1]), M(u[1], w[0]))
        d1  = A(M(u[0], w[2]), M(u[2], w[0]))
        d2  = A(M(u[0], w[3]), M(u[3], w[0]))
        d3  = A(M(u[0], w[4]), M(u[4], w[0]))
        e00 = A(A(M(u[0], w[5]),  M(u[5],  w[0])), M(u[1], w[1]))
        if wrong_leibniz_e01:      # NEGATIVE CONTROL: drop the d0*d1+d1*d0 cross term
            e01 = A(M(u[0], w[6]), M(u[6], w[0]))
        else:
            e01 = A(A(M(u[0], w[6]),  M(u[6],  w[0])), A(M(u[1], w[2]), M(u[2], w[1])))
        e02 = A(A(M(u[0], w[7]),  M(u[7],  w[0])), A(M(u[1], w[3]), M(u[3], w[1])))
        e03 = A(A(M(u[0], w[8]),  M(u[8],  w[0])), A(M(u[1], w[4]), M(u[4], w[1])))
        e11 = A(A(M(u[0], w[9]),  M(u[9],  w[0])), M(u[2], w[2]))
        e12 = A(A(M(u[0], w[10]), M(u[10], w[0])), A(M(u[2], w[3]), M(u[3], w[2])))
        e13 = A(A(M(u[0], w[11]), M(u[11], w[0])), A(M(u[2], w[4]), M(u[4], w[2])))
        e22 = A(A(M(u[0], w[12]), M(u[12], w[0])), M(u[3], w[3]))
        e23 = A(A(M(u[0], w[13]), M(u[13], w[0])), A(M(u[3], w[4]), M(u[4], w[3])))
        e33 = A(A(M(u[0], w[14]), M(u[14], w[0])), M(u[4], w[4]))
        return (v, d0, d1, d2, d3, e00, e01, e02, e03, e11, e12, e13, e22, e23, e33)
    return Rng(zero, one, add, neg, mul)

def jp(K, a, k, seed_e00=False, seed_d0=False):  # jp — coordinate with its own infinitesimal
    j = [a] + [K.one if k == i else K.zero for i in range(4)] + [K.zero] * 10
    if seed_e00:                                 # NEGATIVE CONTROL: second-order seed (x + eps_k + eps_0^2)
        j[5] = K.one
    if seed_d0:                                  # NEGATIVE CONTROL: first-order shear (x + eps_k + eps_0)
        j[1] = K.one
    return tuple(j)

def germ(K, p, q, r, sp, **kw):                  # germ = SS over jets at (p+e0,q+e1,r+e2,s+e3)
    JR = j2Rng(K, wrong_leibniz_e01=kw.get('wrong_leibniz_e01', False))
    se = kw.get('seed_e00_on_k', None)
    sd = kw.get('seed_d0_on_k', None)
    F = Fg(jp(K, p, 0, seed_e00=(se == 0), seed_d0=(sd == 0)),
           jp(K, q, 1, seed_e00=(se == 1), seed_d0=(sd == 1)),
           jp(K, r, 2, seed_e00=(se == 2), seed_d0=(sd == 2)),
           jp(K, sp, 3, seed_e00=(se == 3), seed_d0=(sd == 3)))
    return SS(JR, F)

def hessOf(K, g, double_diag=True):              # hessOf — diagonals doubled (file convention)
    E = {(0,0):5,(0,1):6,(0,2):7,(0,3):8,(1,1):9,(1,2):10,(1,3):11,(2,2):12,(2,3):13,(3,3):14}
    def entry(a, b):
        i, j = (a, b) if a <= b else (b, a)
        v = g[E[(i, j)]]
        if a == b and double_diag: return K.add(v, v)
        return v
    return [[entry(a, b) for b in range(4)] for a in range(4)]

def gradOf(g):                                   # gradOf — the four first-order slots
    return (g[1], g[2], g[3], g[4])

# ======================================================================
# ROUTE B — the builder's symbolic differentiation, copied from
# r6_gift_hessian.py V2 (sparse poly ring over Z[p,q,r,sPar])
# ======================================================================
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

def FsB(K, F, a, b, c, d, x, y):                 # builder's Fs (dict-valued F)
    if x in fuse(a, b) and d in fuse(x, c) and y in fuse(b, c) and d in fuse(a, y):
        if a == ONE or b == ONE or c == ONE: return K['one']
        if d == ONE:
            return K['one'] if x != ONE and y != ONE else K['zero']
        return F[(x, y)]
    return K['zero']

def pent_residual_poly(tp):
    a, b, c, dd, x, y, t, w, v = tp
    lhs = PZERO
    for u in fuse(b, c):
        lhs = padd(lhs, pmul(pmul(FsB(RingA, FgA, a, b, c, y, x, u),
                                  FsB(RingA, FgA, a, u, dd, t, y, v)),
                             FsB(RingA, FgA, b, c, dd, v, u, w)))
    rhs = pmul(FsB(RingA, FgA, x, c, dd, t, y, w), FsB(RingA, FgA, a, b, w, t, x, v))
    return psub(lhs, rhs)

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
    tot = EE0
    for m, c in poly.items():
        v = EE(c)
        for i in m: v = v * pt[i]
        tot = tot + v
    return tot

ALLT  = list(product((ONE, TAU), repeat=9))
VALID = [tp for tp in ALLT if pentagonValid(*tp)]
resid = {tp: pent_residual_poly(tp) for tp in VALID}
nonzero_t = [tp for tp in VALID if resid[tp]]
FILE11 = [(ONE,TAU,ONE,ONE,TAU),(ONE,TAU,ONE,TAU,TAU),(ONE,TAU,TAU,ONE,TAU),
          (ONE,TAU,TAU,TAU,ONE),(ONE,TAU,TAU,TAU,TAU),(TAU,ONE,TAU,ONE,TAU),
          (TAU,ONE,TAU,TAU,ONE),(TAU,TAU,ONE,ONE,TAU),(TAU,TAU,ONE,TAU,TAU),
          (TAU,TAU,TAU,ONE,TAU),(TAU,TAU,TAU,TAU,TAU)]
FILE11 = [(TAU,TAU,TAU,TAU) + t for t in FILE11]
RES = [resid[tp] for tp in FILE11]
RSUM = PZERO
for R in RES: RSUM = padd(RSUM, pmul(R, R))

def full_hessian(pt):                            # builder's d2(RSUM) — TRUE second partials
    return [[peval(pdiff(pdiff(RSUM, a), b), pt) for b in range(4)] for a in range(4)]
def full_grad(pt):
    return [peval(pdiff(RSUM, a), pt) for a in range(4)]

# builder's determinant/minor over EE
def detEE(M):
    n = len(M)
    if n == 1: return M[0][0]
    tot = EE0
    for j in range(n):
        sub = [row[:j] + row[j + 1:] for row in M[1:]]
        t = M[0][j] * detEE(sub)
        tot = tot + t if j % 2 == 0 else tot - t
    return tot
def minor(M, rows, cols): return [[M[a][b] for b in cols] for a in rows]

# ======================================================================
# S1 (J1) — census ties, then the germ at all four points vs file literals
# ======================================================================
print()
print("== S1 (J1): transcription — census, and the germ vs the file's literals ==")
check("r6s.J1.census_512_50_11",
      len(ALLT) == 512 and len(VALID) == 50 and len(nonzero_t) == 11,
      f"nine nests: total={len(ALLT)}, guard-live={len(VALID)}, nonzero-residual={len(nonzero_t)}")
check("r6s.J1.file11_nest_order", nonzero_t == FILE11,
      "the 11 nonzero residuals appear in exactly the pack's FILE11 nest order")

# file literals (Rigidity.lean, positional 15-tuples: v,d0..d3,e00..e33)
GY = (ZP0, ZP0, ZP0, ZP0, ZP0,
      (15,10), (8,18), (-10,-8), (12,18),
      (8,9), (-2,-16), (-4,-8),
      (7,1), (4,4),
      (29,29))
GS = ((17,0), (24,0), (20,0), (20,0), (26,0),
      (21,0), (14,0), (14,0), (16,0),
      (12,0), (24,0), (28,0),
      (12,0), (28,0),
      (26,0))
GC = ((201,0), ZP0, (220,0), (150,0), (-96,0),
      (39,0), (-10,0), ZP0, (-2,0),
      (64,0), (156,0), (-64,0),
      (29,0), (-56,0),
      (136,0))
GG = (EP0, EP0, EP0, EP0, EP0,
      (( 15,-4), ZP0), (ZP0, (26,-18)), (ZP0, (26,-18)), ((-12,8), ZP0),
      (( -9, 8), ZP0), ((-18,16), ZP0), (ZP0, (-12,8)),
      (( -9, 8), ZP0), (ZP0, (-12,8)),
      ((  1, 6), ZP0))

# Yang-Lee over Zp:  (p,q,r,s) = (-phi, 1, -phi, phi)
pY, qY, rY, sY = zneg(ZPHI), ZP1, zneg(ZPHI), ZPHI
gY = germ(zpRng, pY, qY, rY, sY)
check("r6s.J1.germY_equals_GY", gY == GY,
      "jets at (-phi,1,-phi,phi) over Zp reproduce ALL 15 slots of the file's GY literal")

# strict and control over plain ints (jet ring generic over the Rng record)
gS = germ(intRng, 1, 1, 1, 1)
check("r6s.J1.germS_equals_GS", tuple((c, 0) for c in gS) == GS,
      f"jets at (1,1,1,1) over int: v={gS[0]}, d={gS[1:5]}, e={gS[5:]} == GS")
gC = germ(intRng, 1, 2, 3, -1)
gC_zp = germ(zpRng, (1,0), (2,0), (3,0), (-1,0))
check("r6s.J1.germC_equals_GC", tuple((c, 0) for c in gC) == GC and gC_zp == GC,
      f"jets at (1,2,3,-1) over int AND over Zp: v={gC[0]}, d={gC[1:5]} == GC (both layers)")

# golden, layer 1: Lean's Ep = Z[phi][sqrt phi] integer pairs
pG_ep, qG_ep, sG_ep = ((-1,1), ZP0), (ZP0, (-1,1)), ((1,-1), ZP0)
gG_ep = germ(epRng, pG_ep, qG_ep, qG_ep, sG_ep)
check("r6s.J1.germG_epLayer_equals_GG", gG_ep == GG,
      "jets at golden over Lean's Ep reproduce ALL 15 slots of GG (incl. the 4 slots needing sqrt(phi))")

# golden, layer 2: the pack's EE (E = Q(sqrt5)(sqrt phi), Fractions) — the seat-pinned layer
pG_ee, qG_ee, sG_ee = EE(PHIM1), EE(Q5(0), PHIM1), EE(-PHIM1)
GOLD_EE = (pG_ee, qG_ee, qG_ee, sG_ee)
gG_ee = germ(eeRng, *GOLD_EE)
check("r6s.J1.germG_EElayer_equals_GG", tuple(gG_ee) == tuple(ep2ee(s) for s in GG),
      "jets at golden over the pack's EE arithmetic == GG converted (m+n*phi -> ((2m+n)+n*sqrt5)/2): "
      "two independent E implementations agree slot by slot")

# ======================================================================
# S2 (J2) — THE RACE: jets (route A) vs builder d2(RSUM) (route B), entrywise
# ======================================================================
print()
print("== S2 (J2): the race — jet Hessians vs builder symbolic Hessians, entry by entry ==")
def H_ee_from_zp(Hzp):  return [[zp2q5(Hzp[a][b]) for b in range(4)] for a in range(4)]

# golden
H_G_jets = hessOf(eeRng, gG_ee)                          # route A (EE layer)
H_G_bldr = full_hessian(GOLD_EE)                         # route B
okG = all(H_G_jets[a][b] == H_G_bldr[a][b] for a in range(4) for b in range(4))
check("r6s.J2.golden_entrywise_race", okG,
      "16/16 entries: hessOf(jets) == d2(RSUM) at golden, exact in E (independent routes)")

# the quoted certificate values (task list): golden blocks + cross entries
QUOTED_G = {(0,0): EE(Q5(26,-4)), (0,3): EE(Q5(-8,4)), (3,3): EE(Q5(8,6)),
            (1,1): EE(Q5(-10,8)), (1,2): EE(Q5(-10,8)), (2,2): EE(Q5(-10,8)),
            (0,1): EE(Q5(0), Q5(17,-9)), (0,2): EE(Q5(0), Q5(17,-9)),
            (1,3): EE(Q5(0), Q5(-8,4)), (2,3): EE(Q5(0), Q5(-8,4))}
okQ = all(H_G_jets[a][b] == v and H_G_jets[b][a] == v for (a, b), v in QUOTED_G.items())
check("r6s.J2.golden_quoted_certificate_values", okQ,
      "H00=26-4~5, H03=-8+4~5, H33=8+6~5, H11=H12=H22=-10+8~5, H01=H02=(17-9~5)s, H13=H23=(-8+4~5)s "
      "— all ten distinct entries match the certificate world exactly")
# and the same ten against the file's HG literal (phi basis: 30-8phi etc.)
HG_lit = {(0,0): ((30,-8),ZP0), (0,1): (ZP0,(26,-18)), (0,2): (ZP0,(26,-18)),
          (0,3): ((-12,8),ZP0), (1,1): ((-18,16),ZP0), (1,2): ((-18,16),ZP0),
          (1,3): (ZP0,(-12,8)), (2,2): ((-18,16),ZP0), (2,3): (ZP0,(-12,8)),
          (3,3): ((2,12),ZP0)}
H_G_ep = hessOf(epRng, gG_ep)
okHGl = all(H_G_ep[a][b] == v for (a, b), v in HG_lit.items())
check("r6s.J2.golden_HG_literal", okHGl,
      "hessOf(Ep jets) == the file's HG_entries literal, all ten distinct entries")

# Yang-Lee
H_Y_jets = hessOf(zpRng, gY)
H_Y_ee   = H_ee_from_zp(H_Y_jets)
YL_EE = (EE(-PHI5), EE(1), EE(-PHI5), EE(PHI5))
H_Y_bldr = full_hessian(YL_EE)
okY = all(EE(H_Y_ee[a][b]) == H_Y_bldr[a][b] for a in range(4) for b in range(4))
check("r6s.J2.yl_entrywise_race", okY,
      "16/16 entries: hessOf(jets over Zp) -> sqrt5 basis == d2(RSUM) at Yang-Lee, exact")
HY_lit = {(0,0): (30,20), (0,1): (8,18), (0,2): (-10,-8), (0,3): (12,18),
          (1,1): (16,18), (1,2): (-2,-16), (1,3): (-4,-8),
          (2,2): (14,2), (2,3): (4,4), (3,3): (58,58)}
okYl = all(H_Y_jets[a][b] == v and H_Y_jets[b][a] == v for (a, b), v in HY_lit.items())
QUOTED_Y = {(0,0): Q5(40,10), (0,1): Q5(17,9), (0,2): Q5(-14,-4), (0,3): Q5(21,9),
            (1,1): Q5(25,9), (1,2): Q5(-10,-8), (1,3): Q5(-8,-4),
            (2,2): Q5(15,1), (2,3): Q5(6,2), (3,3): Q5(87,29)}
okYq = all(H_Y_ee[a][b] == v for (a, b), v in QUOTED_Y.items())
check("r6s.J2.yl_HY_literal_and_quoted", okYl and okYq,
      "HY literal (30,20)...(58,58) in m+n*phi AND certificate basis H00=40+10~5, H33=87+29~5, "
      "H11=25+9~5, H22=15+~5, H01=17+9~5, H02=-14-4~5, H03=21+9~5, H12=-10-8~5, H13=-8-4~5, H23=6+2~5")

# control point (1,2,3,-1)
H_C_jets = hessOf(intRng, gC)
CTRL_EE = (EE(1), EE(2), EE(3), EE(-1))
H_C_bldr = full_hessian(CTRL_EE)
okC = all(EE(H_C_jets[a][b]) == H_C_bldr[a][b] for a in range(4) for b in range(4))
check("r6s.J2.control_entrywise_race", okC,
      "16/16 entries: hessOf(jets over int) == d2(RSUM) at (1,2,3,-1), exact")

# control receipts: Hv, wHw, det4  (file: HC_tangent_not_null, HC_not_psd, HC_rank4)
def matvec_int(M, v): return [sum(M[a][b] * v[b] for b in range(4)) for a in range(4)]
def qform_int(M, w):  return sum(w[a] * M[a][b] * w[b] for a in range(4) for b in range(4))
Hv = matvec_int(H_C_jets, [0, 2, -3, 0])                 # tangent (0,q,-r,0) = (0,2,-3,0)
wHw = qform_int(H_C_jets, [-3, -3, 3, -1])
d4C = detEE([[EE(H_C_jets[a][b]) for b in range(4)] for a in range(4)])
check("r6s.J2.control_Hv_wHw_det4",
      Hv == [-20, -212, 138, 40] and wHw == -400 and d4C == EE(-322420288),
      f"H.(0,2,-3,0) = {Hv} == (-20,-212,138,40); w=(-3,-3,3,-1): wHw = {wHw} == -400; "
      f"det4 = -322420288 (rank 4) — matches certificate AND file theorems HC_tangent_not_null/HC_not_psd/HC_rank4")

# ======================================================================
# S3 (J3) — the swap value at Yang-Lee: wHw = 34+52phi = 60+26sqrt5
# ======================================================================
print()
print("== S3 (J3): the swap direction (0,1,-1,0) at Yang-Lee ==")
def mvec_zp(M, v):
    out = []
    for a in range(4):
        acc = ZP0
        for b in range(4): acc = zadd(acc, zmul(M[a][b], v[b]))
        out.append(acc)
    return out
def qform_zp(M, w):
    Hw = mvec_zp(M, w)
    acc = ZP0
    for a in range(4): acc = zadd(acc, zmul(w[a], Hw[a]))
    return acc
swap = [ZP0, ZP1, zneg(ZP1), ZP0]
Hswap = mvec_zp(H_Y_jets, swap)
qsw = qform_zp(H_Y_jets, swap)
check("r6s.J3.swap_qform_34_52phi",
      qsw == (34, 52) and Hswap[0] != ZP0,
      f"jets: (0,1,-1,0)^T H (0,1,-1,0) = {qsw} == (34,52) i.e. 34+52*phi; H.swap = {Hswap} != 0 "
      "— exactly the round-6 ledger line for HY_swap_not_null")
# basis conversion, both forms, and the builder-route value
conv = zp2q5((34, 52))
qsw_b = EE0
Hw_b = [sum((H_Y_bldr[a][b] * [EE0, EE1, -EE1, EE0][b] for b in range(4)), EE0) for a in range(4)]
for a in range(4): qsw_b = qsw_b + [EE0, EE1, -EE1, EE0][a] * Hw_b[a]
check("r6s.J3.swap_conversion_60_26sqrt5",
      conv == Q5(60, 26) and qsw_b == EE(Q5(60, 26)) and signE(qsw_b) == 1,
      "34+52*phi = 34+52*(1+sqrt5)/2 = 60+26*sqrt5: Zp->Q5 conversion gives (60,26); "
      "builder route gives the SAME value 60+26~5, sign +1 (positive) — both forms verified")

# ======================================================================
# S4 (J4) — gradient receipts through the jets, both routes
# ======================================================================
print()
print("== S4 (J4): gradient receipts ==")
gradY = gradOf(gY); gradG_ep = gradOf(gG_ep); gradG_ee = gradOf(gG_ee)
bgY = full_grad(YL_EE); bgG = full_grad(GOLD_EE)
check("r6s.J4.grad_zero_both_worlds",
      all(g == ZP0 for g in gradY) and all(g == EP0 for g in gradG_ep)
      and all(g.is_zero() for g in gradG_ee)
      and all(g.is_zero() for g in bgY) and all(g.is_zero() for g in bgG)
      and gY[0] == ZP0 and gG_ep[0] == EP0,
      "SS=0 and grad(SS)=0 EXACTLY at Yang-Lee (Zp jets) and golden (Ep jets + EE jets), "
      "and the builder symbolic gradient agrees: both worlds are critical points")
gradC = gradOf(gC); gradS = gradOf(gS)
bgC = full_grad(CTRL_EE); bgS = full_grad(tuple(EE(1) for _ in range(4)))
check("r6s.J4.grad_nonzero_control_strict",
      gradC == (0, 220, 150, -96) and any(g != 0 for g in gradC)
      and gradS == (24, 20, 20, 26)
      and [EE(g) for g in gradC] == bgC and [EE(g) for g in gradS] == bgS
      and gS[0] == 17 and gC[0] == 201,
      f"control: grad = {gradC} != 0 (SS=201); strict: grad = {gradS} == (24,20,20,26) per the "
      "earlier certificate (SS=17) — jets and builder route agree exactly; note d0=0 at control "
      "(single component), the VECTOR is nonzero")

# ======================================================================
# S5 (J5) — the ten golden gg_e values vs certificate H entries: the mapping
# ======================================================================
print()
print("== S5 (J5): gg_e00..gg_e33 vs certificate H — the diagonal convention ==")
info("CONVENTION MAPPING (as documented in Rigidity.lean SS3 and hessOf docstring):")
info("  jets store e_ii = (1/2) d2SS/dxi2   =>  certificate H_ii = 2*e_ii   (diagonal doubled)")
info("  jets store e_ij = d2SS/dxi dxj (i<j) =>  certificate H_ij = e_ij    (off-diagonal as-is)")
GGE = {(0,0): GG[5], (0,1): GG[6], (0,2): GG[7], (0,3): GG[8], (1,1): GG[9],
       (1,2): GG[10], (1,3): GG[11], (2,2): GG[12], (2,3): GG[13], (3,3): GG[14]}
ok5 = True
for (i, j), e in GGE.items():
    lhs = ep2ee(e)
    lhs = lhs + lhs if i == j else lhs
    if lhs != H_G_bldr[i][j]: ok5 = False
check("r6s.J5.ten_gg_e_vs_certificate", ok5,
      "all ten gg_eIJ literals map onto the builder's d2(RSUM) golden entries under EXACTLY "
      "that documented mapping (e00=15-4phi -> H00=30-8phi=26-4~5, e01=(26-18phi)s -> H01=(17-9~5)s, ...)")
doc_ok = (ANCHORS["documented convention Hii=2eii"] in txt and
          ANCHORS["documented convention Hij=eij"] in txt and
          ANCHORS["hessOf doubling docstring"] in txt)
check("r6s.J5.convention_is_documented", doc_ok,
      "the mapping is stated in the file itself (SS3 header d2/dxi2 = 2*e_ii, d2/dxi dxj = e_ij; "
      "hessOf docstring 'Diagonal entries are doubled...') — no undocumented convention gap")

# ======================================================================
# S6 (J6) — negative controls
# ======================================================================
print()
print("== S6 (J6): negative controls ==")
# N1: perturb one jet seed field.
# N1a — second-order seed jp(p).e00 := 1, i.e. input p + eps0 + eps0^2.  Chain
# rule: e00 slot becomes e00 + d0*1, ALL other 14 slots unchanged.  At STRICT
# d0 = 24 != 0, so the Hessian must move by exactly 2*d0; at YANG-LEE d0 = 0
# (critical point), so the SAME perturbation must be a no-op — the first run of
# this script tried "must move" at YL and the jets correctly refused: a
# second-order reparametrization cannot move the Hessian at a critical point.
gS_pert = germ(intRng, 1, 1, 1, 1, seed_e00_on_k=0)
pred_S = tuple((gS[i] + gS[1]) if i == 5 else gS[i] for i in range(15))   # e00 += d0
gY_pert = germ(zpRng, pY, qY, rY, sY, seed_e00_on_k=0)
check("r6s.J6.negctrl_seed_e00_chain_rule",
      gS_pert == pred_S and gS_pert[5] == 45 and gS_pert != gS
      and hessOf(intRng, gS_pert)[0][0] == 90 != hessOf(intRng, gS)[0][0]
      and gY_pert == gY,
      "jp(p).e00 := 1 at STRICT moves e00 by exactly d0 (21 -> 45, H00 42 -> 90), every other slot "
      "fixed; at YANG-LEE (d0 = 0, critical) the same seed is provably a NO-OP and the jets agree "
      "— the seed field is wired into exactly the chain-rule path, with the critical-point invariance as receipt")
# N1b — first-order shear seed jp(q).d0 := 1, i.e. input q + eps0 + eps1: the
# germ must transform by the congruence H' = M^T H M, M = I + E[1][0] — this
# DOES move the Hessian at Yang-Lee.
gY_shear = germ(zpRng, pY, qY, rY, sY, seed_d0_on_k=1)
H_shear = hessOf(zpRng, gY_shear)
M = [[1 if a == b else 0 for b in range(4)] for a in range(4)]; M[1][0] = 1
H_cong = [[ZP0] * 4 for _ in range(4)]
for a in range(4):
    for b in range(4):
        acc = ZP0
        for i in range(4):
            for j in range(4):
                if M[i][a] and M[j][b]: acc = zadd(acc, H_Y_jets[i][j])
        H_cong[a][b] = acc
check("r6s.J6.negctrl_seed_shear_moves_H",
      H_shear != H_Y_jets and H_shear == H_cong and H_shear[0][0] == (62, 74)
      and gY_shear[5] == (31, 37) and gradOf(gY_shear) == gradOf(gY),
      f"jp(q).d0 := 1 at YL MOVES the Hessian (H00 (30,20) -> {H_shear[0][0]}; e00 -> e00+e01+e11 = "
      f"{gY_shear[5]}) and lands EXACTLY on the congruence M^T.H.M of the unperturbed jets H: "
      "the first-order seeds feed the quadratic slots as a change of infinitesimal frame should")
# N2: wrong Leibniz rule (drop d0*d1+d1*d0 from the e01 slot) — race must break at e01 only
gY_wl = germ(zpRng, pY, qY, rY, sY, wrong_leibniz_e01=True)
check("r6s.J6.negctrl_wrong_leibniz_breaks",
      gY_wl[6] != gY[6] and gY_wl[5] == gY[5] and gY_wl[0] == gY[0]
      and gradOf(gY_wl) == gradOf(gY),
      f"dropping the d0*d1 cross term corrupts e01 ({gY[6]} -> {gY_wl[6]}) while v, grad, e00 stay "
      "— the truncated Leibniz cross term is load-bearing and my transcription would have caught its absence")
# N3: undoubled diagonal — the convention race must break on every diagonal
H_Y_undoubled = hessOf(zpRng, gY, double_diag=False)
und_break = all(zp2q5(H_Y_undoubled[i][i]) != H_Y_bldr[i][i].x or not H_Y_bldr[i][i].y.is_zero()
                for i in range(4))
und_off_ok = all(H_Y_undoubled[a][b] == H_Y_jets[a][b] for a in range(4) for b in range(4) if a != b)
check("r6s.J6.negctrl_undoubled_diagonal_breaks", und_break and und_off_ok,
      "reading H_ii = e_ii (no factor 2) breaks the race on ALL FOUR diagonals vs the builder's "
      "true second partials, off-diagonals unaffected: the factor-2 convention is real and detectable")
# N4: wrong Zp multiplication (phi^2 = phi instead of phi+1) — germ must break
def zmul_wrong(u, v): return (u[0] * v[0], u[0] * v[1] + u[1] * v[0] + u[1] * v[1])
zpWrong = Rng(ZP0, ZP1, zadd, zneg, zmul_wrong)
gY_wrongphi = germ(zpWrong, pY, qY, rY, sY)
check("r6s.J6.negctrl_wrong_phi_relation_breaks", gY_wrongphi != gY,
      "coefficient ring with phi^2 = phi (dropping the +1) changes the germ at Yang-Lee: "
      "the phi^2 = phi+1 relation in Zp.mul is exercised by the computation")
# N5: random non-critical integer points — full race + nonzero gradient
n_pts, ok_race, ok_grad = 0, True, True
tried = []
while n_pts < 6:
    pt = tuple(random.randint(-3, 3) for _ in range(4))
    bg = full_grad(tuple(EE(c) for c in pt))
    if all(g.is_zero() for g in bg):        # skip critical points (e.g. on the variety)
        continue
    g = germ(intRng, *pt)
    Hj = hessOf(intRng, g)
    Hb = full_hessian(tuple(EE(c) for c in pt))
    if not all(EE(Hj[a][b]) == Hb[a][b] for a in range(4) for b in range(4)): ok_race = False
    if [EE(c) for c in gradOf(g)] != bg: ok_race = False
    if not any(c != 0 for c in gradOf(g)): ok_grad = False
    tried.append(pt); n_pts += 1
check("r6s.J6.random_noncritical_race", ok_race and ok_grad,
      f"6 seeded random integer points {tried}: jet gradient NONZERO at each and jets == builder "
      "(16 H entries + 4 grad slots) at every point — the transcription races clean off the worlds too")

# ======================================================================
# S7 — extra receipts tying jets to the file's remaining round-6 numbers
# ======================================================================
print()
print("== S7: extra receipts (solutionhood, dets, minors) off the same jets ==")
live_zero = all(pentResid(zpRng, Fg(pY, qY, rY, sY), *tp) == ZP0 for tp in VALID)
n_alive_S = sum(1 for tp in FILE11
                if pentResid(intRng, Fg(1, 1, 1, 1), *tp) != 0)
check("r6s.X.solutionhood_hypothesis",
      live_zero and n_alive_S == 8,
      "Yang-Lee: all 50 guard-live residuals vanish exactly (the load-bearing hypothesis of the "
      "headline theorem, 462 vacuous by guard); strict (1,1,1,1): 8/11 residuals alive (the refutation specimen)")
d4Y = detEE([[EE(H_Y_ee[a][b]) for b in range(4)] for a in range(4)])
m3Y = detEE(minor([[EE(H_Y_ee[a][b]) for b in range(4)] for a in range(4)], (0,1,3), (0,1,3)))
d4G = detEE(H_G_jets)
m3G = detEE(minor(H_G_jets, (0,1,3), (0,1,3)))
check("r6s.X.rank3_receipts",
      d4Y.is_zero() and m3Y == EE(zp2q5((21120, 31480)))
      and d4G.is_zero() and m3G == ep2ee(((1920, 360), ZP0)) and signE(m3G) == 1,
      "off the JET Hessians: det4=0 at both worlds; minor3(0,1,3) = (21120,31480) in m+n*phi at YL "
      "(file HY_minor3_pos) and (1920,360) at golden (file HG_minor3_pos), both > 0 — rank exactly 3")

print()
nfail = sum(1 for _, ok in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  ({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
