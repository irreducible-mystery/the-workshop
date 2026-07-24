#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Round-3 adversarial audit — Galois-conjugation and gauge-equivalence sections
of /home/claude/workshop/lean/Anyon.lean.

Standalone.  All algebra is reimplemented FROM THE LEAN SOURCE in exact Python
integer arithmetic:

    Z5 = Z[zeta5]     integer 4-tuples (a0,a1,a2,a3), zeta^4 = -(1+z+z^2+z^3)
    KK = Z5[t]/(t^2 - phi)   pairs (x,y) of Z5 meaning x + y*t
    Zp = Z[phi]       integer pairs (m,n) meaning m + n*phi, phi^2 = phi + 1

plus a generic-coefficient run of the same operations over a small integer
multivariate-polynomial class (for the symbolic identities) and over the
polynomial ring KK[R1,RT] (for the structural naturality check G4).

Floats appear ONLY in the clearly marked sanity-check block of G3.

Checks: G1..G10 as specified by the round-3 audit charge.  One summary
PASS/FAIL line per check at the end.
"""

import random
import re
import sys
import cmath
import math

LEAN = "/home/claude/workshop/lean/Anyon.lean"

# ════════════════════════════════════════════════════════════════════════
# 0.  Exact multivariate polynomials over Z (for symbolic identities)
# ════════════════════════════════════════════════════════════════════════

def _mon_mul(m1, m2):
    d = dict(m1)
    for v, e in m2:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))

class P:
    """Multivariate polynomial over Z.  d : monomial -> int coeff, where a
    monomial is a sorted tuple of (varname, exponent)."""
    __slots__ = ("d",)

    def __init__(self, d=None):
        dd = {}
        if d:
            for m, c in d.items():
                if c:
                    dd[m] = dd.get(m, 0) + c
        self.d = {m: c for m, c in dd.items() if c}

    @staticmethod
    def lift(x):
        if isinstance(x, P):
            return x
        if isinstance(x, int):
            return P({(): x})
        raise TypeError(x)

    @staticmethod
    def var(name):
        return P({((name, 1),): 1})

    def __add__(self, o):
        o = P.lift(o)
        d = dict(self.d)
        for m, c in o.d.items():
            d[m] = d.get(m, 0) + c
        return P(d)
    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.d.items()})

    def __sub__(self, o):
        return self + (-P.lift(o))

    def __rsub__(self, o):
        return P.lift(o) + (-self)

    def __mul__(self, o):
        o = P.lift(o)
        d = {}
        for m1, c1 in self.d.items():
            for m2, c2 in o.d.items():
                m = _mon_mul(m1, m2)
                d[m] = d.get(m, 0) + c1 * c2
        return P(d)
    __rmul__ = __mul__

    def __eq__(self, o):
        try:
            o = P.lift(o)
        except TypeError:
            return NotImplemented
        return self.d == o.d

    def __hash__(self):
        return hash(frozenset(self.d.items()))

    def __repr__(self):
        if not self.d:
            return "0"
        return " + ".join(f"{c}*{m}" for m, c in sorted(self.d.items()))

def peq(a, b):
    return P.lift(a) == P.lift(b)

def teq(u, v):
    """Equality of same-shape tuples whose leaves are int/P."""
    if isinstance(u, tuple):
        return len(u) == len(v) and all(teq(a, b) for a, b in zip(u, v))
    return peq(u, v)

# ════════════════════════════════════════════════════════════════════════
# 1.  Z5, KK, Zp — transcribed from Anyon.lean (entries may be int or P)
# ════════════════════════════════════════════════════════════════════════

# --- Z5 (Anyon.lean lines 240-277) ---
Z5_ZERO = (0, 0, 0, 0)
Z5_ONE  = (1, 0, 0, 0)
ZETA    = (0, 1, 0, 0)
ZETA2   = (0, 0, 1, 0)
ZETA3   = (0, 0, 0, 1)
ZETA4   = (-1, -1, -1, -1)
Z5_PHI    = (0, 0, -1, -1)
Z5_INVPHI = (-1, 0, -1, -1)

def z5_add(u, v):
    return tuple(a + b for a, b in zip(u, v))

def z5_neg(u):
    return tuple(-a for a in u)

def z5_mul(u, v):
    c0 = u[0]*v[0]
    c1 = u[0]*v[1] + u[1]*v[0]
    c2 = u[0]*v[2] + u[1]*v[1] + u[2]*v[0]
    c3 = u[0]*v[3] + u[1]*v[2] + u[2]*v[1] + u[3]*v[0]
    c4 = u[1]*v[3] + u[2]*v[2] + u[3]*v[1]
    c5 = u[2]*v[3] + u[3]*v[2]
    c6 = u[3]*v[3]
    return (c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4)

# --- the three coordinate maps on Z5 (lines 1700, 1761, 1778) ---
def z5_conj(u):      # conj (a0,a1,a2,a3) = (a0-a1, -a1, a3-a1, a2-a1)
    return (u[0] - u[1], -u[1], u[3] - u[1], u[2] - u[1])

def z5_swapBad(u):   # swapBad = (a0, a2, a1, a3)
    return (u[0], u[2], u[1], u[3])

def z5_sigma(u):     # sigma = (a0-a2, a3-a2, a1-a2, -a2)
    return (u[0] - u[2], u[3] - u[2], u[1] - u[2], -u[2])

# --- KK (lines 303-341) ---
K_ZERO = (Z5_ZERO, Z5_ZERO)
K_ONE  = (Z5_ONE,  Z5_ZERO)
K_T    = (Z5_ZERO, Z5_ONE)

def k_emb(u):
    return (u, Z5_ZERO)

def k_add(u, v):
    return (z5_add(u[0], v[0]), z5_add(u[1], v[1]))

def k_neg(u):
    return (z5_neg(u[0]), z5_neg(u[1]))

def k_mul(u, v):
    return (z5_add(z5_mul(u[0], v[0]), z5_mul(Z5_PHI, z5_mul(u[1], v[1]))),
            z5_add(z5_mul(u[0], v[1]), z5_mul(u[1], v[0])))

K_INVPHI = k_emb(Z5_INVPHI)
K_B      = k_mul(K_T, K_INVPHI)          # file: b = mul t invPhi
K_R1     = k_emb(ZETA2)                  # r1 = zeta^2
K_RT     = k_emb(z5_neg(ZETA))           # rt = -zeta
K_THETA  = k_emb(ZETA3)
K_PHI    = k_emb(Z5_PHI)
R1P      = k_emb(ZETA3)                  # file line 542: r1' = emb zeta3
RTP      = k_emb(z5_neg(ZETA4))          # file line 544: rt' = emb (neg zeta4)
THETAP   = k_emb(ZETA2)                  # file line 546

def k_conj(u):       # line 1822: conj (x,y) = (Z5.conj x, Z5.conj y)
    return (z5_conj(u[0]), z5_conj(u[1]))

def k_badConj(u):    # line 2055: badConj (x,y) = (swapBad x, swapBad y)
    return (z5_swapBad(u[0]), z5_swapBad(u[1]))

def k_sigmalift(u):  # illegitimate componentwise lift of sigma (negative control)
    return (z5_sigma(u[0]), z5_sigma(u[1]))

# --- Zp (lines 175-195) ---
ZP_ZERO = (0, 0)
ZP_ONE  = (1, 0)
ZP_PHI  = (0, 1)
ZP_INVPHI = (-1, 1)

def zp_add(u, v):
    return (u[0] + v[0], u[1] + v[1])

def zp_neg(u):
    return (-u[0], -u[1])

def zp_mul(u, v):    # (mm'+nn', mn'+nm'+nn')
    return (u[0]*v[0] + u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])

# --- the embedding (lines 2119, 2177) ---
def zp_toZ5(u):      # toZ5 (m,n) = (m, 0, -n, -n)
    return (u[0], 0, -u[1], -u[1])

def zp_toKK(u):
    return k_emb(zp_toZ5(u))

# ════════════════════════════════════════════════════════════════════════
# 2.  Fusion grammar + generic coherence machinery (lines 47-168)
# ════════════════════════════════════════════════════════════════════════

ONE, TAU = 0, 1
LAB = (ONE, TAU)

def fuse(a, b):
    if a == ONE:
        return (b,)
    if b == ONE:
        return (a,)
    return (ONE, TAU)

def isone(a):
    return a == ONE

def memA(a, l):
    return a in l

class Rng:
    def __init__(self, zero, one, add, mul, beq):
        self.zero, self.one, self.add, self.mul, self.beq = zero, one, add, mul, beq

kR  = Rng(K_ZERO, K_ONE, k_add, k_mul, lambda u, v: u == v)
zpR = Rng(ZP_ZERO, ZP_ONE, zp_add, zp_mul, lambda u, v: u == v)

def sumOver(R, f, l):
    """Lean foldr: sumOver [] = 0 ; u::us => add (f u) (sumOver us)."""
    if not l:
        return R.zero
    return R.add(f(l[0]), sumOver(R, f, l[1:]))

def Fs(R, F, a, b, c, d, x, y):
    if (memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and
            memA(y, fuse(b, c)) and memA(d, fuse(a, y))):
        if isone(a) or isone(b) or isone(c):
            return R.one
        if isone(d):
            return R.one if ((not isone(x)) and (not isone(y))) else R.zero
        return F(x, y)
    return R.zero

def Rb(R, r1, rt, x, y, c):
    if isone(x) or isone(y):
        return R.one
    return r1 if isone(c) else rt

def hexagonValid(a, b, c, d, e, z):
    return (memA(e, fuse(a, b)) and memA(d, fuse(e, c)) and
            memA(z, fuse(a, c)) and memA(d, fuse(z, b)))

def hexagon_sides(R, F, r1, rt, a, b, c, d, e, z):
    lhs = R.mul(Rb(R, r1, rt, e, c, d), Fs(R, F, c, a, b, d, z, e))
    rhs = sumOver(R,
                  lambda g: R.mul(R.mul(R.mul(Fs(R, F, a, b, c, d, e, g),
                                              Rb(R, r1, rt, b, c, g)),
                                        Fs(R, F, a, c, b, d, z, g)),
                                  Rb(R, r1, rt, a, c, z)),
                  list(fuse(b, c)))
    return lhs, rhs

def hexagonCheck(R, F, r1, rt, a, b, c, d, e, z):
    if hexagonValid(a, b, c, d, e, z):
        l, r = hexagon_sides(R, F, r1, rt, a, b, c, d, e, z)
        return R.beq(l, r)
    return True

def Fsymm(x, y):     # lines 353-357
    return {(ONE, ONE): K_INVPHI, (ONE, TAU): K_B,
            (TAU, ONE): K_B, (TAU, TAU): k_neg(K_INVPHI)}[(x, y)]

def Frat(x, y):      # lines 216-220 (identical in round-2 archive)
    return {(ONE, ONE): ZP_INVPHI, (ONE, TAU): ZP_INVPHI,
            (TAU, ONE): ZP_ONE, (TAU, TAU): zp_neg(ZP_INVPHI)}[(x, y)]

def FratK(x, y):     # line 2238
    return zp_toKK(Frat(x, y))

def countHexViolations(r1, rt, F=Fsymm):
    tot = 0
    for a in LAB:
        for b in LAB:
            for c in LAB:
                for d in LAB:
                    for e in LAB:
                        for z in LAB:
                            if not hexagonCheck(kR, F, r1, rt, a, b, c, d, e, z):
                                tot += 1
    return tot

def hexFailures(r1, rt, F=Fsymm):
    out = []
    for a in LAB:
        for b in LAB:
            for c in LAB:
                for d in LAB:
                    for e in LAB:
                        for z in LAB:
                            if not hexagonCheck(kR, F, r1, rt, a, b, c, d, e, z):
                                out.append((a, b, c, d, e, z))
    return out

def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and memA(t, fuse(y, dd)) and
            memA(w, fuse(c, dd)) and memA(v, fuse(b, w)) and memA(t, fuse(a, v)))

def pentagonCheck(R, F, a, b, c, dd, x, y, t, w, v):
    if pentagonValid(a, b, c, dd, x, y, t, w, v):
        lhs = sumOver(R,
                      lambda u: R.mul(R.mul(Fs(R, F, a, b, c, y, x, u),
                                            Fs(R, F, a, u, dd, t, y, v)),
                                      Fs(R, F, b, c, dd, v, u, w)),
                      list(fuse(b, c)))
        rhs = R.mul(Fs(R, F, x, c, dd, t, y, w), Fs(R, F, a, b, w, t, x, v))
        return R.beq(lhs, rhs)
    return True

def pentStats(R, F):
    live = viol = 0
    for tup in _all_tuples(9):
        if pentagonValid(*tup):
            live += 1
        if not pentagonCheck(R, F, *tup):
            viol += 1
    return live, viol

def _all_tuples(n):
    if n == 0:
        yield ()
        return
    for rest in _all_tuples(n - 1):
        for l in LAB:
            yield (l,) + rest

def lname(x):
    return "1" if x == ONE else "t"

def fmt(tup):
    return "(" + ",".join(lname(x) for x in tup) + ")"

# ════════════════════════════════════════════════════════════════════════
# 3.  KK[R1,RT] — polynomial ring for the structural naturality check
# ════════════════════════════════════════════════════════════════════════

def kp_canon(d):
    return {m: c for m, c in d.items() if c != K_ZERO}

KP_ZERO = {}
KP_ONE  = {(0, 0): K_ONE}
KP_R1   = {(1, 0): K_ONE}
KP_RT   = {(0, 1): K_ONE}

def kp_const(k):
    return kp_canon({(0, 0): k})

def kp_add(p, q):
    out = dict(p)
    for m, c in q.items():
        out[m] = k_add(out.get(m, K_ZERO), c)
    return kp_canon(out)

def kp_neg(p):
    return {m: k_neg(c) for m, c in p.items()}

def kp_sub(p, q):
    return kp_add(p, kp_neg(q))

def kp_mul(p, q):
    out = {}
    for (i1, j1), c1 in p.items():
        for (i2, j2), c2 in q.items():
            m = (i1 + i2, j1 + j2)
            out[m] = k_add(out.get(m, K_ZERO), k_mul(c1, c2))
    return kp_canon(out)

kpR = Rng(KP_ZERO, KP_ONE, kp_add, kp_mul, lambda p, q: p == q)

# ════════════════════════════════════════════════════════════════════════
# 4.  Small helpers
# ════════════════════════════════════════════════════════════════════════

RESULTS = []   # (check_id, ok, summary_detail)
NONZERO_RESID = None
DISCREPANCIES = []

def report(cid, ok, detail):
    print(f"{'PASS' if ok else 'FAIL'} {cid} {detail}")
    RESULTS.append((cid, ok, detail))
    return ok

def info(msg):
    print("     " + msg)

def det4(M):
    """Integer determinant, cofactor expansion."""
    def det(m):
        n = len(m)
        if n == 1:
            return m[0][0]
        s = 0
        for j in range(n):
            minor = [row[:j] + row[j+1:] for row in m[1:]]
            s += ((-1) ** j) * m[0][j] * det(minor)
        return s
    return det(M)

def linmap_matrix(f):
    """Matrix (rows = output coords) of a Z-linear map on Z^4, from basis images."""
    cols = [f(tuple(1 if i == k else 0 for i in range(4))) for k in range(4)]
    return [[cols[j][i] for j in range(4)] for i in range(4)]

def rand_z5(rng):
    return tuple(rng.randint(-4, 4) for _ in range(4))

def rand_k(rng):
    return (rand_z5(rng), rand_z5(rng))

# floats — sanity only
ZC = cmath.exp(2j * math.pi / 5)
PHI_F = (1 + math.sqrt(5)) / 2

def c_of_z5(u):
    return sum(u[i] * ZC ** i for i in range(4))

def c_of_k(u):
    return c_of_z5(u[0]) + c_of_z5(u[1]) * math.sqrt(PHI_F)

# ════════════════════════════════════════════════════════════════════════
# G1 — Z5.conj is z -> z^4 in the reduced basis, symbolically
# ════════════════════════════════════════════════════════════════════════

def galois_power_map(k):
    """The reduced-basis formula for z -> z^k on a generic a0+a1 z+a2 z^2+a3 z^3,
    computed independently: send a_i z^i to a_i z^{ki mod 5}, then eliminate z^4
    via z^4 = -(1+z+z^2+z^3).  Returns a 4-tuple of P in vars a0..a3."""
    A = [P.var(f"a{i}") for i in range(4)]
    img = [P() for _ in range(5)]
    for i in range(4):
        img[(k * i) % 5] = img[(k * i) % 5] + A[i]
    return tuple(img[j] - img[4] for j in range(4))

def check_G1():
    A = tuple(P.var(f"a{i}") for i in range(4))
    ok = True
    # symbolic: the file's formula == the independently derived z->z^4 map
    derived = galois_power_map(4)
    ok &= teq(derived, z5_conj(A))
    info(f"z->z^4 reduced-basis formula derived independently == Lean conj formula: {teq(derived, z5_conj(A))}")
    # basis receipts (the file's conj_zeta.. theorems)
    basis = (z5_conj(Z5_ONE) == Z5_ONE and z5_conj(ZETA) == ZETA4 and
             z5_conj(ZETA2) == ZETA3 and z5_conj(ZETA3) == ZETA2 and
             z5_conj(ZETA4) == ZETA and z5_conj(Z5_ZERO) == Z5_ZERO)
    ok &= basis
    info(f"basis: conj(1)=1, conj z=z^4, conj z^2=z^3, conj z^3=z^2, conj z^4=z: {basis}")
    # identity control and the sigma cross-check (z->z^2 matches the file's sigma)
    id_ok = teq(galois_power_map(1), A)
    sig_ok = teq(galois_power_map(2), z5_sigma(A))
    sig3_ne = not teq(galois_power_map(3), z5_conj(A))
    ok &= id_ok and sig_ok and sig3_ne
    info(f"controls: z->z^1 = id: {id_ok}; z->z^2 == file's sigma formula: {sig_ok}; z->z^3 != conj: {sig3_ne}")
    # sigma^2 = conj, sigma^4 = id, symbolically (file: sigma_sigma, sigma_order_four)
    ss = teq(z5_sigma(z5_sigma(A)), z5_conj(A))
    s4 = teq(z5_sigma(z5_sigma(z5_sigma(z5_sigma(A)))), A)
    ok &= ss and s4
    info(f"sigma∘sigma == conj (symbolic): {ss}; sigma^4 == id (symbolic): {s4}")
    return report("G1", ok, "Z5.conj (a0-a1,-a1,a3-a1,a2-a1) IS z->z^4 in the reduced basis (symbolic; basis receipts; sigma=z->z^2 cross-check)")

# ════════════════════════════════════════════════════════════════════════
# G2 — hom laws, symbolic; the KK lift
# ════════════════════════════════════════════════════════════════════════

def check_G2():
    U = tuple(P.var(f"u{i}") for i in range(4))
    V = tuple(P.var(f"v{i}") for i in range(4))
    ok = True
    a_ok = teq(z5_conj(z5_add(U, V)), z5_add(z5_conj(U), z5_conj(V)))
    n_ok = teq(z5_conj(z5_neg(U)), z5_neg(z5_conj(U)))
    m_ok = teq(z5_conj(z5_mul(U, V)), z5_mul(z5_conj(U), z5_conj(V)))
    i_ok = teq(z5_conj(z5_conj(U)), U)
    ok &= a_ok and n_ok and m_ok and i_ok
    info(f"Z5 level (8 indeterminates for mul): conj_add {a_ok}, conj_neg {n_ok}, conj_mul {m_ok}, conj_conj=id {i_ok}")
    # sigma is also a ring map (file: sigma_mul) — so the negative control below
    # is about phi-fixing, not about a broken map
    sm_ok = teq(z5_sigma(z5_mul(U, V)), z5_mul(z5_sigma(U), z5_sigma(V)))
    ok &= sm_ok
    info(f"sigma_mul symbolic (sigma is a genuine ring map too): {sm_ok}")
    # the lift to KK: read from the file — componentwise
    src = open(LEAN, encoding="utf-8").read()
    lift_line = "def conj (u : KK) : KK := ⟨Z5.conj u.x, Z5.conj u.y⟩" in src
    ok &= lift_line
    info(f"file lifts conj to KK componentwise (def conj (u:KK) := ⟨Z5.conj u.x, Z5.conj u.y⟩): {lift_line}")
    # legitimacy: conj fixes phi (exact) — this is what the cross term needs
    phi_fix = z5_conj(Z5_PHI) == Z5_PHI
    ok &= phi_fix
    info(f"legitimacy of the componentwise lift: Z5.conj(phi) == phi exactly: {phi_fix}")
    # K-level hom laws with 16 indeterminates
    KU = (tuple(P.var(f"p{i}") for i in range(4)), tuple(P.var(f"q{i}") for i in range(4)))
    KV = (tuple(P.var(f"r{i}") for i in range(4)), tuple(P.var(f"s{i}") for i in range(4)))
    ka = teq(k_conj(k_add(KU, KV)), k_add(k_conj(KU), k_conj(KV)))
    kn = teq(k_conj(k_neg(KU)), k_neg(k_conj(KU)))
    km = teq(k_conj(k_mul(KU, KV)), k_mul(k_conj(KU), k_conj(KV)))
    ki = teq(k_conj(k_conj(KU)), KU)
    ok &= ka and kn and km and ki
    info(f"K level (16 indeterminates): conj_add {ka}, conj_neg {kn}, conj_mul {km}, conj_conj=id {ki}")
    # negative control: the componentwise lift of sigma FAILS K-multiplicativity
    # (sigma is a ring map on Z5 but moves phi — so componentwise is legitimate
    #  precisely BECAUSE conj fixes phi)
    sig_fail = not teq(k_sigmalift(k_mul(KU, KV)), k_mul(k_sigmalift(KU), k_sigmalift(KV)))
    ok &= sig_fail
    info(f"negative control: componentwise sigma-lift fails K-multiplicativity (sigma moves phi): {sig_fail}")
    return report("G2", ok, "conj_add/neg/mul/conj exact symbolic identities over Z (mul: 8 indets); KK lift componentwise, legitimate since conj(phi)=phi; K-level hom laws symbolic (16 indets)")

# ════════════════════════════════════════════════════════════════════════
# G3 — fixed and moved elements; mirror constants; bench tie
# ════════════════════════════════════════════════════════════════════════

def check_G3():
    ok = True
    fixes = (z5_conj(Z5_PHI) == Z5_PHI and z5_conj(Z5_INVPHI) == Z5_INVPHI and
             k_conj(K_T) == K_T and k_conj(K_B) == K_B and
             k_conj(K_ONE) == K_ONE and k_conj(K_ZERO) == K_ZERO and
             k_conj(K_INVPHI) == K_INVPHI)
    ok &= fixes
    info(f"fixed: conj phi=phi, conj invPhi=invPhi (Z5 and K), conj t=t, conj b=b, conj 0=0, conj 1=1: {fixes}")
    # sanity on the charge's stated coordinates
    coords = (Z5_INVPHI == z5_add(ZETA, ZETA4) and K_B == (Z5_ZERO, Z5_INVPHI)
              and k_mul(K_T, K_B) == K_ONE)
    ok &= coords
    info(f"charge algebra: invPhi == z+z^4 reduced (-1,0,-1,-1); b == (0,invPhi); t*b == 1: {coords}")
    moved = (k_conj(K_R1) == R1P and k_conj(K_RT) == RTP and k_conj(K_THETA) == THETAP)
    ok &= moved
    info(f"moved: conj r1 == emb(zeta3) == file r1'; conj rt == emb(-zeta4) == file rt'; conj theta == theta': {moved}")
    concrete = (k_conj(K_R1) == k_emb(ZETA3) and
                k_conj(K_RT) == k_emb((1, 1, 1, 1)))   # -zeta4 reduced = (1,1,1,1)
    ok &= concrete
    info(f"conj r1 = z^3; conj rt = -z^4 reduced = (1,1,1,1): {concrete}")
    nonid = k_conj(K_R1) != K_R1 and K_R1 != R1P
    ok &= nonid
    info(f"anti-vacuity: conj != id at r1; r1 != r1' (chiralities distinct): {nonid}")
    # mirror obeys the same receipts (file mirror_receipts) + the originals
    rec = (k_mul(K_RT, K_RT) == K_R1 and
           k_add(k_mul(K_R1, K_INVPHI), K_RT) == K_THETA and
           k_mul(K_R1, K_THETA) == K_ONE and
           k_mul(RTP, RTP) == R1P and
           k_add(k_mul(R1P, K_INVPHI), RTP) == THETAP and
           k_mul(R1P, THETAP) == K_ONE)
    ok &= rec
    info(f"receipts both chiralities: r1=rt^2, ribbon, Frobenius-Schur (exact): {rec}")
    # negative control: sigma does NOT fix the real subfield
    neg = (z5_sigma(Z5_PHI) == z5_neg(Z5_INVPHI)) and (z5_sigma(Z5_PHI) != Z5_PHI)
    ok &= neg
    info(f"negative control: sigma(phi) == -invPhi != phi (file sigma_phi / sigma_phi_ne): {neg}")
    # ---- FLOAT SANITY ONLY (bench grammar_hexagon.py: target = e^{4i pi/5}, e^{-3i pi/5}) ----
    tgt_r1 = cmath.exp(4j * math.pi / 5)
    tgt_rt = cmath.exp(-3j * math.pi / 5)
    f_ok = (abs(c_of_k(K_R1) - tgt_r1) < 1e-9 and abs(c_of_k(K_RT) - tgt_rt) < 1e-9 and
            abs(c_of_k(R1P) - tgt_r1.conjugate()) < 1e-9 and
            abs(c_of_k(RTP) - tgt_rt.conjugate()) < 1e-9 and
            abs(c_of_k(K_THETA) - cmath.exp(-4j * math.pi / 5)) < 1e-9 and
            abs(abs(c_of_k(K_RT)) - 1) < 1e-12)
    rng = random.Random(477)
    cc_ok = all(abs(c_of_k(k_conj(u)) - c_of_k(u).conjugate()) < 1e-9
                for u in (rand_k(rng) for _ in range(20)))
    ok &= f_ok and cc_ok
    info(f"[float sanity] r1,rt == bench target e^(4i pi/5), e^(-3i pi/5); r1',rt' == their complex conjugates (bench's mirror cluster); theta == e^(-4i pi/5): {f_ok}")
    info(f"[float sanity] k_conj == complex conjugation on 20 random K elements: {cc_ok}")
    return report("G3", ok, "conj fixes phi,invPhi,t,b; conj r1=z^3=r1', conj rt=-z^4=(1,1,1,1)=rt', conj theta=theta' — file mirror constants and bench mirror cluster confirmed")

# ════════════════════════════════════════════════════════════════════════
# G4 — structural naturality of hexagonCheck under conj
# ════════════════════════════════════════════════════════════════════════

SPOT_PAIRS = None

def make_spot_pairs():
    global SPOT_PAIRS
    rng = random.Random(477)
    named = [("golden", (K_R1, K_RT)), ("mirror", (R1P, RTP)),
             ("zero", (K_ZERO, K_ZERO))]
    rnd = [(f"rand{i+1}", (rand_k(rng), rand_k(rng))) for i in range(5)]
    SPOT_PAIRS = named + rnd
    return SPOT_PAIRS

def check_G4():
    ok = True
    FP = lambda x, y: kp_const(Fsymm(x, y))
    live = []
    for tup in _all_tuples(6):
        if hexagonValid(*tup):
            live.append(tup)
    n_live = len(live)
    tie = (n_live == 15 and 64 - n_live == 49)
    ok &= tie
    info(f"live hexagon tuples: {n_live}/64 (49 vacuous) — ties to file hexagon_live_instances = 15: {tie}")
    all_coeffs_fixed = True
    n_coeffs = 0
    max_deg = 0
    nonzero_resid = 0
    for tup in live:
        lhs, rhs = hexagon_sides(kpR, FP, KP_R1, KP_RT, *tup)
        resid = kp_sub(lhs, rhs)
        if resid:
            nonzero_resid += 1
        for poly in (lhs, rhs, resid):
            for m, c in poly.items():
                n_coeffs += 1
                max_deg = max(max_deg, m[0] + m[1])
                if k_conj(c) != c:
                    all_coeffs_fixed = False
                    info(f"UNFIXED coefficient at {fmt(tup)} monomial R1^{m[0]}*RT^{m[1]}: {c}")
    ok &= all_coeffs_fixed
    info(f"all 15 live residual polynomials in KK[R1,RT]: every coefficient of LHS, RHS and LHS-RHS conj-fixed: {all_coeffs_fixed} ({n_coeffs} coefficients inspected, max total degree {max_deg}, {nonzero_resid} residuals not identically zero)")
    # which live instances carry a genuine (non-identically-zero) constraint
    nz = [tup for tup in live if kp_sub(*hexagon_sides(kpR, FP, KP_R1, KP_RT, *tup))]
    global NONZERO_RESID
    NONZERO_RESID = nz
    info("the 5 genuine-constraint instances: " + ", ".join(fmt(t) for t in nz) +
         "  (the other 10 live instances are ring identities for ALL R1,RT)")
    for tup in nz:
        resid = kp_sub(*hexagon_sides(kpR, FP, KP_R1, KP_RT, *tup))
        supp = ", ".join(f"R1^{m[0]}*RT^{m[1]}" for m in sorted(resid))
        info(f"  residual support at {fmt(tup)}: {supp}")
    # conj_Fs directly on all 64 tuples; conj_Rb on all 8 triples (random values)
    fs_ok = all(k_conj(Fs(kR, Fsymm, *tup)) == Fs(kR, Fsymm, *tup)
                for tup in _all_tuples(6))
    fs_support = sum(1 for tup in _all_tuples(6)
                     if Fs(kR, Fsymm, *tup) != K_ZERO)
    rngv = random.Random(99)
    rb_ok = True
    for _ in range(4):
        rr1, rrt = rand_k(rngv), rand_k(rngv)
        for trip in _all_tuples(3):
            if k_conj(Rb(kR, rr1, rrt, *trip)) != Rb(kR, k_conj(rr1), k_conj(rrt), *trip):
                rb_ok = False
    ok &= fs_ok and rb_ok
    info(f"conj_Fs: conj fixes Fs(Fsymm) at ALL 64 (a,b,c,d,x,y) tuples ({fs_support} with Fs != 0): {fs_ok}")
    info(f"conj_Rb: conj(Rb(r1,rt,x,y,c)) == Rb(conj r1, conj rt, x,y,c) at all 8 triples x 4 random braidings: {rb_ok}")
    info("WHY THIS SUFFICES: each live instance compares two polynomials in (R1,RT) all of whose")
    info("coefficients lie in the conj-fixed subring, so LHS(conj r1,conj rt) = conj(LHS(r1,rt)) and")
    info("likewise for RHS; conj is an injective ring hom with conj 0 = 0, so the two sides are equal")
    info("after conjugation iff they were equal before — hence hexagonCheck(conj r1,conj rt) =")
    info("hexagonCheck(r1,rt) for ALL values, and non-live tuples are vacuously true on both sides.")
    # spot verification
    pairs = make_spot_pairs()
    spot_ok = True
    for name, (r1, rt) in pairs:
        for tup in _all_tuples(6):
            lhsv = hexagonCheck(kR, Fsymm, k_conj(r1), k_conj(rt), *tup)
            rhsv = hexagonCheck(kR, Fsymm, r1, rt, *tup)
            if lhsv != rhsv:
                spot_ok = False
                info(f"MISMATCH at pair {name} tuple {fmt(tup)}")
    ok &= spot_ok
    info(f"spot check (all 64 tuples x 8 pairs: golden, mirror, zero, 5 seed-477 pseudo-random): {spot_ok}")
    # beq_conj spot (conj invisible to the equality test)
    rng = random.Random(1313)
    beq_ok = True
    for _ in range(50):
        u, v = rand_k(rng), rand_k(rng)
        if (k_conj(u) == k_conj(v)) != (u == v):
            beq_ok = False
        w = u
        if (k_conj(u) == k_conj(w)) != (u == w):
            beq_ok = False
    ok &= beq_ok
    info(f"KK.beq_conj behavior: beq(conj u, conj v) == beq(u,v) on 50 random pairs + equal pairs: {beq_ok}")
    return report("G4", ok, "hexagonCheck_conj verified STRUCTURALLY: all 15 live residuals over KK[R1,RT] have every coefficient conj-fixed; spot-verified at golden/mirror/zero + 5 fixed-seed random pairs (64 tuples each)")

# ════════════════════════════════════════════════════════════════════════
# G5 — violation counts invariant under conj
# ════════════════════════════════════════════════════════════════════════

def check_G5():
    ok = True
    pairs = SPOT_PAIRS or make_spot_pairs()
    counts = {}
    for name, (r1, rt) in pairs:
        c0 = countHexViolations(r1, rt)
        c1 = countHexViolations(k_conj(r1), k_conj(rt))
        counts[name] = (c0, c1)
        if c0 != c1:
            ok = False
    info("countHexViolations (orig, conj): " +
         ", ".join(f"{n}={c}" for n, c in counts.items()))
    anchors = (counts["golden"] == (0, 0) and counts["mirror"] == (0, 0) and
               counts["zero"] == (2, 2))
    ok &= anchors
    info(f"anchors: golden 0, mirror 0, zero-braiding 2 (file zero_braiding_fails_only_two): {anchors}")
    trivial = countHexViolations(K_ONE, K_ONE)
    swapped = countHexViolations(K_RT, K_R1)
    ok &= trivial == 4 and swapped == 5
    info(f"harness ties to file theorems: trivial (1,1) -> {trivial} (=4), swapped (rt,r1) -> {swapped} (=5)")
    info("negative control: the swap r1<->rt changes the count (0 -> 5), conj never does")
    return report("G5", ok, "countHexViolations invariant under conj at golden/mirror/zero + 5 random pairs; swap negative control changes count 0->5")

# ════════════════════════════════════════════════════════════════════════
# G6 — badConj: additive, involutive, bijective, NOT multiplicative;
#      breaks exactly 5 of the 15 live instances
# ════════════════════════════════════════════════════════════════════════

def check_G6():
    ok = True
    src = open(LEAN, encoding="utf-8").read()
    defs = ("def badConj (u : KK) : KK := ⟨Z5.swapBad u.x, Z5.swapBad u.y⟩" in src and
            "def swapBad (u : Z5) : Z5 := ⟨u.a0, u.a2, u.a1, u.a3⟩" in src)
    ok &= defs
    info(f"definitions read from file: badConj = componentwise swapBad; swapBad = (a0,a2,a1,a3): {defs}")
    U = tuple(P.var(f"u{i}") for i in range(4))
    V = tuple(P.var(f"v{i}") for i in range(4))
    KU = (tuple(P.var(f"p{i}") for i in range(4)), tuple(P.var(f"q{i}") for i in range(4)))
    KV = (tuple(P.var(f"r{i}") for i in range(4)), tuple(P.var(f"s{i}") for i in range(4)))
    addF = (teq(z5_swapBad(z5_add(U, V)), z5_add(z5_swapBad(U), z5_swapBad(V))) and
            teq(k_badConj(k_add(KU, KV)), k_add(k_badConj(KU), k_badConj(KV))))
    invF = (teq(z5_swapBad(z5_swapBad(U)), U) and teq(k_badConj(k_badConj(KU)), KU))
    ok &= addF and invF
    info(f"additive (symbolic, Z5 and K): {addF}; involution (symbolic) hence bijective: {invF}")
    Mc, Mb = linmap_matrix(z5_conj), linmap_matrix(z5_swapBad)
    dets = (det4(Mc), det4(Mb))
    ok &= abs(dets[0]) == 1 and abs(dets[1]) == 1
    info(f"unimodularity cross-check: det(conj matrix) = {dets[0]}, det(swapBad matrix) = {dets[1]} (both +-1, bijective on Z^4)")
    # NOT multiplicative: the file's own witness zeta*zeta
    w_lhs = z5_swapBad(z5_mul(ZETA, ZETA))
    w_rhs = z5_mul(z5_swapBad(ZETA), z5_swapBad(ZETA))
    wit = (w_lhs == ZETA and w_rhs == ZETA4 and w_lhs != w_rhs)
    kwit = k_badConj(k_mul(k_emb(ZETA), k_emb(ZETA))) != k_mul(k_badConj(k_emb(ZETA)), k_badConj(k_emb(ZETA)))
    ok &= wit and kwit
    info(f"NOT multiplicative — witness zeta*zeta: swapBad(zeta^2)=zeta but swapBad(zeta)^2=zeta^4: {wit}; same failure at K level: {kwit}")
    br1, brt = k_badConj(K_R1), k_badConj(K_RT)
    ident = (br1 == k_emb(ZETA) and brt == k_emb(z5_neg(ZETA2)))
    info(f"transported braiding: badConj r1 = emb(zeta), badConj rt = emb(-zeta^2): {ident}")
    ok &= ident
    fails = hexFailures(br1, brt)
    n_fail = len(fails)
    n_live = sum(1 for tup in _all_tuples(6) if hexagonValid(*tup))
    n_pass = n_live - n_fail
    tie = (n_fail == 5 and n_pass == 10 and n_live == 15)
    ok &= tie
    info(f"badConj transport of golden braiding: {n_fail} of {n_live} live instances FAIL, {n_pass} pass; 5 + 10 = 15: {tie}")
    info("the 5 broken instances (a,b,c,d,e,z): " + ", ".join(fmt(t) for t in fails))
    if NONZERO_RESID is not None:
        same_as_nz = set(fails) == set(NONZERO_RESID)
        ok &= same_as_nz
        info(f"tie to G4: the broken 5 are EXACTLY the 5 genuine-constraint instances (non-zero residual polynomials): {same_as_nz}")
    sw_fails = hexFailures(K_RT, K_R1)
    info("(compare swapped-braiding failures:      " + ", ".join(fmt(t) for t in sw_fails) +
         (" — same 5)" if set(sw_fails) == set(fails) else " — different set)"))
    # contrast with the genuine conj transport (0 failures)
    good = countHexViolations(k_conj(K_R1), k_conj(K_RT)) == 0
    ok &= good
    info(f"contrast (file multiplicativity_is_load_bearing): conj transport 0 violations, badConj 5: {good}")
    return report("G6", ok, f"badConj additive+involutive+bijective, NOT multiplicative (zeta*zeta witness); breaks exactly 5/15 live hexagon instances at golden braiding (5+10=15): {', '.join(fmt(t) for t in fails)}")

# ════════════════════════════════════════════════════════════════════════
# G7 — norms
# ════════════════════════════════════════════════════════════════════════

def check_G7():
    ok = True
    rt_n = k_mul(K_RT, k_conj(K_RT)) == K_ONE
    r1_n = k_mul(K_R1, k_conj(K_R1)) == K_ONE
    ok &= rt_n and r1_n
    info(f"rt * conj rt == 1 exactly: {rt_n};  r1 * conj r1 == 1 exactly: {r1_n}")
    same = (k_mul(K_RT, RTP) == K_ONE and k_mul(K_R1, R1P) == K_ONE)
    ok &= same
    info(f"identical to file roots_product_one / r1_roots_product_one (conj rt = rt', conj r1 = r1'): {same}")
    # negative controls: norm is not identically 1
    phi_norm = k_mul(K_PHI, k_conj(K_PHI))
    t_norm = k_mul(K_T, k_conj(K_T))
    neg = (phi_norm == k_mul(K_PHI, K_PHI) and phi_norm != K_ONE and
           t_norm == K_PHI and t_norm != K_ONE)
    ok &= neg
    info(f"negative controls: phi*conj(phi) = phi^2 != 1; t*conj(t) = t^2 = phi != 1: {neg}")
    return report("G7", ok, "rt*conj(rt) = 1 and r1*conj(r1) = 1 exact (== roots_product_one via conj rt = rt'); negative controls phi, t have norm != 1")

# ════════════════════════════════════════════════════════════════════════
# G8 — the embedding Z[phi] -> K, FratK, gauge relation, pentagon_FratK
# ════════════════════════════════════════════════════════════════════════

def check_G8():
    ok = True
    # Zp receipts
    rec = (zp_mul(ZP_PHI, ZP_PHI) == zp_add(ZP_PHI, ZP_ONE) and
           zp_mul(ZP_PHI, ZP_INVPHI) == ZP_ONE)
    ok &= rec
    info(f"Zp receipts: phi^2 = phi+1, phi*invPhi = 1: {rec}")
    # toZ5 / toKK symbolic ring-map laws (4 indeterminates m1,n1,m2,n2)
    Uz = (P.var("m1"), P.var("n1"))
    Vz = (P.var("m2"), P.var("n2"))
    tz_add = teq(zp_toZ5(zp_add(Uz, Vz)), z5_add(zp_toZ5(Uz), zp_toZ5(Vz)))
    tz_mul = teq(zp_toZ5(zp_mul(Uz, Vz)), z5_mul(zp_toZ5(Uz), zp_toZ5(Vz)))
    tz_neg = teq(zp_toZ5(zp_neg(Uz)), z5_neg(zp_toZ5(Uz)))
    ok &= tz_add and tz_mul and tz_neg
    info(f"toZ5 symbolic: add {tz_add}, mul {tz_mul} (uses phi^2=phi+1 vs zeta relations), neg {tz_neg}")
    # closed form is really m*1 + n*phi (file toZ5_eq)
    closed = teq(zp_toZ5(Uz),
                 z5_add(z5_mul((P.var("m1"), 0, 0, 0), Z5_ONE),
                        z5_mul((P.var("n1"), 0, 0, 0), Z5_PHI)))
    ok &= closed
    info(f"toZ5 closed form == m*1 + n*Z5.phi (symbolic, file toZ5_eq): {closed}")
    # emb is a ring map (8 indeterminates), then toKK laws
    U = tuple(P.var(f"u{i}") for i in range(4))
    V = tuple(P.var(f"v{i}") for i in range(4))
    emb_ok = (teq(k_mul(k_emb(U), k_emb(V)), k_emb(z5_mul(U, V))) and
              teq(k_add(k_emb(U), k_emb(V)), k_emb(z5_add(U, V))))
    ok &= emb_ok
    info(f"KK.emb_mul / emb_add symbolic (8 indets): {emb_ok}")
    tk_add = teq(zp_toKK(zp_add(Uz, Vz)), k_add(zp_toKK(Uz), zp_toKK(Vz)))
    tk_mul = teq(zp_toKK(zp_mul(Uz, Vz)), k_mul(zp_toKK(Uz), zp_toKK(Vz)))
    ok &= tk_add and tk_mul
    info(f"toKK_add symbolic: {tk_add}; toKK_mul symbolic: {tk_mul}")
    # injectivity in the representation: exact symbolic recovery
    img = zp_toKK(Uz)
    recov = (peq(img[0][0], P.var("m1")) and peq(-1 * P.lift(img[0][2]), P.var("n1")) and
             peq(img[0][1], 0) and teq(img[1], (P.lift(0),) * 4) and
             peq(img[0][2], img[0][3]))
    ok &= recov
    info(f"toKK injective in the representation: m = x.a0 and n = -x.a2 recover (m,n) symbolically; image has a1=0, a2=a3, y=0: {recov}")
    nontriv = (zp_toKK(ZP_ONE) != K_ZERO and zp_toKK(ZP_PHI) != zp_toKK(ZP_ONE) and
               zp_toKK(ZP_INVPHI) != zp_toKK(ZP_ONE))
    ok &= nontriv
    info(f"anti-vacuity (file toKK_nontrivial): toKK 1 != 0, toKK phi != toKK 1, toKK invPhi != toKK 1: {nontriv}")
    # negative control: the wrong closed form (m,0,n,n) is NOT a ring map
    bad = lambda u: (u[0], 0, u[1], u[1])
    bad_fail = not teq(bad(zp_mul(Uz, Vz)), z5_mul(bad(Uz), bad(Vz)))
    ok &= bad_fail
    info(f"negative control: sign-broken closed form (m,0,+n,+n) fails multiplicativity symbolically: {bad_fail}")
    # named constants transport
    consts = (zp_toKK(ZP_ZERO) == K_ZERO and zp_toKK(ZP_ONE) == K_ONE and
              zp_toKK(ZP_PHI) == K_PHI and zp_toKK(ZP_INVPHI) == K_INVPHI and
              zp_toKK(ZP_PHI) == k_mul(K_T, K_T) and
              k_mul(zp_toKK(ZP_PHI), zp_toKK(ZP_INVPHI)) == K_ONE)
    ok &= consts
    info(f"0,1,phi,invPhi transport; toKK phi = t^2; phi*invPhi = 1 in K: {consts}")
    # FratK = toKK of Frat, and the file's entry table
    table = {(x, y): FratK(x, y) for x in LAB for y in LAB}
    claimed = {(ONE, ONE): K_INVPHI, (ONE, TAU): K_INVPHI,
               (TAU, ONE): K_ONE, (TAU, TAU): k_neg(K_INVPHI)}
    entries = table == claimed
    ok &= entries
    info(f"FratK entries == toKK images of Frat == [[1/phi,1/phi],[1,-1/phi]] (file FratK_entries): {entries}")
    diff = [(x, y) for x in LAB for y in LAB if FratK(x, y) != Fsymm(x, y)]
    ne = (diff == [(ONE, TAU), (TAU, ONE)])
    ok &= ne
    info(f"FratK != Fsymm exactly at the off-diagonal (file FratK_ne_Fsymm): {ne} — differing entries {[fmt(d) for d in diff]}")
    # FratK^2 = I in K
    def matmul(A, B):
        return lambda i, j: k_add(k_mul(A(i, ONE), B(ONE, j)), k_mul(A(i, TAU), B(TAU, j)))
    sq = matmul(FratK, FratK)
    idm = lambda i, j: K_ONE if i == j else K_ZERO
    sq_ok = all(sq(i, j) == idm(i, j) for i in LAB for j in LAB)
    ok &= sq_ok
    info(f"FratK * FratK == I over K (file FratK_sq): {sq_ok}")
    # gauge relation, all four pairs, exact
    lam = {ONE: K_ONE, TAU: K_T}
    lamInv = {ONE: K_ONE, TAU: K_B}
    rel = all(k_mul(lam[x], Fsymm(x, y)) == k_mul(FratK(x, y), lam[y])
              for x in LAB for y in LAB)
    ok &= rel
    info(f"gauge_relation lam(x)*Fsymm(x,y) == FratK(x,y)*lam(y) for ALL 4 pairs, exact: {rel}")
    two_sided = (all(FratK(x, y) == k_mul(k_mul(lam[x], Fsymm(x, y)), lamInv[y])
                     for x in LAB for y in LAB) and
                 all(Fsymm(x, y) == k_mul(k_mul(lamInv[x], FratK(x, y)), lam[y])
                     for x in LAB for y in LAB))
    units = (k_mul(K_T, K_B) == K_ONE and k_mul(K_B, K_T) == K_ONE and
             all(k_mul(lam[x], lamInv[x]) == K_ONE and k_mul(lamInv[x], lam[x]) == K_ONE
                 for x in LAB))
    ok &= two_sided and units
    info(f"two-sided forms FratK = lam*Fsymm*lamInv and Fsymm = lamInv*FratK*lam (4 pairs each): {two_sided}; t*b = b*t = 1 and lam entrywise two-sided unit: {units}")
    # ratio table (file gauge_ratio_table / gauge_ratio_is_lambda_quotient)
    ratio = {(ONE, ONE): K_ONE, (ONE, TAU): K_B, (TAU, ONE): K_T, (TAU, TAU): K_ONE}
    rat_ok = (all(FratK(x, y) == k_mul(ratio[(x, y)], Fsymm(x, y)) for x in LAB for y in LAB) and
              all(k_mul(ratio[(x, y)], lam[y]) == lam[x] for x in LAB for y in LAB))
    ok &= rat_ok
    info(f"ratio table [[1,b],[t,1]]: FratK = ratio.*Fsymm and ratio(x,y)*lam(y) = lam(x), 4 pairs each: {rat_ok}")
    # pentagon for FratK over K: all 512, 50 live, 0 violations
    live_k, viol_k = pentStats(kR, FratK)
    pk = (live_k == 50 and viol_k == 0)
    ok &= pk
    info(f"pentagon_FratK: 512 tuples, {live_k} live (=50), {viol_k} violations (=0): {pk}")
    live_zp, viol_zp = pentStats(zpR, Frat)
    pz = (live_zp == 50 and viol_zp == 0)
    ok &= pz
    info(f"cross-check pentagon_rational_gauge at Zp level: {live_zp} live, {viol_zp} violations: {pz}")
    # negative controls for the pentagon harness (file: strict 4, wrong 5)
    Fid = lambda x, y: K_ONE if x == y else K_ZERO
    Fwrong = lambda x, y: k_neg(K_ONE) if (x, y) == (TAU, TAU) else K_ONE
    _, v_id = pentStats(kR, Fid)
    _, v_wr = pentStats(kR, Fwrong)
    ctrl = (v_id == 4 and v_wr == 5)
    ok &= ctrl
    info(f"negative controls: strict associator {v_id} violations (=4), Fwrong {v_wr} (=5): {ctrl}")
    return report("G8", ok, "toKK_add/mul symbolic, injective in the representation; FratK = toKK(Frat) with claimed entries; gauge_relation + two-sided forms exact on all 4 pairs; t*b=b*t=1; pentagon_FratK 50 live / 0 violations")

# ════════════════════════════════════════════════════════════════════════
# G9 — the C4 record: sketch diag(t,1) fails 2/4 forward, satisfies reversed
# ════════════════════════════════════════════════════════════════════════

def gaugeFails(l):
    tot = 0
    for x in LAB:
        for y in LAB:
            if k_mul(l[x], Fsymm(x, y)) != k_mul(FratK(x, y), l[y]):
                tot += 1
    return tot

def gaugeFailPairs(l):
    return [(x, y) for x in LAB for y in LAB
            if k_mul(l[x], Fsymm(x, y)) != k_mul(FratK(x, y), l[y])]

def check_G9():
    ok = True
    lam = {ONE: K_ONE, TAU: K_T}
    lamInv = {ONE: K_ONE, TAU: K_B}
    lamSketch = {ONE: K_T, TAU: K_ONE}
    g_clean = gaugeFails(lam)
    ok &= g_clean == 0
    info(f"gauge_clean: gaugeFails(diag(1,t)) = {g_clean} (=0)")
    s_fails = gaugeFails(lamSketch)
    s_pairs = gaugeFailPairs(lamSketch)
    named = (s_fails == 2 and s_pairs == [(ONE, TAU), (TAU, ONE)])
    ok &= named
    info(f"sketch_gauge_fails: gaugeFails(diag(t,1)) = {s_fails} (=2); failing pairs {[fmt(p) for p in s_pairs]} == [(1,t),(t,1)]: {named}")
    # the file docstring's concrete values at the two failing entries
    v1 = (k_mul(lamSketch[ONE], Fsymm(ONE, TAU)) == K_ONE and       # t*b = 1
          k_mul(FratK(ONE, TAU), lamSketch[TAU]) == K_INVPHI)       # (1/phi)*1
    v2 = (k_mul(lamSketch[TAU], Fsymm(TAU, ONE)) == K_B and         # 1*b = b
          k_mul(FratK(TAU, ONE), lamSketch[ONE]) == K_T)            # 1*t = t
    ok &= v1 and v2
    info(f"docstring values: at (1,t) lhs=t*b=1 vs rhs=1/phi: {v1}; at (t,1) lhs=b vs rhs=t: {v2}")
    # sketch passes 2 of 4: tie 2+2=4
    tie = (4 - s_fails == 2)
    ok &= tie
    info(f"nest tie: 4 entries = 2 fail + 2 pass: {tie}")
    # controls: trivial and non-unit diagonals also fail 2
    triv = gaugeFails({ONE: K_ONE, TAU: K_ONE})
    nonu = gaugeFails({ONE: K_ONE, TAU: K_INVPHI})
    ok &= triv == 2 and nonu == 2
    info(f"negative controls: trivial gauge fails {triv} (=2), non-unit diag(1,1/phi) fails {nonu} (=2)")
    # lamSketch = t * lamInv (file lamSketch_eq)
    eq = all(lamSketch[x] == k_mul(K_T, lamInv[x]) for x in LAB)
    ok &= eq
    info(f"lamSketch == t * lamInv pointwise: {eq}")
    # REVERSED relation: sketch and lamInv satisfy it on all 4 pairs
    rev_sketch = all(k_mul(lamSketch[x], FratK(x, y)) == k_mul(Fsymm(x, y), lamSketch[y])
                     for x in LAB for y in LAB)
    rev_inv = all(k_mul(lamInv[x], FratK(x, y)) == k_mul(Fsymm(x, y), lamInv[y])
                  for x in LAB for y in LAB)
    ok &= rev_sketch and rev_inv
    info(f"sketch_gauge_relation_reversed (diag(t,1) carries FratK to Fsymm, 4/4): {rev_sketch}; gauge_relation_reversed for lamInv (4/4): {rev_inv}")
    # negative control for direction: the correct forward gauge FAILS the reversed relation
    rev_lam_fails = [(x, y) for x in LAB for y in LAB
                     if k_mul(lam[x], FratK(x, y)) != k_mul(Fsymm(x, y), lam[y])]
    dir_ok = rev_lam_fails == [(ONE, TAU), (TAU, ONE)]
    ok &= dir_ok
    info(f"direction has teeth: diag(1,t) in the REVERSED relation fails exactly {[fmt(p) for p in rev_lam_fails]}: {dir_ok}")
    # uniqueness arithmetic (file gauge_unique_normalized): s*b = 1 => s = t
    S = (tuple(P.var(f"s{i}") for i in range(4)), tuple(P.var(f"S{i}") for i in range(4)))
    assoc = teq(k_mul(S, k_mul(K_B, K_T)), k_mul(k_mul(S, K_B), K_T))
    bt = k_mul(K_B, K_T) == K_ONE
    ok &= assoc and bt
    info(f"uniqueness step: s*(b*t) == (s*b)*t symbolically (8 indets) and b*t == 1, so s*b=1 forces s=t: {assoc and bt}")
    return report("G9", ok, "C4 verified: gauge_clean=0; sketch diag(t,1) fails exactly {(1,t),(t,1)} forward (docstring values exact) and satisfies the reversed relation 4/4, as does lamInv; forward lam fails reversed at the same 2 — direction is load-bearing")

# ════════════════════════════════════════════════════════════════════════
# G10 — declarations present; honest label; toKK_injective proof shape
# ════════════════════════════════════════════════════════════════════════

def strip_comments(src):
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i) and not src.startswith("--⟨", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)

def check_G10():
    ok = True
    src = open(LEAN, encoding="utf-8").read()
    code = strip_comments(src)
    # collect declared names with namespace qualification
    stack = []
    decls = set()
    for line in code.splitlines():
        m = re.match(r"\s*namespace\s+([A-Za-z0-9_.]+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"\s*end\s+([A-Za-z0-9_.]+)", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = re.match(r"\s*(?:theorem|def)\s+([A-Za-z0-9_']+)", line)
        if m:
            decls.add(".".join(stack + [m.group(1)]))
    def has(name):
        return any(d == name or d.endswith("." + name) for d in decls)
    wanted = ["conj_add", "conj_mul", "conj_neg", "conj_conj", "conj_inj",
              "conj_Fs", "conj_Rb", "conj_sumOver", "KK.beq_conj",
              "hexagonCheck_conj", "countHexViolations_conj",
              "chirality_left_structural", "badConj_breaks_hexagon",
              "rt_norm_one", "r1_norm_one", "toKK_add", "toKK_mul",
              "toKK_injective", "gauge_relation", "gauge_relation_reversed",
              "tier3a_tier3b_same_anyon", "pentagon_FratK"]
    missing = [w for w in wanted if not has(w)]
    ok &= not missing
    info(f"all {len(wanted)} required declarations present: {not missing}" +
         (f" — MISSING {missing}" if missing else ""))
    # KK.beq_conj specifically inside namespace KK
    kk_beq = has("KK.beq_conj")
    ok &= kk_beq
    info(f"beq_conj declared inside namespace KK (qualifies as KK.beq_conj): {kk_beq}")
    # both Z5-level and KK-level conj hom laws exist
    both = all(has(f"Z5.{n}") and has(f"KK.{n}")
               for n in ("conj_add", "conj_mul", "conj_neg", "conj_conj", "conj_inj"))
    ok &= both
    info(f"conj hom laws present at BOTH Z5 and KK level: {both}")
    # honest-label comment
    honest = ("One four-integer" in src and "conj ζ² = ζ³" in src and
              "partner" in src)
    ok &= honest
    info(f"honest-label comment present (one four-integer rfl remains: conj ζ² = ζ³ and its r_τ partner): {honest}")
    # toKK_injective: docstring mentions Classical.choice; proof destructures +
    # substs, and contains NO omega at all
    lines = src.splitlines()
    ti = next(i for i, l in enumerate(lines) if l.startswith("theorem toKK_injective"))
    # docstring: walk back to the enclosing /-- block
    dstart = ti
    while dstart > 0 and "/--" not in lines[dstart]:
        dstart -= 1
    docstring = "\n".join(lines[dstart:ti])
    body = "\n".join(lines[ti:ti + 6])
    doc_ok = "Classical.choice" in docstring
    body_ok = ("omega" not in body and "obtain" in body and "subst" in body)
    ok &= doc_ok and body_ok
    info(f"toKK_injective docstring explains the Classical.choice regression: {doc_ok}")
    info(f"toKK_injective proof: destructure (obtain) + subst, NO omega anywhere in the body (a fortiori none closing a conjunctive goal): {body_ok}")
    info("proof body: " + " | ".join(l.strip() for l in lines[ti + 1:ti + 6]))
    # hygiene: no sorry / axiom in code
    hyg = ("sorry" not in code and re.search(r"^\s*axiom\s", code, re.M) is None)
    ok &= hyg
    info(f"hygiene: no `sorry`, no `axiom` declarations in stripped source: {hyg}")
    return report("G10", ok, "all 22 required declarations present (KK.beq_conj in namespace KK); honest four-integer-rfl label present; toKK_injective = obtain+subst with NO omega, docstring records the Classical.choice regression; no sorry/axiom")

# ════════════════════════════════════════════════════════════════════════
# self-test of the harness against file receipts, then main
# ════════════════════════════════════════════════════════════════════════

def selftest():
    assert z5_mul(ZETA3, ZETA) == ZETA4                      # z5_zeta4_eq
    assert z5_mul(ZETA4, ZETA) == Z5_ONE                     # z5_zeta5_eq
    assert z5_add(z5_add(Z5_ONE, ZETA), ZETA4) == Z5_PHI     # z5_phi_eq
    assert z5_mul(Z5_PHI, Z5_INVPHI) == Z5_ONE               # z5_invPhi_mul
    assert z5_mul(Z5_PHI, Z5_PHI) == z5_add(Z5_PHI, Z5_ONE)  # z5_phi_sq
    assert k_mul(K_T, K_T) == k_emb(Z5_PHI)                  # kk_t_sq
    assert k_mul(K_B, K_B) == K_INVPHI                       # kk_b_sq
    assert k_mul(K_RT, K_RT) == K_R1                         # r1_eq_rt_sq
    assert k_mul(K_R1, K_THETA) == K_ONE                     # frobenius_schur
    assert k_add(k_mul(K_R1, K_INVPHI), K_RT) == K_THETA     # ribbon_twist
    n_live = sum(1 for t in _all_tuples(6) if hexagonValid(*t))
    assert n_live == 15
    assert countHexViolations(K_R1, K_RT) == 0               # chirality_right
    assert countHexViolations(R1P, RTP) == 0                 # chirality_left
    live, viol = pentStats(kR, Fsymm)
    assert (live, viol) == (50, 0)                           # pentagon_symmetric_gauge
    print("     [harness self-test: 14 file receipts reproduced exactly]")

def discrepancy_scan():
    """Prose-level defects in the audited sections (house norm: a false label is
    a defect even when every elaborated statement is true)."""
    print("-" * 78)
    print("DISCREPANCY SCAN (doc comments in the audited sections):")
    src = open(LEAN, encoding="utf-8").read()
    # Line ~1833: the docstring on KK.conj_b reads "`b = t/√φ` is fixed".
    # Exact algebra: t = √φ, so t/√φ = t·(1/t) = t·b = 1, and b ≠ 1 — the label
    # is wrong as written.  Correct forms used elsewhere in the same file:
    # line 333 "b = t(ζ + ζ⁴) = 1/√φ" and line 1687 "fixes b = t/φ".
    phrase = "`b = t/√φ` is fixed"
    present = phrase in src
    refuted = (k_mul(K_T, K_B) == K_ONE) and (K_B != K_ONE)
    if present and refuted:
        d = ("Anyon.lean line ~1833 (docstring of KK.conj_b): says \"b = t/√φ\"; "
             "exactly t/√φ = t·b = 1 ≠ b.  Correct forms appear at line 333 "
             "(b = 1/√φ) and line 1687 (b = t/φ).  Doc-comment typo only: the "
             "elaborated theorem conj_b : conj b = b is verified true.")
        DISCREPANCIES.append(d)
        print("  FOUND: " + d)
    elif present:
        print("  phrase present but refutation failed — investigate")
    else:
        print("  (b = t/√φ phrase not found — file may have been fixed)")
    if not DISCREPANCIES:
        print("  none")

def main():
    print("Round-3 audit: Galois-conjugation + gauge-equivalence sections of Anyon.lean")
    print("=" * 78)
    selftest()
    for f in (check_G1, check_G2, check_G3, check_G4, check_G5,
              check_G6, check_G7, check_G8, check_G9, check_G10):
        print("-" * 78)
        f()
    discrepancy_scan()
    print("=" * 78)
    print("SUMMARY (one line per check):")
    for cid, ok, detail in RESULTS:
        print(f"{'PASS' if ok else 'FAIL'} {cid} {detail}")
    n_fail = sum(1 for _, ok, _ in RESULTS if not ok)
    print("=" * 78)
    print(f"OVERALL: {len(RESULTS) - n_fail}/{len(RESULTS)} checks pass")
    sys.exit(1 if n_fail else 0)

if __name__ == "__main__":
    main()
