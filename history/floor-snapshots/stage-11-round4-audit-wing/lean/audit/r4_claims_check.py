#!/usr/bin/env python3
"""r4_claims_check.py — round-4 mathematical-claims audit, checks C1..C12.

CONTEXT: the round-4 .lean sources did NOT arrive; the local .lean files are
the round-3 sources.  Nothing here is verified against round-4 Lean text.
What IS verified: exact mathematics (from definitions fixed since round 1 and
present in the round-3 sources), instrument logic, and internal consistency
of the shipped round-4 outputs (audit/axioms-round4.txt,
audit/transcript-round4.txt) against PROOFS.md.

Exact integer arithmetic only.  Standalone.  One PASS/FAIL line per check.

Algebra (fixed since round 1, cross-checked against round-3 Anyon.lean):
  Z5 = Z[zeta5], 4-tuples (a0,a1,a2,a3), z^4 = -(1+z+z^2+z^3), z^5 = 1.
  phi = -z^2-z^3 = (0,0,-1,-1); invPhi = (-1,0,-1,-1); phi*invPhi = 1.
  Zp = Z[phi], pairs (m,n) = m+n*phi, phi^2 = phi+1; invPhi = (-1,1).
  KK = pairs (x,y) of Z5 = x + y*t, t^2 = phi; b = (0,invPhi); t*b = 1.
  r1 = z^2; rt = -z; mirror rt2 = -z^4 = (1,1,1,1); sigma2: z -> z^2,
  closed form sigma2(a0,a1,a2,a3) = (a0-a2, a3-a2, a1-a2, -a2).
"""
import sys, re, time
from itertools import product
from collections import Counter

HERE = "/home/claude/workshop/lean"

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok, detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ═════════════════════════════════════════════════════════════════════════
# Scalar-generic Z5 / KK (verbatim transcription of round-3 Anyon.lean
# lines 256-264 / 324-326; serves ints AND symbolic Z-polynomials).
# ═════════════════════════════════════════════════════════════════════════
class SInt:
    zero = 0
    of  = staticmethod(lambda c: c)
    add = staticmethod(lambda a, b: a + b)
    sub = staticmethod(lambda a, b: a - b)
    neg = staticmethod(lambda a: -a)
    mul = staticmethod(lambda a, b: a * b)

class SPoly:                      # sparse Z-polynomials {sorted var tuple: int}
    zero = {}
    @staticmethod
    def of(c): return {(): c} if c else {}
    @staticmethod
    def var(i): return {(i,): 1}
    @staticmethod
    def add(u, v):
        w = dict(u)
        for m, c in v.items():
            t = w.get(m, 0) + c
            if t: w[m] = t
            else: w.pop(m, None)
        return w
    @staticmethod
    def neg(u): return {m: -c for m, c in u.items()}
    @staticmethod
    def sub(u, v): return SPoly.add(u, SPoly.neg(v))
    @staticmethod
    def mul(u, v):
        w = {}
        for m1, c1 in u.items():
            for m2, c2 in v.items():
                m = tuple(sorted(m1 + m2))
                t = w.get(m, 0) + c1 * c2
                if t: w[m] = t
                else: w.pop(m, None)
        return w

def z5_of(S, t): return tuple(S.of(c) for c in t)
def z5_add(S, u, v): return tuple(S.add(a, b) for a, b in zip(u, v))
def z5_neg(S, u): return tuple(S.neg(a) for a in u)
def z5_mul(S, u, v):
    a0, a1, a2, a3 = u; b0, b1, b2, b3 = v
    c0 = S.mul(a0, b0)
    c1 = S.add(S.mul(a0, b1), S.mul(a1, b0))
    c2 = S.add(S.add(S.mul(a0, b2), S.mul(a1, b1)), S.mul(a2, b0))
    c3 = S.add(S.add(S.add(S.mul(a0, b3), S.mul(a1, b2)), S.mul(a2, b1)), S.mul(a3, b0))
    c4 = S.add(S.add(S.mul(a1, b3), S.mul(a2, b2)), S.mul(a3, b1))
    c5 = S.add(S.mul(a2, b3), S.mul(a3, b2))
    c6 = S.mul(a3, b3)
    return (S.add(S.sub(c0, c4), c5), S.add(S.sub(c1, c4), c6),
            S.sub(c2, c4), S.sub(c3, c4))
def kk_mul_generic(S, u, v, phit=(0, 0, -1, -1)):
    phiS = z5_of(S, phit)
    return (z5_add(S, z5_mul(S, u[0], v[0]), z5_mul(S, phiS, z5_mul(S, u[1], v[1]))),
            z5_add(S, z5_mul(S, u[0], v[1]), z5_mul(S, u[1], v[0])))

I = SInt; P = SPoly
Z5_ZERO = (0, 0, 0, 0); Z5_ONE = (1, 0, 0, 0)
ZETA  = (0, 1, 0, 0); ZETA2 = (0, 0, 1, 0); ZETA3 = (0, 0, 0, 1)
ZETA4 = (-1, -1, -1, -1)
PHI5  = (0, 0, -1, -1); INVPHI5 = (-1, 0, -1, -1)
def z5m(u, v): return z5_mul(I, u, v)
def z5a(u, v): return z5_add(I, u, v)
def z5n(u): return z5_neg(I, u)

K_ZERO = (Z5_ZERO, Z5_ZERO); K_ONE = (Z5_ONE, Z5_ZERO)
def emb(u): return (u, Z5_ZERO)
K_T = (Z5_ZERO, Z5_ONE)
def km(u, v): return kk_mul_generic(I, u, v)
def ka(u, v): return (z5a(u[0], v[0]), z5a(u[1], v[1]))
def kn(u): return (z5n(u[0]), z5n(u[1]))
K_PHI = emb(PHI5); K_INVPHI = emb(INVPHI5)
K_B   = km(K_T, K_INVPHI)
K_R1  = emb(ZETA2); K_RT = emb(z5n(ZETA))
K_R1P = emb(ZETA3); K_RTP = emb(z5n(ZETA4))       # mirror; -zeta^4 = (1,1,1,1)

def sig2(a):        # closed form (verified symbolically below)
    return (a[0] - a[2], a[3] - a[2], a[1] - a[2], -a[2])
def sig2_spread(S, a):   # zeta -> zeta^2 by exponent spreading, then reduce
    z = [S.zero] * 7
    z[0], z[2], z[4], z[6] = a[0], a[1], a[2], a[3]
    c0, c1, c2, c3, c4, c5, c6 = z
    return (S.add(S.sub(c0, c4), c5), S.add(S.sub(c1, c4), c6),
            S.sub(c2, c4), S.sub(c3, c4))
def norm4(a):       # a * sigma2(a) * sigma2^2(a) * sigma2^3(a), full tuple
    n1 = sig2(a); n2 = sig2(n1); n3 = sig2(n2)
    return z5m(z5m(a, n1), z5m(n2, n3))

# Zp = Z[phi], pairs (m,n), phi^2 = phi+1 (verbatim Anyon.lean Zp.mul)
ZP_ZERO = (0, 0); ZP_ONE = (1, 0); ZP_PHI = (0, 1); ZP_INVPHI = (-1, 1)
def zp_add(u, v): return (u[0] + v[0], u[1] + v[1])
def zp_neg(u): return (-u[0], -u[1])
def zp_mul(u, v):
    return (u[0]*v[0] + u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])

# ═════════════════════════════════════════════════════════════════════════
# Coherence machinery — verbatim transcription (Fs / pentagonValid /
# pentagonCheck / hexagonValid / Rb / hexagonCheck of round-3 Anyon.lean).
# ═════════════════════════════════════════════════════════════════════════
ONE, TAU = 0, 1
LABELS = (ONE, TAU)
def fuse(a, b):
    if a == ONE: return (b,)
    if b == ONE: return (a,)
    return (ONE, TAU)
def memA(x, l): return x in l
def isOne(a): return a == ONE
def Fs(R, F, a, b, c, d, x, y):
    if memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and \
       memA(y, fuse(b, c)) and memA(d, fuse(a, y)):
        if isOne(a) or isOne(b) or isOne(c): return R["one"]
        if isOne(d):
            return R["one"] if (not isOne(x)) and (not isOne(y)) else R["zero"]
        return F[(x, y)]
    return R["zero"]
def sumOver(R, f, l):
    if not l: return R["zero"]
    return R["add"](f(l[0]), sumOver(R, f, l[1:]))
def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and
            memA(t, fuse(y, dd)) and memA(w, fuse(c, dd)) and
            memA(v, fuse(b, w)) and memA(t, fuse(a, v)))
def pent_sides(R, F, a, b, c, dd, x, y, t, w, v):
    lhs = sumOver(R, lambda u: R["mul"](R["mul"](Fs(R, F, a, b, c, y, x, u),
                                                 Fs(R, F, a, u, dd, t, y, v)),
                                        Fs(R, F, b, c, dd, v, u, w)), fuse(b, c))
    rhs = R["mul"](Fs(R, F, x, c, dd, t, y, w), Fs(R, F, a, b, w, t, x, v))
    return lhs, rhs
def pent_violations(R, F):
    live = 0; viol = 0
    for tp in product(LABELS, repeat=9):
        if pentagonValid(*tp):
            live += 1
            l, r = pent_sides(R, F, *tp)
            if not R["beq"](l, r): viol += 1
    return live, viol
def hexagonValid(a, b, c, d, e, z):
    return (memA(e, fuse(a, b)) and memA(d, fuse(e, c)) and
            memA(z, fuse(a, c)) and memA(d, fuse(z, b)))
def Rb(R, r1v, rtv, x, y, c):
    if isOne(x) or isOne(y): return R["one"]
    if isOne(c): return r1v
    return rtv
def hex_sides(R, F, r1v, rtv, a, b, c, d, e, z):
    lhs = R["mul"](Rb(R, r1v, rtv, e, c, d), Fs(R, F, c, a, b, d, z, e))
    rhs = sumOver(R, lambda g:
                  R["mul"](R["mul"](R["mul"](Fs(R, F, a, b, c, d, e, g),
                                             Rb(R, r1v, rtv, b, c, g)),
                                    Fs(R, F, a, c, b, d, z, g)),
                           Rb(R, r1v, rtv, a, c, z)), fuse(b, c))
    return lhs, rhs
def hex_violations(R, F, r1v, rtv):
    live = 0; viol = 0
    for tp in product(LABELS, repeat=6):
        if hexagonValid(*tp):
            live += 1
            l, r = hex_sides(R, F, r1v, rtv, *tp)
            if not R["beq"](l, r): viol += 1
    return live, viol

RK = dict(zero=K_ZERO, one=K_ONE, add=ka, mul=km, beq=lambda a, b: a == b)
FsymmK  = {(ONE, ONE): K_INVPHI, (ONE, TAU): K_B,
           (TAU, ONE): K_B,      (TAU, TAU): kn(K_INVPHI)}
FratKK  = {(ONE, ONE): K_INVPHI, (ONE, TAU): K_INVPHI,
           (TAU, ONE): K_ONE,    (TAU, TAU): kn(K_INVPHI)}
FyangLee = {(ONE, ONE): kn(K_PHI), (ONE, TAU): kn(K_PHI),
            (TAU, ONE): K_ONE,     (TAU, TAU): K_PHI}   # (p,q,r,s)=(-phi,-phi,1,phi)

# ═════════════════════════════════════════════════════════════════════════
# Symbolic handshake: sigma2 closed form / hom / order 4; norm lands in Z
# and is multiplicative — all as polynomial identities (no sampling).
# ═════════════════════════════════════════════════════════════════════════
GA = tuple(P.var(i) for i in range(4))
GB = tuple(P.var(4 + i) for i in range(4))
sA = sig2_spread(P, GA)
check("SYM.sigma2_closed_form",
      sA == (P.sub(GA[0], GA[2]), P.sub(GA[3], GA[2]),
             P.sub(GA[1], GA[2]), P.neg(GA[2])),
      "sigma2(a) == (a0-a2, a3-a2, a1-a2, -a2) identically (generic 4-tuple)")
def sig2P(a): return sig2_spread(P, a)
check("SYM.sigma2_multiplicative",
      sig2P(z5_mul(P, GA, GB)) == z5_mul(P, sig2P(GA), sig2P(GB)),
      "sigma2(a*b) == sigma2(a)*sigma2(b) identically (8 indeterminates)")
check("SYM.sigma2_order4",
      sig2P(sig2P(sig2P(sig2P(GA)))) == GA, "sigma2^4 == id identically")
def norm4P(a):
    n1 = sig2P(a); n2 = sig2P(n1); n3 = sig2P(n2)
    return z5_mul(P, z5_mul(P, a, n1), z5_mul(P, n2, n3))
NA = norm4P(GA)
check("SYM.norm_lands_in_Z", NA[1] == {} and NA[2] == {} and NA[3] == {},
      "coordinates 1..3 of N(a) vanish identically — N is the rational coordinate")
NAB = norm4P(z5_mul(P, GA, GB))
check("SYM.norm_multiplicative",
      NAB[0] == P.mul(NA[0], norm4P(GB)[0]) and NAB[1] == {} and NAB[2] == {} and NAB[3] == {},
      "N(a*b) == N(a)*N(b) identically (8 indeterminates, degree 8)")

# ═════════════════════════════════════════════════════════════════════════
# C1 — eleven_splits
# ═════════════════════════════════════════════════════════════════════════
n3 = norm4((-3, 1, 0, 0)); n4 = norm4((-4, 1, 0, 0))
check("C1.norm_zeta_minus_3", n3 == (121, 0, 0, 0) and 121 == 11**2,
      f"N(zeta-3) = {n3[0]} = 11^2 (tail coords {n3[1:]})")
check("C1.norm_zeta_minus_4", n4 == (341, 0, 0, 0) and 341 == 11*31,
      f"N(zeta-4) = {n4[0]} = 11*31 (tail coords {n4[1:]})")
check("C1.zeta3_not_div_11", any(c % 11 != 0 for c in (-3, 1, 0, 0)),
      "zeta-3 = (-3,1,0,0): coordinate a1=1 not divisible by 11 — "
      "so 11 | N(a) does NOT force 11 | a (11 splits; contrast p=2)")
def phi5_at(c): return sum(c**k for k in range(5))
check("C1.norm_is_cyclotomic_value",
      all(norm4((-c, 1, 0, 0)) == (phi5_at(c), 0, 0, 0) for c in range(-6, 7)),
      "cross-route: N(zeta-c) == Phi5(c) for c in [-6,6]; Phi5(3)=121, Phi5(4)=341")
par = [v for v in product((0, 1), repeat=4) if v != (0, 0, 0, 0)]
odd = [v for v in par if norm4(v)[0] % 2 == 1 and norm4(v)[1:] == (0, 0, 0)]
check("C1.mod2_15_classes_odd", len(par) == 15 and len(odd) == 15,
      f"{len(odd)}/15 nonzero parity classes have ODD norm — 2 is inert; "
      "2 | N(a) => a = 0 mod 2")
r11 = sorted(x for x in range(2, 11) if pow(x, 5, 11) == 1)
check("C1.fifth_roots_mod_11", r11 == [3, 4, 5, 9] and set(r11) == {3, 9, 5, 4},
      f"nontrivial 5th roots of 1 mod 11 = {r11} = {{3,9,5,4}} — 11 splits completely")
check("C1.eleven_splits_contrast",
      n3[0] % 11 == 0 and n4[0] % 11 == 0 and any(c % 11 for c in (-3, 1, 0, 0))
      and all(norm4(v)[0] % 2 == 1 for v in par),
      "the descent's arithmetic input is a fact about p=2, not of multiplicativity: "
      "at p=11 the implication '11|N(a) => 11|a' FAILS at a=zeta-3")

# ═════════════════════════════════════════════════════════════════════════
# C2 — Q_factors: (s - rt)(s - rt2) == s^2 + invPhi*s + 1 in K[s], exactly
# ═════════════════════════════════════════════════════════════════════════
def kpoly_mul(A, B):        # lists of KK coefficients, index = degree in s
    out = [K_ZERO] * (len(A) + len(B) - 1)
    for i, ca in enumerate(A):
        for j, cb in enumerate(B):
            out[i + j] = ka(out[i + j], km(ca, cb))
    return out
lin1 = [kn(K_RT), K_ONE]        # s - rt
lin2 = [kn(K_RTP), K_ONE]       # s - rt2
prodQ = kpoly_mul(lin1, lin2)
check("C2.Q_factors_identity", prodQ == [K_ONE, K_INVPHI, K_ONE],
      "(s-rt)(s-rt2) == 1 + invPhi*s + s^2 as an exact polynomial identity in K[s]")
check("C2.sum_of_roots", ka(K_RT, K_RTP) == kn(K_INVPHI),
      "rt + rt2 == -invPhi (so the s-coefficient is +invPhi)")
check("C2.product_of_roots", km(K_RT, K_RTP) == K_ONE,
      "rt * rt2 == (-zeta)(-zeta^4) = zeta^5 = 1")
check("C2.negctrl_wrong_root", kpoly_mul(lin1, lin1) != [K_ONE, K_INVPHI, K_ONE],
      "(s-rt)^2 != s^2+invPhi*s+1 — using rt twice breaks the factorization")

# ═════════════════════════════════════════════════════════════════════════
# C3 — distinctness + both branches realized (hexagon and pentagon)
# ═════════════════════════════════════════════════════════════════════════
check("C3.rt_ne_rt2", K_RT != K_RTP,
      f"rt = (0,-1,0,0) != rt2 = (1,1,1,1): the hexagon dichotomy is sharp")
check("C3.invPhi_ne_neg_phi_Zp", ZP_INVPHI != zp_neg(ZP_PHI),
      f"in Zp: invPhi = {ZP_INVPHI} != -phi = {zp_neg(ZP_PHI)}: pentagon dichotomy sharp")
lg, vg = hex_violations(RK, FsymmK, K_R1, K_RT)
lm, vm = hex_violations(RK, FsymmK, K_R1P, K_RTP)
check("C3.hexagon_golden", (lg, vg) == (15, 0),
      f"golden (r1,rt)=(z^2,-z): {vg} of {lg} hexagon instances violated")
check("C3.hexagon_mirror", (lm, vm) == (15, 0),
      f"mirror (r1',rt2)=(z^3,-z^4): {vm} of {lm} violated — both branches realized")
lx, vx = hex_violations(RK, FsymmK, K_R1, K_RTP)
check("C3.hexagon_negctrl_mixed", lx == 15 and vx > 0,
      f"mixed pair (z^2, rt2) violates {vx}/15 — the check is sensitive")
for nm, FF in (("Fsymm", FsymmK), ("FratK", FratKK), ("YangLee", FyangLee)):
    lv, vv = pent_violations(RK, FF)
    check(f"C3.pentagon_{nm}", (lv, vv) == (50, 0),
          f"{nm}: {vv} of {lv} live pentagon instances violated in K (exact)")
def relholds(p, q, r, s, mulf, addf, negf, onev):
    return (mulf(q, r) == p, addf(mulf(p, p), p) == onev, s == negf(p))
ylP, ylQ, ylR, ylS = kn(K_PHI), kn(K_PHI), K_ONE, K_PHI
check("C3.yang_lee_relations",
      relholds(ylP, ylQ, ylR, ylS, km, ka, kn, K_ONE) == (True, True, True),
      "YangLee (p,q,r,s)=(-phi,-phi,1,phi) satisfies qr=p, p^2+p=1, s=-p exactly")
Fbad = dict(FyangLee); Fbad[(TAU, TAU)] = kn(K_PHI)     # s = -phi breaks s=-p
lb, vb = pent_violations(RK, Fbad)
check("C3.pentagon_negctrl", lb == 50 and vb > 0,
      f"perturbed YangLee (s=-phi): {vb}/50 violated — the count is load-bearing")

# ═════════════════════════════════════════════════════════════════════════
# C4 — no_gauge_golden_to_yang_lee: diagonal gauge action derived symbolically
#   vars: l1=0, lt=1, m1=2 (=l1^-1), mt=3 (=lt^-1), p=4, q=5, r=6, s=7, g=8
#   reduction: cancel (l1,m1) and (lt,mt) pairs — exactly the unit relations
# ═════════════════════════════════════════════════════════════════════════
L1, LT, M1, MT = P.var(0), P.var(1), P.var(2), P.var(3)
Pp, Qq, Rr, Ss, Gg = P.var(4), P.var(5), P.var(6), P.var(7), P.var(8)
def ured(poly):
    out = {}
    for m, c in poly.items():
        cnt = Counter(m)
        k1 = min(cnt[0], cnt[2]); cnt[0] -= k1; cnt[2] -= k1
        kt = min(cnt[1], cnt[3]); cnt[1] -= kt; cnt[3] -= kt
        mm = tuple(sorted(cnt.elements()))
        t = out.get(mm, 0) + c
        if t: out[mm] = t
        else: out.pop(mm, None)
    return out
lam  = {ONE: L1, TAU: LT}
lamI = {ONE: M1, TAU: MT}
Fcell = {(ONE, ONE): Pp, (ONE, TAU): Qq, (TAU, ONE): Rr, (TAU, TAU): Ss}
check("C4.units", ured(P.mul(L1, M1)) == P.of(1) and ured(P.mul(LT, MT)) == P.of(1),
      "l1*m1 -> 1, lt*mt -> 1: the reduction IS invertibility, nothing else")
check("C4.forced_form",
      all(ured(P.mul(P.mul(Gg, lam[y]), lamI[y])) == Gg for y in LABELS),
      "G*lam(y)*lam(y)^-1 == G: the vertex relation G(x,y)*lam(y) = lam(x)*F(x,y) "
      "forces G(x,y) = lam(x)*F(x,y)*lam(y)^-1")
Fp = {(x, y): ured(P.mul(P.mul(lam[x], Fcell[(x, y)]), lamI[y]))
      for x in LABELS for y in LABELS}
check("C4.vertex_relation_all_cells",
      all(ured(P.mul(Fp[(x, y)], lam[y])) == ured(P.mul(lam[x], Fcell[(x, y)]))
          for x in LABELS for y in LABELS),
      "lam(x)*F(x,y) == F'(x,y)*lam(y) holds identically for all 4 cells "
      "(the section-9 gauge relation, generic)")
check("C4.action_p_s_fixed",
      Fp[(ONE, ONE)] == Pp and Fp[(TAU, TAU)] == Ss,
      "p -> p and s -> s: the diagonal entries are gauge INVARIANT")
check("C4.action_q_r_scaled",
      Fp[(ONE, TAU)] == {(0, 3, 5): 1} and Fp[(TAU, ONE)] == {(1, 2, 6): 1},
      "q -> l1*lt^-1*q = (l1/lt)q and r -> lt*l1^-1*r = (lt/l1)r, exactly")
# matrix-conjugation route: diag(l1,lt) * [[p,q],[r,s]] * diag(m1,mt)
def m22mul(A, B):
    return [[P.add(P.mul(A[i][0], B[0][j]), P.mul(A[i][1], B[1][j]))
             for j in (0, 1)] for i in (0, 1)]
D  = [[L1, P.zero], [P.zero, LT]]
Di = [[M1, P.zero], [P.zero, MT]]
FM = [[Pp, Qq], [Rr, Ss]]
CONJ = m22mul(m22mul(D, FM), Di)
check("C4.matrix_conjugation_agrees",
      [[ured(CONJ[i][j]) for j in (0, 1)] for i in (0, 1)] ==
      [[Fp[(ONE, ONE)], Fp[(ONE, TAU)]], [Fp[(TAU, ONE)], Fp[(TAU, TAU)]]],
      "D F D^-1 entrywise == the vertex-relation solution (two derivations agree)")
check("C4.qr_invariant",
      ured(P.mul(Fp[(ONE, TAU)], Fp[(TAU, ONE)])) == P.mul(Qq, Rr),
      "(l1/lt)q * (lt/l1)r == qr: the off-diagonal product is also invariant")
check("C4.negctrl_needs_invertibility",
      P.mul(P.mul(L1, Pp), M1) != Pp,
      "without the unit relations l1*p*m1 != p in the free ring — "
      "the invariance spends invertibility")
check("C4.action_nontrivial", Fp[(ONE, TAU)] != Qq,
      "(l1/lt)q != q in the free ring: the gauge genuinely moves q — "
      "invariance of p,s is not the reduction trivializing everything")
sZp = zp_add(ZP_INVPHI, ZP_PHI)
check("C4.invPhi_plus_phi_Zp", sZp == (-1, 2) and sZp != (0, 0),
      f"invPhi + phi = {sZp} != 0 in Zp — the forced equation 1/phi = -phi FAILS")
check("C4.invPhi_plus_phi_Z5", z5a(INVPHI5, PHI5) == (-1, 0, -2, -2)
      and z5a(INVPHI5, PHI5) != Z5_ZERO,
      "same in Z5/K: invPhi + phi = (-1,0,-2,-2) != 0")
check("C4.conclusion_not_gauge_related",
      Fp[(ONE, ONE)] == Pp and ZP_INVPHI != zp_neg(ZP_PHI),
      "any diagonal gauge fixes p; golden p=1/phi, YangLee p=-phi, 1/phi != -phi "
      "=> the two pentagon worlds are NOT gauge-related")

# ═════════════════════════════════════════════════════════════════════════
# C5 — sigma2-lift receipts
# ═════════════════════════════════════════════════════════════════════════
s2phi = sig2(PHI5)
check("C5.sigma2_phi", s2phi == z5n(INVPHI5) and s2phi == (1, 0, 1, 1),
      "sigma2(phi) = (1,0,1,1) = -invPhi in Z5")
target = kn(K_INVPHI)     # emb(-invPhi): what a lift must send t^2 to
check("C5.lift_target",
      target == emb(z5n(INVPHI5)),
      "any multiplicative lift L of sigma2 must satisfy L(t)^2 = L(phi) = -invPhi")
sq_t  = km(K_T, K_T); sq_nt = km(kn(K_T), kn(K_T)); sq_b = km(K_B, K_B)
check("C5.candidate_t_fails",  sq_t  == K_PHI    and sq_t  != target,
      "t^2 = phi != -invPhi")
check("C5.candidate_neg_t_fails", sq_nt == K_PHI and sq_nt != target,
      "(-t)^2 = phi != -invPhi")
check("C5.candidate_b_fails",  sq_b  == K_INVPHI and sq_b  != target,
      "b^2 = invPhi != -invPhi (2*invPhi != 0)")
def s2naive(u): return (sig2(u[0]), sig2(u[1]))
lhs_w = s2naive(km(K_T, K_T)); rhs_w = km(s2naive(K_T), s2naive(K_T))
check("C5.naive_fails_at_t_t",
      lhs_w == (z5n(INVPHI5), Z5_ZERO) and rhs_w == (PHI5, Z5_ZERO) and lhs_w != rhs_w,
      "witness t*t: naive(t*t) = (-invPhi,0) = ((1,0,1,1),0) but "
      "naive(t)*naive(t) = (phi,0) = ((0,0,-1,-1),0) — componentwise sigma2 is not multiplicative")
check("C5.naive_additive",
      all(s2naive(ka(u, v)) == ka(s2naive(u), s2naive(v))
          for u in (K_T, K_B, K_R1) for v in (K_RT, K_ONE, K_PHI)),
      "context: the naive map IS additive (spots) — multiplicativity is the exact failure")

# ═════════════════════════════════════════════════════════════════════════
# C6 — t^2 = 4 control vs t^2 = phi
# ═════════════════════════════════════════════════════════════════════════
def km4(u, v): return kk_mul_generic(I, u, v, phit=(4, 0, 0, 0))
u2p = ((2, 0, 0, 0), (1, 0, 0, 0))       # 2 + t
u2m = ((2, 0, 0, 0), (-1, 0, 0, 0))      # 2 - t
prod4 = km4(u2p, u2m)
check("C6.t2_4_zero_divisor",
      prod4 == K_ZERO and u2p != K_ZERO and u2m != K_ZERO,
      "in Z5[t]/(t^2-4): (2+t)(2-t) == 0 with both factors nonzero — exact zero divisor")
# same construction at t^2 = phi: (2+t)(2-t) = 4 - phi != 0
prodK = km(u2p, u2m)
check("C6.same_pair_in_KK", prodK == emb((4, 0, 1, 1)) and prodK != K_ZERO,
      "in KK the SAME pair gives (2+t)(2-t) = 4-phi = (4,0,1,1) != 0")
# 8x8 multiplication-matrix determinant instrument (no domain assumption)
BASIS  = [emb(Z5_ONE), emb(ZETA), emb(ZETA2), emb(ZETA3),
          K_T, km(K_T, emb(ZETA)), km(K_T, emb(ZETA2)), km(K_T, emb(ZETA3))]
def det_int(M):
    M = [row[:] for row in M]; n = len(M); sign = 1; prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]
def mult_det(u, mulf):
    cols = [list(mulf(u, e)[0]) + list(mulf(u, e)[1]) for e in BASIS]
    return det_int([[cols[j][i] for j in range(8)] for i in range(8)])
d4 = mult_det(u2p, km4); dK = mult_det(u2p, km)
check("C6.det_sees_it", d4 == 0 and abs(dK) == 121,
      f"multiplication-by-(2+t) determinant: 0 at t^2=4 (zero divisor), "
      f"{dK} at t^2=phi (injective) — same instrument, opposite verdicts")
# certificate chain making the fast sweep airtight (all symbolic):
GX = tuple(P.var(i) for i in range(4)); GY = tuple(P.var(4 + i) for i in range(4))
GU = (GX, GY)
GV = (tuple(P.var(8 + i) for i in range(4)), tuple(P.var(12 + i) for i in range(4)))
GUbar = (GX, z5_neg(P, GY))
lhs_as = kk_mul_generic(P, GUbar, kk_mul_generic(P, GU, GV))
rhs_as = kk_mul_generic(P, kk_mul_generic(P, GUbar, GU), GV)
check("C6.sym_assoc_instance", lhs_as == rhs_as,
      "ubar*(u*v) == (ubar*u)*v identically in KK (16 indeterminates)")
NtG = z5_add(P, z5_mul(P, GX, GX),
             z5_neg(P, z5_mul(P, z5_of(P, PHI5), z5_mul(P, GY, GY))))
check("C6.sym_ubar_u", kk_mul_generic(P, GUbar, GU) ==
      (NtG, tuple(P.zero for _ in range(4))),
      "ubar*u == (x^2 - phi*y^2, 0) identically — the t-norm appears")
GW = tuple(P.var(i) for i in range(4)); GV5 = tuple(P.var(4 + i) for i in range(4))
check("C6.sym_scalar_mul",
      z5_mul(P, (GW[0], P.zero, P.zero, P.zero), GV5) ==
      tuple(P.mul(GW[0], GV5[i]) for i in range(4)),
      "(N,0,0,0)*v == N*v coordinatewise identically")
GC = tuple(P.var(8 + i) for i in range(4))
check("C6.sym_z5_assoc",
      z5_mul(P, GW, z5_mul(P, GV5, GC)) == z5_mul(P, z5_mul(P, GW, GV5), GC),
      "Z5 mul associative identically (12 indeterminates)")
# the sweep: every nonzero u with all 8 coefficients in [-2,2] has
# NZ(u) := N(x^2 - phi*y^2) != 0, hence (by the chain above + coordinatewise
# torsion-freeness) u*v = 0 forces v = 0 for EVERY v — no zero-divisor pair
# with either factor in the box (KK mul is commutative).
t0 = time.time()
xs = list(product(range(-2, 3), repeat=4))
bad = None; n_seen = 0
for x in xs:
    for y in xs:
        v8 = x + y
        for c in v8:
            if c:
                lead = c
                break
        else:
            continue                      # u = 0
        if lead < 0: continue             # u -> -u symmetry (NZ even in u)
        n_seen += 1
        w = z5a(z5m(x, x), z5n(z5m(PHI5, z5m(y, y))))
        n1 = sig2(w); n2 = sig2(n1); n3 = sig2(n2)
        nt = z5m(z5m(w, n1), z5m(n2, n3))
        if nt[0] == 0 or nt[1] or nt[2] or nt[3]:
            bad = (x, y, nt); break
    if bad: break
dt = time.time() - t0
check("C6.kk_no_zero_divisor_in_box", bad is None,
      f"bound |coeff|<=2 on all 8 Z5-coordinates: {n_seen} canonical nonzero u "
      f"(of 390624, u~-u), every NZ(u) != 0 => no zero-divisor pair with either "
      f"factor in the box (the box contains the (2+-t) control pair) [{dt:.1f}s]")
check("C6.commutative", km(u2p, K_B) == km(K_B, u2p) and
      km(K_RT, K_T) == km(K_T, K_RT),
      "KK mul commutative (formula symmetric; spots) — 'either factor' is licit")

# ═════════════════════════════════════════════════════════════════════════
# C7 — wrong-sign control: x^2 + phi*y^2 not multiplicative; Brahmagupta is
# ═════════════════════════════════════════════════════════════════════════
def NtI(u):  return z5a(z5m(u[0], u[0]), z5n(z5m(PHI5, z5m(u[1], u[1]))))
def NpI(u):  return z5a(z5m(u[0], u[0]), z5m(PHI5, z5m(u[1], u[1])))
u1t = ((1, 0, 0, 0), (1, 0, 0, 0))            # 1 + t
wl = NpI(km(u1t, u1t)); wr = z5m(NpI(u1t), NpI(u1t))
check("C7.wrong_sign_fails",
      wl == (2, 0, -7, -7) and wr == (2, 0, -3, -3) and wl != wr,
      "witness u=v=1+t: (x^2+phi*y^2)(u*v) = 2+7phi = (2,0,-7,-7) but "
      "product of values = 2+3phi = (2,0,-3,-3) — NOT multiplicative")
GX1 = tuple(P.var(i) for i in range(4));  GY1 = tuple(P.var(4 + i) for i in range(4))
GX2 = tuple(P.var(8 + i) for i in range(4)); GY2 = tuple(P.var(12 + i) for i in range(4))
phiP = z5_of(P, PHI5)
def NtP(x, y): return z5_add(P, z5_mul(P, x, x), z5_neg(P, z5_mul(P, phiP, z5_mul(P, y, y))))
Lbr = z5_mul(P, NtP(GX1, GY1), NtP(GX2, GY2))
Abr = z5_add(P, z5_mul(P, GX1, GX2), z5_mul(P, phiP, z5_mul(P, GY1, GY2)))
Bbr = z5_add(P, z5_mul(P, GX1, GY2), z5_mul(P, GY1, GX2))
check("C7.brahmagupta_symbolic", Lbr == NtP(Abr, Bbr),
      "(x1^2-phi y1^2)(x2^2-phi y2^2) == (x1x2+phi y1y2)^2 - phi(x1y2+y1x2)^2 "
      "identically (16 indeterminates) — the t-norm IS multiplicative")
check("C7.brahmagupta_is_kk_norm",
      all(NtI(km(u, v)) == z5m(NtI(u), NtI(v))
          for u, v in ((u1t, K_B), (K_T, K_RT), (u2p, u2m), (K_B, K_R1P))),
      "spots: Nt(u*v) == Nt(u)*Nt(v) through the actual KK mul")

# ═════════════════════════════════════════════════════════════════════════
# C8 — pentagon sufficiency: all 50 live residuals -> 0 under
#       {qr := p, p^2 := 1-p, s := -p}   (free ring Z[p,q,r,s])
# ═════════════════════════════════════════════════════════════════════════
PZERO = {}; PONE = {(): 1}
def pvar(i): return {(i,): 1}
Rfree = dict(zero=PZERO, one=PONE, add=P.add, mul=P.mul, beq=lambda a, b: a == b)
Ffree = {(ONE, ONE): pvar(0), (ONE, TAU): pvar(1),
         (TAU, ONE): pvar(2), (TAU, TAU): pvar(3)}
ALL512 = list(product(LABELS, repeat=9))
VALIDP = [tp for tp in ALL512 if pentagonValid(*tp)]
SIDESP = {tp: pent_sides(Rfree, Ffree, *tp) for tp in VALIDP}
RESP = {tp: P.sub(*SIDESP[tp]) for tp in VALIDP}
zeroP = [tp for tp in VALIDP if not RESP[tp]]
liveP = [tp for tp in VALIDP if RESP[tp]]
check("C8.split_50_39_11",
      len(VALIDP) == 50 and len(zeroP) == 39 and len(liveP) == 11,
      f"live {len(VALIDP)} = {len(zeroP)} identically-zero + {len(liveP)} nonzero")
def red_p2(poly):
    poly = dict(poly)
    while True:
        hit = next((m for m in poly if m.count(0) >= 2), None)
        if hit is None: return poly
        c = poly.pop(hit)
        rest = list(hit); rest.remove(0); rest.remove(0)
        for mm, cc in ((tuple(sorted(rest)), c), (tuple(sorted(rest + [0])), -c)):
            t = poly.get(mm, 0) + cc
            if t: poly[mm] = t
            else: poly.pop(mm, None)
def NF(poly):
    out = {}
    for m, c in poly.items():
        ep = m.count(0); eq = m.count(1); er = m.count(2); es = m.count(3)
        c *= (-1) ** es; ep += es                    # s := -p
        k = min(eq, er); ep += k; eq -= k; er -= k   # qr := p
        mm = tuple(sorted((0,) * ep + (1,) * eq + (2,) * er + (3,) * es * 0))
        t = out.get(mm, 0) + c
        if t: out[mm] = t
        else: out.pop(mm, None)
    return red_p2(out)                               # p^2 := 1-p
nred = sum(1 for tp in VALIDP if NF(RESP[tp]) == PZERO)
check("C8.all_50_reduce_to_zero", nred == 50,
      f"{nred}/50 live residuals reduce to EXACTLY 0 under "
      "{qr:=p, p^2:=1-p, s:=-p} — sufficiency, exact arithmetic")
def red_p2_wrong(poly):
    poly = dict(poly)
    while True:
        hit = next((m for m in poly if m.count(0) >= 2), None)
        if hit is None: return poly
        c = poly.pop(hit)
        rest = list(hit); rest.remove(0); rest.remove(0)
        for mm, cc in ((tuple(sorted(rest)), c), (tuple(sorted(rest + [0])), c)):
            t = poly.get(mm, 0) + cc
            if t: poly[mm] = t
            else: poly.pop(mm, None)
def NFwrong(poly):
    out = {}
    for m, c in poly.items():
        ep = m.count(0); eq = m.count(1); er = m.count(2); es = m.count(3)
        c *= (-1) ** es; ep += es
        k = min(eq, er); ep += k; eq -= k; er -= k
        mm = tuple(sorted((0,) * ep + (1,) * eq + (2,) * er))
        t = out.get(mm, 0) + c
        if t: out[mm] = t
        else: out.pop(mm, None)
    return red_p2_wrong(out)
nwrong = sum(1 for tp in liveP if NFwrong(RESP[tp]) != PZERO)
check("C8.negctrl_wrong_relation", nwrong > 0,
      f"with p^2:=1+p instead, {nwrong}/11 nonzero residuals do NOT reduce to 0")

# ═════════════════════════════════════════════════════════════════════════
# C9 — THE EIGHT SHAPES: the 39 identically-zero live instances cluster by
#       (LHS polynomial, RHS polynomial) into 8 shapes, mults {21,4,3,5,2,2,1,1}
# ═════════════════════════════════════════════════════════════════════════
def freeze(pd): return tuple(sorted(pd.items()))
shapes = Counter((freeze(SIDESP[tp][0]), freeze(SIDESP[tp][1])) for tp in zeroP)
mults = sorted(shapes.values(), reverse=True)
def prend(fz):
    if not fz: return "0"
    names = "pqrs"
    out = []
    for m, c in sorted(fz, key=lambda kv: (len(kv[0]), kv[0])):
        ms = "".join(names[i] for i in m)
        if not ms: out.append(str(c))
        elif c == 1: out.append(ms)
        elif c == -1: out.append("-" + ms)
        else: out.append(f"{c}{ms}")
    return "+".join(out).replace("+-", "-")
shape_str = "; ".join(f"{prend(l)}={prend(r)} x{n}"
                      for (l, r), n in sorted(shapes.items(), key=lambda kv: -kv[1]))
check("C9.eight_shapes", len(shapes) == 8,
      f"distinct (LHS,RHS) pairs among the 39 trivial live instances = {len(shapes)} "
      f"(claim: 8)")
check("C9.multiplicities", mults == [21, 5, 4, 3, 2, 2, 1, 1] and sum(mults) == 39,
      f"multiset {mults} vs claimed {{21,4,3,5,2,2,1,1}} (sum {sum(mults)}); "
      f"shapes: {shape_str}")
check("C9.claimed_multiset_sums_to_39",
      sorted([21, 4, 3, 5, 2, 2, 1, 1], reverse=True) == [21, 5, 4, 3, 2, 2, 1, 1]
      and sum([21, 4, 3, 5, 2, 2, 1, 1]) == 39,
      "the ledger's multiset is at least internally consistent: 8 numbers, sum 39")
# diagnostic probe: nearby syntactic clusterings (Lean-term structure, from the
# round-3 pentagonCheck/sumOver text, which round 4 says it did not change)
def T_Fs(a, b, c, d, x, y, mode):
    if memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and \
       memA(y, fuse(b, c)) and memA(d, fuse(a, y)):
        if isOne(a) or isOne(b) or isOne(c): return ('1',)
        if isOne(d):
            return ('1',) if (not isOne(x)) and (not isOne(y)) else ('0',)
        return ('F', x, y) if mode == 'cell' else ('X',)
    return ('0',)
def sumT(f, l):
    if not l: return ('0',)
    return ('+', f(l[0]), sumT(f, l[1:]))
def sides_tree(a, b, c, dd, x, y, t, w, v, mode):
    lhs = sumT(lambda u: ('*', ('*', T_Fs(a, b, c, y, x, u, mode),
                                     T_Fs(a, u, dd, t, y, v, mode)),
                               T_Fs(b, c, dd, v, u, w, mode)), fuse(b, c))
    rhs = ('*', T_Fs(x, c, dd, t, y, w, mode), T_Fs(a, b, w, t, x, v, mode))
    return lhs, rhs
cl_cell = Counter(sides_tree(*tp, 'cell') for tp in zeroP)
cl_abs  = Counter(sides_tree(*tp, 'abs') for tp in zeroP)
m_cell = sorted(cl_cell.values(), reverse=True)
m_abs  = sorted(cl_abs.values(), reverse=True)
check("C9.probe_alternative_clusterings",
      len(cl_cell) == 21 and len(cl_abs) == 11 and
      m_abs == [17, 4, 4, 3, 2, 2, 2, 2, 1, 1, 1],
      f"raw Lean expression trees: {len(cl_cell)} shapes {m_cell}; "
      f"entry-abstracted trees: {len(cl_abs)} shapes {m_abs}; "
      "neither (nor any merging of the abstracted families {2,2,2,2,4,4}) can "
      "produce the claimed 5 or 3 — the claimed multiset is not reproducible "
      "from the checker's syntax; the 8-shape bookkeeping lives in the "
      "round-4 file, which did not arrive")

# ═════════════════════════════════════════════════════════════════════════
# C10 — Laurent quotient Z[phi][q, q^-1]: p=1/phi, s=-1/phi, r=q^-1/phi
# ═════════════════════════════════════════════════════════════════════════
def lp_add(a, b):
    w = dict(a)
    for e, c in b.items():
        t = zp_add(w.get(e, ZP_ZERO), c)
        if t != ZP_ZERO: w[e] = t
        else: w.pop(e, None)
    return w
def lp_mul(a, b):
    w = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            t = zp_add(w.get(e1 + e2, ZP_ZERO), zp_mul(c1, c2))
            if t != ZP_ZERO: w[e1 + e2] = t
            else: w.pop(e1 + e2, None)
    return w
LZERO = {}; LONE = {0: ZP_ONE}
RL = dict(zero=LZERO, one=LONE, add=lp_add, mul=lp_mul, beq=lambda a, b: a == b)
Lp = {0: ZP_INVPHI}; Lq = {1: ZP_ONE}; Lr = {-1: ZP_INVPHI}; Ls = {0: zp_neg(ZP_INVPHI)}
FL = {(ONE, ONE): Lp, (ONE, TAU): Lq, (TAU, ONE): Lr, (TAU, TAU): Ls}
lL, vL = pent_violations(RL, FL)
check("C10.laurent_zero_violations", (lL, vL) == (50, 0),
      f"Z[phi][q,q^-1] with p=1/phi, s=-1/phi, q free, r=q^-1/phi: "
      f"{vL} of {lL} live pentagon instances violated")
lF, vF = pent_violations(Rfree, Ffree)
check("C10.free_ring_control_11", (lF, vF) == (50, 11),
      f"free ring Z[p,q,r,s]: {vF} of {lF} violated — the quotient is doing real work")
check("C10.nondegeneracy",
      LONE != LZERO and all(F != LZERO for F in (Lp, Lq, Lr, Ls)) and
      lp_mul(Lq, Lq) != lp_mul(Lq, lp_mul(Lq, Lq)),
      "1 != 0; p,q,r,s all nonzero; q^2 != q^3 (genuinely infinite rank)")
check("C10.relations_hold_in_laurent",
      lp_mul(Lq, Lr) == Lp and
      lp_add(lp_mul(Lp, Lp), Lp) == LONE and
      Ls == {e: zp_neg(c) for e, c in Lp.items()},
      "qr == p, p^2+p == 1, s == -p hold exactly in the Laurent ring")
FLbad = dict(FL); FLbad[(TAU, ONE)] = {-1: ZP_PHI}
lB, vB = pent_violations(RL, FLbad)
check("C10.negctrl_wrong_r", lB == 50 and vB > 0,
      f"r = q^-1*phi instead: {vB}/50 violated — evaluation is sensitive")

# ═════════════════════════════════════════════════════════════════════════
# C11 — ledger vs instrument outputs (arithmetic + hashes)
# ═════════════════════════════════════════════════════════════════════════
AX = open(f"{HERE}/audit/axioms-round4.txt", encoding="utf-8").read()
TR = open(f"{HERE}/audit/transcript-round4.txt", encoding="utf-8").read()
PM = open(f"{HERE}/PROOFS.md", encoding="utf-8").read()
R3 = open(f"{HERE}/archive/PROOFS-round3.md", encoding="utf-8").read()
FILES = ("Interchange", "MagicSquare", "Anyon", "Exchangeable")

def census_rows(text):
    rows = {}
    for m in re.finditer(r'^ ?(Interchange|MagicSquare|Anyon|Exchangeable|TOTAL)'
                         r'\s+(\d+)\s+(\d+)\s+(\d+)\s*$', text, re.M):
        rows.setdefault(m.group(1), set()).add(tuple(int(m.group(i)) for i in (2, 3, 4)))
    return rows
axr = census_rows(AX); pmr = census_rows(PM)
EXP = {"Interchange": (21, 21, 0), "MagicSquare": (63, 16, 47),
       "Anyon": (565, 250, 315), "Exchangeable": (41, 41, 0),
       "TOTAL": (690, 328, 362)}
def rows_ok(rows):
    return all(rows.get(k) == {v} for k, v in EXP.items())
trc = {m.group(1): int(m.group(2)) for m in
       re.finditer(r'^\s+(Interchange|MagicSquare|Anyon|Exchangeable)\.lean\s+(\d+)\s*$', TR, re.M)}
trt = re.search(r'^\s+TOTAL\s+(\d+)\s*$', TR, re.M)
check("C11.theorem_counts_both_instruments",
      rows_ok(axr) and trc == {"Interchange": 21, "MagicSquare": 63,
                               "Anyon": 565, "Exchangeable": 41}
      and trt and int(trt.group(1)) == 690 and sum(trc.values()) == 690
      and sum(axr[f].copy().pop()[0] for f in FILES) == 690,
      "21/63/565/41, total 690, in BOTH axioms-round4.txt and transcript-round4.txt; sums check")
check("C11.axiom_free_arithmetic",
      all(axr[f] == {EXP[f]} for f in FILES) and axr["TOTAL"] == {EXP["TOTAL"]}
      and 21 + 16 + 250 + 41 == 328 and 690 - 328 == 362
      and all(EXP[f][0] - EXP[f][1] == EXP[f][2] for f in FILES),
      "axiom-free 21/16/250/41 = 328; rest 0/47/315/0 = 362; per-row theorems-free==rest")
occ = {}
for m in re.finditer(r'^\s*(Anyon|MagicSquare)\s+\[([^\]]*)\]\s+(\d+)\s*$', AX, re.M):
    occ[(m.group(1), re.sub(r'\s+', '', m.group(2)))] = int(m.group(3))
anyon_sets = (occ.get(("Anyon", "propext"), -1), occ.get(("Anyon", "propext,Quot.sound"), -1),
              occ.get(("Anyon", "Quot.sound"), -1))
magic_sets = (occ.get(("MagicSquare", "propext"), -1),
              occ.get(("MagicSquare", "propext,Quot.sound"), -1))
check("C11.anyon_occurring_sets", anyon_sets == (19, 288, 8) and sum(anyon_sets) == 315
      and 315 == 565 - 250,
      f"Anyon sets 19+288+8 = {sum(anyon_sets)} = 565-250")
check("C11.magic_occurring_sets", magic_sets == (45, 2) and sum(magic_sets) == 47
      and 47 == 63 - 16,
      f"MagicSquare sets 45+2 = {sum(magic_sets)} = 63-16")
sax = re.search(r'^\s*sorryAx\s+(\d+)', AX, re.M)
cch = re.search(r'^\s*Classical\.choice\s+(\d+)', AX, re.M)
saxp = re.search(r'^sorryAx\s+(\d+)\s*$', PM, re.M)
cchp = re.search(r'^Classical\.choice\s+(\d+)\s*$', PM, re.M)
check("C11.hygiene_zeros",
      sax and cch and saxp and cchp and
      (sax.group(1), cch.group(1), saxp.group(1), cchp.group(1)) == ("0",) * 4,
      "sorryAx 0 and Classical.choice 0 in axioms-round4.txt AND in the PROOFS.md census block")
def olean_rows(text, style):
    if style == "instr":
        pat = (r'^(Interchange|MagicSquare|Anyon|Exchangeable)\.lean\s+exit=(\d+)\s+(\d+) ms\s+'
               r'stdout\+stderr=(\d+) bytes\s+olean=(\d+) bytes\s*\n\s*sha256\(olean\) = ([0-9a-f]{64})')
    else:
        pat = (r'^(Interchange|MagicSquare|Anyon|Exchangeable)\.lean\s+exit=(\d+)\s+(\d+) ms\s+'
               r'(\d+) bytes\s+olean\s+(\d+) B\s*\n\s+sha256\s+([0-9a-f]{64})')
    return {m.group(1): dict(exit=int(m.group(2)), ms=int(m.group(3)),
                             out=int(m.group(4)), size=int(m.group(5)), sha=m.group(6))
            for m in re.finditer(pat, text, re.M)}
tro = olean_rows(TR, "instr"); pmo = olean_rows(PM, "ledger"); r3o = olean_rows(R3, "ledger")
check("C11.parsed_all_rows",
      set(tro) == set(FILES) and set(pmo) == set(FILES) and set(r3o) == set(FILES),
      "per-file olean rows parsed from transcript-round4.txt, PROOFS.md, PROOFS-round3.md")
same3 = all(tro[f]["sha"] == r3o[f]["sha"] and tro[f]["size"] == r3o[f]["size"]
            for f in ("Interchange", "MagicSquare", "Exchangeable"))
check("C11.three_hashes_unchanged", same3,
      "Interchange/MagicSquare/Exchangeable olean sha256+size identical to round 3 "
      "(7439cf99../304712, 0e04bccd../9883616, a402def5../828248)")
check("C11.anyon_hash_changed",
      r3o["Anyon"]["sha"].startswith("84ea435a") and r3o["Anyon"]["size"] == 6160504 and
      tro["Anyon"]["sha"].startswith("5bec0f8b") and tro["Anyon"]["size"] == 10836872 and
      tro["Anyon"]["sha"] != r3o["Anyon"]["sha"],
      "Anyon olean 84ea435a../6160504 (r3) -> 5bec0f8b../10836872 (r4): changed as claimed")
check("C11.ledger_block_matches_transcript",
      all(pmo[f]["sha"] == tro[f]["sha"] and pmo[f]["size"] == tro[f]["size"]
          and pmo[f]["ms"] == tro[f]["ms"] and pmo[f]["exit"] == tro[f]["exit"] == 0
          and pmo[f]["out"] == tro[f]["out"] == 0 for f in FILES),
      "PROOFS.md transcript block == transcript-round4.txt on exit/ms/bytes/size/sha, all four files")
PMn = re.sub(r'\s+', ' ', PM)
mocc = re.search(r'Occurring sets: `\[propext, Quot\.sound\]` (\d+) in Anyon and (\d+) in '
                 r'MagicSquare; `\[propext\]` (\d+) in Anyon and (\d+) in MagicSquare; '
                 r'`\[Quot\.sound\]` alone (\d+) in Anyon', PMn)
check("C11.ledger_census_matches",
      rows_ok(pmr) and mocc and tuple(int(g) for g in mocc.groups()) == (288, 2, 19, 45, 8),
      "PROOFS.md census table == axioms-round4.txt; occurring-sets prose (288,2,19,45,8) matches")
mdt = {m.group(1): (int(m.group(2)), int(m.group(3))) for m in
       re.finditer(r'\|\s*`(Interchange|MagicSquare|Anyon|Exchangeable)\.lean`\s*\|'
                   r'\s*(\d+)\s*\|\s*\**(\d+)\**\s*\|', PM)}
mtt = re.search(r'\|\s*\*\*total\*\*\s*\|\s*\*\*(\d+)\*\*\s*\|\s*\*\*(\d+)\*\*\s*\|', PM)
r3md = {m.group(1): int(m.group(2)) for m in
        re.finditer(r'\|\s*`(Interchange|MagicSquare|Anyon|Exchangeable)\.lean`\s*\|'
                    r'\s*(\d+)\s*\|', R3)}
check("C11.round_table_consistent",
      mdt == {"Interchange": (21, 21), "MagicSquare": (63, 63),
              "Anyon": (245, 565), "Exchangeable": (41, 41)}
      and mtt and (int(mtt.group(1)), int(mtt.group(2))) == (370, 690)
      and sum(v[0] for v in mdt.values()) == 370 and sum(v[1] for v in mdt.values()) == 690
      and r3md.get("Anyon") == 245,
      "PROOFS.md round3->round4 table: 21/63/245->565/41, totals 370->690; "
      "round-3 column matches the archived round-3 census (Anyon 245)")

# ═════════════════════════════════════════════════════════════════════════
# C12 — date-field check: identical measurements, different dates
# ═════════════════════════════════════════════════════════════════════════
dtr = re.search(r'^date\s*:\s*(\S+)', TR, re.M)
dpm = re.search(r'^date\s*:\s*(\S+)', PM, re.M)
ms_tr = [tro[f]["ms"] for f in FILES]
ms_pm = [pmo[f]["ms"] for f in FILES]
check("C12.measurements_identical",
      ms_tr == ms_pm == [1659, 51082, 102185, 18219] and
      all(tro[f]["sha"] == pmo[f]["sha"] for f in FILES),
      f"per-file ms identical in both blocks: {ms_tr}; hashes identical too")
check("C12.dates_differ",
      dtr and dpm and dtr.group(1) == "2026-07-21T06:54:40Z"
      and dpm.group(1) == "2026-07-21T07:12Z" and dtr.group(1) != dpm.group(1),
      f"transcript-round4.txt says {dtr.group(1) if dtr else '?'}, PROOFS.md block says "
      f"{dpm.group(1) if dpm else '?'} — SAME measurements, DIFFERENT date: "
      "DISCREPANCY (ledger block vs instrument output), flagged for the ferry")

# ═════════════════════════════════════════════════════════════════════════
print()
nfail = sum(1 for _, ok, _ in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  ({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
