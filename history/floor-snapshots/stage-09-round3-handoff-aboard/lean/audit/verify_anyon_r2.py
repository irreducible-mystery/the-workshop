#!/usr/bin/env python3
"""Independent re-verification of Anyon.lean ROUND-2 state, in exact integer
arithmetic.  Everything below is reimplemented from the Lean definitions only
(no other Python source consulted).

Sections:
  A. Label-level grammar (fuse/memA/isOne), Fs, Rb, pentagon/hexagon checks.
  B. Rings Zp = Z[phi], Z5 = Z[zeta5], KK = Z5[t]/(t^2-phi) -- with BOTH the
     round-2 (new, canonical order u.y*v.x) and round-1 (v.x*u.y) second
     component of KK.mul, run through the whole suite, results diffed.
  C. Full round-1 rfl-theorem suite.
  D. Symbolic checks: 16-var proof new-mul == old-mul; Z5/KK ring laws.
  E. Symbolic hexagon instances hex_at_r1 / hex_at_3 / hex_at_5 over K[r1,rt]
     (value equality) and over free expression trees (structural equality
     mirroring Lean's rfl).
  F. The doc-comment derivation chains: residual3 * (b*phi) and
     residual5 * phi, with exact signs.
  G. b_unit, invPhi_unit.
"""
import sys
from itertools import product

sys.setrecursionlimit(10000)

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok), detail))

# ======================================================================
# A. Labels and the coherence machinery (polymorphic over a Rng)
# ======================================================================
ONE, TAU = 'one', 'tau'
LABELS = (ONE, TAU)

def fuse(a, b):
    # Lean: | .one, b => [b] | a, .one => [a] | .tau,.tau => [.one,.tau]
    if a == ONE: return [b]
    if b == ONE: return [a]
    return [ONE, TAU]

def memA(a, xs):
    for x in xs:
        if a == x: return True
    return False

def isOne(a): return a == ONE

class Rng:
    def __init__(self, zero, one, add, mul, beq):
        self.zero, self.one, self.add, self.mul, self.beq = zero, one, add, mul, beq

def sumOver(K, f, us):
    if not us: return K.zero
    return K.add(f(us[0]), sumOver(K, f, us[1:]))

def Fs(K, F, a, b, c, d, x, y):
    if (memA(x, fuse(a, b)) and memA(d, fuse(x, c))
            and memA(y, fuse(b, c)) and memA(d, fuse(a, y))):
        if isOne(a) or isOne(b) or isOne(c): return K.one
        if isOne(d):
            return K.one if ((not isOne(x)) and (not isOne(y))) else K.zero
        return F(x, y)
    return K.zero

def Rb(K, r1, rt, x, y, c):
    if isOne(x) or isOne(y): return K.one
    return r1 if isOne(c) else rt

def pentagonValid(a,b,c,dd,x,y,t,w,v):
    return (memA(x,fuse(a,b)) and memA(y,fuse(x,c)) and memA(t,fuse(y,dd))
            and memA(w,fuse(c,dd)) and memA(v,fuse(b,w)) and memA(t,fuse(a,v)))

def pentagonCheck(K,F,a,b,c,dd,x,y,t,w,v):
    if pentagonValid(a,b,c,dd,x,y,t,w,v):
        lhs = sumOver(K, lambda u: K.mul(K.mul(Fs(K,F,a,b,c,y,x,u),
                                               Fs(K,F,a,u,dd,t,y,v)),
                                         Fs(K,F,b,c,dd,v,u,w)), fuse(b,c))
        rhs = K.mul(Fs(K,F,x,c,dd,t,y,w), Fs(K,F,a,b,w,t,x,v))
        return K.beq(lhs, rhs)
    return True

def hexagonValid(a,b,c,d,e,z):
    return (memA(e,fuse(a,b)) and memA(d,fuse(e,c))
            and memA(z,fuse(a,c)) and memA(d,fuse(z,b)))

def hexagonSides(K,F,r1,rt,a,b,c,d,e,z):
    """LHS and RHS of the (bench-ordered) hexagon, exactly as hexagonCheck builds them."""
    lhs = K.mul(Rb(K,r1,rt,e,c,d), Fs(K,F,c,a,b,d,z,e))
    rhs = sumOver(K, lambda g: K.mul(K.mul(K.mul(Fs(K,F,a,b,c,d,e,g),
                                                 Rb(K,r1,rt,b,c,g)),
                                           Fs(K,F,a,c,b,d,z,g)),
                                     Rb(K,r1,rt,a,c,z)), fuse(b,c))
    return lhs, rhs

def hexagonCheck(K,F,r1,rt,a,b,c,d,e,z):
    if hexagonValid(a,b,c,d,e,z):
        lhs, rhs = hexagonSides(K,F,r1,rt,a,b,c,d,e,z)
        return K.beq(lhs,rhs)
    return True

def hexagonCheckCharge(K,F,r1,rt,a,b,c,d,e,z):
    """Charge's (wrong) LHS index order: Fs(c,a,b,d,e,z) i.e. x:=e, y:=z."""
    if hexagonValid(a,b,c,d,e,z):
        lhs = K.mul(Rb(K,r1,rt,e,c,d), Fs(K,F,c,a,b,d,e,z))
        rhs = sumOver(K, lambda g: K.mul(K.mul(K.mul(Fs(K,F,a,b,c,d,e,g),
                                                     Rb(K,r1,rt,b,c,g)),
                                               Fs(K,F,a,c,b,d,z,g)),
                                         Rb(K,r1,rt,a,c,z)), fuse(b,c))
        return K.beq(lhs,rhs)
    return True

def matMul(K,A,B):
    return {(i,j): K.add(K.mul(A[(i,ONE)],B[(ONE,j)]),
                         K.mul(A[(i,TAU)],B[(TAU,j)]))
            for i in LABELS for j in LABELS}
def matEq(K,A,B):
    return all(K.beq(A[(i,j)],B[(i,j)]) for i in LABELS for j in LABELS)
def matId(K):
    return {(i,j): (K.one if i==j else K.zero) for i in LABELS for j in LABELS}

# ======================================================================
# B. The rings
# ======================================================================
# --- Zp = Z[phi], pairs (m,n) = m + n*phi, phi^2 = phi + 1
ZP0, ZP1, ZPPHI = (0,0), (1,0), (0,1)
def zp_add(u,v): return (u[0]+v[0], u[1]+v[1])
def zp_neg(u): return (-u[0], -u[1])
def zp_mul(u,v): return (u[0]*v[0]+u[1]*v[1], u[0]*v[1]+u[1]*v[0]+u[1]*v[1])
ZPINV = (-1,1)
zpRng = Rng(ZP0, ZP1, zp_add, zp_mul, lambda u,v: u==v)

# --- Z5 = Z[zeta5], 4-tuples (a0,a1,a2,a3) = a0+a1 z+a2 z^2+a3 z^3,
#     zeta^4 = -(1+z+z^2+z^3).  Polymorphic over entries (ints or polys).
def z5_add(u,v): return (u[0]+v[0], u[1]+v[1], u[2]+v[2], u[3]+v[3])
def z5_neg(u): return (-u[0], -u[1], -u[2], -u[3])
def z5_mul(u,v):
    c0 = u[0]*v[0]
    c1 = u[0]*v[1] + u[1]*v[0]
    c2 = u[0]*v[2] + u[1]*v[1] + u[2]*v[0]
    c3 = u[0]*v[3] + u[1]*v[2] + u[2]*v[1] + u[3]*v[0]
    c4 = u[1]*v[3] + u[2]*v[2] + u[3]*v[1]
    c5 = u[2]*v[3] + u[3]*v[2]
    c6 = u[3]*v[3]
    return (c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4)

Z50   = (0,0,0,0)
Z51   = (1,0,0,0)
ZETA  = (0,1,0,0)
ZETA2 = (0,0,1,0)
ZETA3 = (0,0,0,1)
ZETA4 = (-1,-1,-1,-1)
PHI5  = (0,0,-1,-1)      # 1 + zeta + zeta^4 reduced
INV5  = (-1,0,-1,-1)     # zeta + zeta^4 reduced

# --- KK = Z5[t]/(t^2 - phi): pairs (x,y) of Z5 elements, x + y*t
def kk_mul_new(u,v):
    """ROUND 2: second component u.x*v.y + u.y*v.x  (canonical operand order)."""
    return (z5_add(z5_mul(u[0],v[0]), z5_mul(PHI5, z5_mul(u[1],v[1]))),
            z5_add(z5_mul(u[0],v[1]), z5_mul(u[1],v[0])))

def kk_mul_old(u,v):
    """ROUND 1: second component u.x*v.y + v.x*u.y  (same value by Z5 commutativity)."""
    return (z5_add(z5_mul(u[0],v[0]), z5_mul(PHI5, z5_mul(u[1],v[1]))),
            z5_add(z5_mul(u[0],v[1]), z5_mul(v[0],u[1])))

def kk_add(u,v): return (z5_add(u[0],v[0]), z5_add(u[1],v[1]))
def kk_neg(u): return (z5_neg(u[0]), z5_neg(u[1]))
def kk_emb(u): return (u, Z50)

KKZ = (Z50, Z50)
KKO = (Z51, Z50)
KT  = (Z50, Z51)

# ======================================================================
# C. The round-1 rfl suite, parameterized by which KK.mul is installed
# ======================================================================
def run_suite(kk_mul):
    kRng = Rng(KKZ, KKO, kk_add, kk_mul, lambda u,v: u==v)
    invPhiK = kk_emb(INV5)
    bK      = kk_mul(KT, invPhiK)          # b = t * (1/phi)
    r1K     = kk_emb(ZETA2)
    rtK     = kk_emb(z5_neg(ZETA))
    thetaK  = kk_emb(ZETA3)
    r1M     = kk_emb(ZETA3)                # mirror r1'
    rtM     = kk_emb(z5_neg(ZETA4))        # mirror rt'
    thetaM  = kk_emb(ZETA2)                # mirror theta'

    FsymmD = {(ONE,ONE): invPhiK, (ONE,TAU): bK,
              (TAU,ONE): bK, (TAU,TAU): kk_neg(invPhiK)}
    Fsymm  = lambda x,y: FsymmD[(x,y)]
    FratD  = {(ONE,ONE): ZPINV, (ONE,TAU): ZPINV,
              (TAU,ONE): ZP1, (TAU,TAU): zp_neg(ZPINV)}
    Frat   = lambda x,y: FratD[(x,y)]
    FidD   = matId(kRng)
    Fid    = lambda x,y: FidD[(x,y)]
    FwrongD = {(ONE,ONE): KKO, (ONE,TAU): KKO,
               (TAU,ONE): KKO, (TAU,TAU): kk_neg(KKO)}
    Fwrong = lambda x,y: FwrongD[(x,y)]

    B1 = {(ONE,ONE): r1K, (ONE,TAU): KKZ, (TAU,ONE): KKZ, (TAU,TAU): rtK}
    B2 = matMul(kRng, matMul(kRng, FsymmD, B1), FsymmD)

    L9 = list(product(LABELS, repeat=9))
    L6 = list(product(LABELS, repeat=6))

    def pentViol(K, F):
        return sum(0 if pentagonCheck(K,F,*tp) else 1 for tp in L9)
    def hexViol(r1, rt):
        return sum(0 if hexagonCheck(kRng,Fsymm,r1,rt,*tp) else 1 for tp in L6)
    def hexViolCharge(r1, rt):
        return sum(0 if hexagonCheckCharge(kRng,Fsymm,r1,rt,*tp) else 1 for tp in L6)

    R = {}
    # Zp receipts
    R['zp_phi_sq']     = zp_mul(ZPPHI,ZPPHI) == zp_add(ZPPHI,ZP1)
    R['zp_invPhi_mul'] = zp_mul(ZPPHI,ZPINV) == ZP1
    R['invPhi_spec']   = (2*ZPINV[0] + ZPINV[1], ZPINV[1]) == (-1, 1)
    # Z5 receipts
    R['z5_zeta4_eq']   = z5_mul(ZETA3,ZETA) == ZETA4
    R['z5_zeta5_eq']   = z5_mul(ZETA4,ZETA) == Z51
    R['z5_phi_eq']     = z5_add(z5_add(Z51,ZETA),ZETA4) == PHI5
    R['z5_invPhi_eq']  = z5_add(ZETA,ZETA4) == INV5
    R['z5_invPhi_mul'] = z5_mul(PHI5,INV5) == Z51
    R['z5_phi_sq']     = z5_mul(PHI5,PHI5) == z5_add(PHI5,Z51)
    # K receipts
    R['kk_t_sq']       = kk_mul(KT,KT) == kk_emb(PHI5)
    R['kk_b_sq']       = kk_mul(bK,bK) == invPhiK
    # F.F = 1 in both gauges
    R['Frat_sq']  = matEq(zpRng, matMul(zpRng, FratD, FratD), matId(zpRng))
    R['Fsymm_sq'] = matEq(kRng, matMul(kRng, FsymmD, FsymmD), matId(kRng))
    # full pentagon / hexagon
    R['pentagon_rational_all512']  = all(pentagonCheck(zpRng,Frat,*tp) for tp in L9)
    R['pentagon_symmetric_all512'] = all(pentagonCheck(kRng,Fsymm,*tp) for tp in L9)
    R['hexagon_symmetric_all64']   = all(hexagonCheck(kRng,Fsymm,r1K,rtK,*tp) for tp in L6)
    # braid representation
    R['yang_baxter'] = matEq(kRng,
        matMul(kRng, matMul(kRng,B1,B2), B1),
        matMul(kRng, matMul(kRng,B2,B1), B2))
    R['nonabelian'] = (matEq(kRng, matMul(kRng,B1,B2), matMul(kRng,B2,B1)) == False)
    # scalar receipts
    R['r1_eq_rt_sq']     = kk_mul(rtK,rtK) == r1K
    R['frobenius_schur'] = kk_mul(r1K,thetaK) == KKO
    R['ribbon_twist']    = kk_add(kk_mul(r1K,invPhiK), rtK) == thetaK
    # strictness witnesses
    R['strictness_fails_1'] = (pentagonCheck(kRng,Fid,TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE,TAU) == False)
    R['strictness_fails_2'] = (pentagonCheck(kRng,Fid,TAU,TAU,TAU,TAU,ONE,TAU,TAU,TAU,ONE) == False)
    R['strictness_fails_3'] = (pentagonCheck(kRng,Fid,TAU,TAU,TAU,TAU,TAU,ONE,TAU,ONE,TAU) == False)
    R['strictness_fails_4'] = (pentagonCheck(kRng,Fid,TAU,TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE) == False)
    R['golden_passes_where_strict_fails'] = all([
        pentagonCheck(kRng,Fsymm,TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE,TAU),
        pentagonCheck(kRng,Fsymm,TAU,TAU,TAU,TAU,ONE,TAU,TAU,TAU,ONE),
        pentagonCheck(kRng,Fsymm,TAU,TAU,TAU,TAU,TAU,ONE,TAU,ONE,TAU),
        pentagonCheck(kRng,Fsymm,TAU,TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE)])
    # anti-vacuity counts
    R['pent_live'] = sum(1 if pentagonValid(*tp) else 0 for tp in L9)
    R['hex_live']  = sum(1 if hexagonValid(*tp) else 0 for tp in L6)
    R['pentViol_Fsymm']  = pentViol(kRng, Fsymm)
    R['pentViol_Frat']   = pentViol(zpRng, Frat)
    R['pentViol_Fid']    = pentViol(kRng, Fid)
    R['pentViol_Fwrong'] = pentViol(kRng, Fwrong)
    R['hexViol_right']   = hexViol(r1K, rtK)
    R['hexViol_left']    = hexViol(r1M, rtM)
    R['hexViol_trivial'] = hexViol(KKO, KKO)
    R['hexViol_swapped'] = hexViol(rtK, r1K)
    R['hexViol_signs']   = (hexViol(KKO,KKO), hexViol(KKO,kk_neg(KKO)),
                            hexViol(kk_neg(KKO),KKO), hexViol(kk_neg(KKO),kk_neg(KKO)))
    R['hexViol_charge_order'] = hexViolCharge(r1K, rtK)
    R['hexViol_bench_order']  = hexViol(r1K, rtK)
    # chirality receipts
    R['chiralities_distinct'] = ((r1K == r1M) == False)
    R['mirror_r1_eq_rt_sq']   = kk_mul(rtM,rtM) == r1M
    R['mirror_ribbon']        = kk_add(kk_mul(r1M,invPhiK), rtM) == thetaM
    R['mirror_frobenius']     = kk_mul(r1M,thetaM) == KKO
    # quadratic receipts
    quad = lambda r: kk_add(kk_add(kk_mul(r,r), kk_mul(invPhiK,r)), KKO)
    R['rt_root_quadratic']    = quad(rtK) == KKZ
    R['rtM_root_quadratic']   = quad(rtM) == KKZ
    R['roots_product_one']    = kk_mul(rtK,rtM) == KKO
    R['r1_roots_product_one'] = kk_mul(r1K,r1M) == KKO
    R['discriminant_negative'] = (z5_add(z5_mul(INV5,INV5), z5_neg((4,0,0,0)))
                                  == z5_neg(z5_add(PHI5,(2,0,0,0))))
    # round-2 unit receipts
    R['b_unit']      = kk_mul(bK, kk_mul(bK, kk_emb(PHI5))) == KKO
    R['invPhi_unit'] = kk_mul(invPhiK, kk_emb(PHI5)) == KKO
    return R

EXPECTED = {
    'zp_phi_sq': True, 'zp_invPhi_mul': True, 'invPhi_spec': True,
    'z5_zeta4_eq': True, 'z5_zeta5_eq': True, 'z5_phi_eq': True,
    'z5_invPhi_eq': True, 'z5_invPhi_mul': True, 'z5_phi_sq': True,
    'kk_t_sq': True, 'kk_b_sq': True,
    'Frat_sq': True, 'Fsymm_sq': True,
    'pentagon_rational_all512': True, 'pentagon_symmetric_all512': True,
    'hexagon_symmetric_all64': True,
    'yang_baxter': True, 'nonabelian': True,
    'r1_eq_rt_sq': True, 'frobenius_schur': True, 'ribbon_twist': True,
    'strictness_fails_1': True, 'strictness_fails_2': True,
    'strictness_fails_3': True, 'strictness_fails_4': True,
    'golden_passes_where_strict_fails': True,
    'pent_live': 50, 'hex_live': 15,
    'pentViol_Fsymm': 0, 'pentViol_Frat': 0, 'pentViol_Fid': 4, 'pentViol_Fwrong': 5,
    'hexViol_right': 0, 'hexViol_left': 0, 'hexViol_trivial': 4, 'hexViol_swapped': 5,
    'hexViol_signs': (4,4,5,5),
    'hexViol_charge_order': 4, 'hexViol_bench_order': 0,
    'chiralities_distinct': True,
    'mirror_r1_eq_rt_sq': True, 'mirror_ribbon': True, 'mirror_frobenius': True,
    'rt_root_quadratic': True, 'rtM_root_quadratic': True,
    'roots_product_one': True, 'r1_roots_product_one': True,
    'discriminant_negative': True,
    'b_unit': True, 'invPhi_unit': True,
}

resN = run_suite(kk_mul_new)
resO = run_suite(kk_mul_old)
check('suite_identical_under_new_and_old_KK.mul', resN == resO,
      'every closed result equal under both operand orders')
for k, v in EXPECTED.items():
    check(f'suite[{k}] == {v!r}', resN[k] == v, f'got {resN[k]!r}')

# ======================================================================
# D. Symbolic polynomial checks over Z (tiny multivariate poly class)
# ======================================================================
class IP:
    """Multivariate polynomial over Z; monomial = sorted tuple of (var,exp)."""
    __slots__ = ('d',)
    def __init__(self, d=None):
        self.d = {}
        if d:
            for m, c in d.items():
                if c: self.d[m] = c
    @staticmethod
    def const(c): return IP({(): c})
    @staticmethod
    def var(nm): return IP({((nm,1),): 1})
    @staticmethod
    def _lift(x):
        if isinstance(x, IP): return x
        if isinstance(x, int): return IP.const(x)
        raise TypeError
    def __add__(self, o):
        o = IP._lift(o); d = dict(self.d)
        for m, c in o.d.items(): d[m] = d.get(m, 0) + c
        return IP(d)
    __radd__ = __add__
    def __neg__(self): return IP({m: -c for m, c in self.d.items()})
    def __sub__(self, o): return self + (-IP._lift(o))
    def __rsub__(self, o): return IP._lift(o) + (-self)
    def __mul__(self, o):
        o = IP._lift(o); d = {}
        for m1, c1 in self.d.items():
            for m2, c2 in o.d.items():
                mm = {}
                for v, e in m1: mm[v] = mm.get(v, 0) + e
                for v, e in m2: mm[v] = mm.get(v, 0) + e
                m = tuple(sorted(mm.items()))
                d[m] = d.get(m, 0) + c1 * c2
        return IP(d)
    __rmul__ = __mul__
    def __eq__(self, o):
        try: o = IP._lift(o)
        except TypeError: return NotImplemented
        return self.d == o.d
    def __ne__(self, o): return not self.__eq__(o)

def z5sym(p):  return tuple(IP.var(f'{p}{i}') for i in range(4))
def kksym(p):  return (z5sym(p + 'x'), z5sym(p + 'y'))

u5, v5, w5 = z5sym('u'), z5sym('v'), z5sym('w')
uk, vk, wk = kksym('u'), kksym('v'), kksym('w')

check('symbolic: Z5.mul commutative (8 vars)', z5_mul(u5, v5) == z5_mul(v5, u5))
check('symbolic: Z5.mul associative (12 vars)',
      z5_mul(z5_mul(u5, v5), w5) == z5_mul(u5, z5_mul(v5, w5)))
check('symbolic: Z5 distributes (12 vars)',
      z5_mul(u5, z5_add(v5, w5)) == z5_add(z5_mul(u5, v5), z5_mul(u5, w5)))
check('symbolic: KK.mul NEW == KK.mul OLD on fully symbolic args (16 vars)',
      kk_mul_new(uk, vk) == kk_mul_old(uk, vk),
      'so the operand-order change is value-preserving on ALL of K, not just closed terms')
check('symbolic: KK.mul (new) commutative (16 vars)',
      kk_mul_new(uk, vk) == kk_mul_new(vk, uk))
check('symbolic: KK.mul (new) associative (24 vars)',
      kk_mul_new(kk_mul_new(uk, vk), wk) == kk_mul_new(uk, kk_mul_new(vk, wk)))

# ======================================================================
# E. hex_at_r1 / hex_at_3 / hex_at_5 with SYMBOLIC r1, rt
# ======================================================================
kk_mul = kk_mul_new
kRng = Rng(KKZ, KKO, kk_add, kk_mul, lambda u,v: u==v)
invPhiK = kk_emb(INV5)
bK      = kk_mul(KT, invPhiK)
r1K     = kk_emb(ZETA2)
rtK     = kk_emb(z5_neg(ZETA))
negInvPhiK = kk_neg(invPhiK)
phiK    = kk_emb(PHI5)
FsymmD = {(ONE,ONE): invPhiK, (ONE,TAU): bK, (TAU,ONE): bK, (TAU,TAU): negInvPhiK}
Fsymm  = lambda x,y: FsymmD[(x,y)]

# ---- E1: free expression trees (structural equality, mirrors the Lean rfl) --
TZERO, TONE = ('zero',), ('one',)
TR1, TRT = ('r1',), ('rt',)
TINV, TB, TNEGINV = ('invPhi',), ('b',), ('negInvPhi',)
treeRng = Rng(TZERO, TONE, lambda p,q: ('add',p,q), lambda p,q: ('mul',p,q), None)
FsymmT = lambda x,y: {(ONE,ONE): TINV, (ONE,TAU): TB,
                      (TAU,ONE): TB, (TAU,TAU): TNEGINV}[(x,y)]

def M(p,q): return ('mul',p,q)
def A(p,q): return ('add',p,q)

# displayed forms, transcribed from the Lean theorem statements verbatim
disp = {
 'hex_at_r1': (M(TR1, TONE),
               A(M(M(M(TZERO, TR1), TZERO), TRT),
                 A(M(M(M(TONE, TRT), TONE), TRT), TZERO))),
 'hex_at_3': (M(TONE, TB),
              A(M(M(M(TINV, TR1), TB), TRT),
                A(M(M(M(TB, TRT), TNEGINV), TRT), TZERO))),
 'hex_at_5': (M(TRT, TNEGINV),
              A(M(M(M(TB, TR1), TB), TRT),
                A(M(M(M(TNEGINV, TRT), TNEGINV), TRT), TZERO))),
}
inst = {
 'hex_at_r1': (TAU,TAU,TAU,ONE,TAU,TAU),
 'hex_at_3':  (TAU,TAU,TAU,TAU,ONE,TAU),
 'hex_at_5':  (TAU,TAU,TAU,TAU,TAU,TAU),
}
for nm, labels in inst.items():
    check(f'{nm}: labels pass hexagonValid', hexagonValid(*labels))
    lhsT, rhsT = hexagonSides(treeRng, FsymmT, TR1, TRT, *labels)
    check(f'{nm}: traced LHS tree == Lean-displayed LHS (STRUCTURAL)',
          lhsT == disp[nm][0], f'traced={lhsT!r}')
    check(f'{nm}: traced RHS tree == Lean-displayed RHS (STRUCTURAL)',
          rhsT == disp[nm][1], f'traced={rhsT!r}')

# ---- E2: polynomial ring K[r1,rt]  (value equality) ------------------------
def pk(d): return {k:v for k,v in d.items() if v != KKZ}
def pk_add(p,q):
    d = dict(p)
    for m,c in q.items(): d[m] = kk_add(d.get(m,KKZ), c)
    return pk(d)
def pk_neg(p): return {m: kk_neg(c) for m,c in p.items()}
def pk_sub(p,q): return pk_add(p, pk_neg(q))
def pk_mul(p,q):
    d = {}
    for (i1,j1),c1 in p.items():
        for (i2,j2),c2 in q.items():
            m = (i1+i2, j1+j2)
            d[m] = kk_add(d.get(m,KKZ), kk_mul(c1,c2))
    return pk(d)
def pk_const(c): return pk({(0,0): c})
PK0, PK1 = {}, pk_const(KKO)
PR1 = {(1,0): KKO}
PRT = {(0,1): KKO}
def pk_eval(p, r1v, rtv):
    acc = KKZ
    for (i,j),c in p.items():
        t = c
        for _ in range(i): t = kk_mul(t, r1v)
        for _ in range(j): t = kk_mul(t, rtv)
        acc = kk_add(acc, t)
    return acc
def pk_show(p):
    if not p: return '0'
    return ' + '.join(f'{c}*r1^{i}*rt^{j}' for (i,j),c in sorted(p.items()))

polyRng = Rng(PK0, PK1, pk_add, pk_mul, lambda p,q: p==q)
FsymmP = lambda x,y: pk_const(FsymmD[(x,y)])

sides_sym = {}
for nm, labels in inst.items():
    lhsP, rhsP = hexagonSides(polyRng, FsymmP, PR1, PRT, *labels)
    sides_sym[nm] = (lhsP, rhsP)

# displayed forms as polynomial VALUES (built with the exact displayed nesting)
c = pk_const
dispP = {
 'hex_at_r1': (pk_mul(PR1, PK1),
               pk_add(pk_mul(pk_mul(pk_mul(PK0,PR1),PK0),PRT),
                      pk_add(pk_mul(pk_mul(pk_mul(PK1,PRT),PK1),PRT), PK0))),
 'hex_at_3': (pk_mul(PK1, c(bK)),
              pk_add(pk_mul(pk_mul(pk_mul(c(invPhiK),PR1),c(bK)),PRT),
                     pk_add(pk_mul(pk_mul(pk_mul(c(bK),PRT),c(negInvPhiK)),PRT), PK0))),
 'hex_at_5': (pk_mul(PRT, c(negInvPhiK)),
              pk_add(pk_mul(pk_mul(pk_mul(c(bK),PR1),c(bK)),PRT),
                     pk_add(pk_mul(pk_mul(pk_mul(c(negInvPhiK),PRT),c(negInvPhiK)),PRT), PK0))),
}
for nm in inst:
    check(f'{nm}: symbolic LHS == displayed LHS as poly in K[r1,rt]',
          sides_sym[nm][0] == dispP[nm][0],
          f'sym={pk_show(sides_sym[nm][0])}')
    check(f'{nm}: symbolic RHS == displayed RHS as poly in K[r1,rt]',
          sides_sym[nm][1] == dispP[nm][1],
          f'sym={pk_show(sides_sym[nm][1])}')
    # cross-check: evaluating the symbolic sides at the golden pair matches
    # the concrete hexagon sides
    lc, rc = hexagonSides(kRng, Fsymm, r1K, rtK, *inst[nm])
    check(f'{nm}: symbolic sides evaluate to concrete sides at golden (r1,rt)',
          pk_eval(sides_sym[nm][0], r1K, rtK) == lc and
          pk_eval(sides_sym[nm][1], r1K, rtK) == rc)

# hex_at_r1's meaning: LHS-poly is exactly r1, RHS-poly exactly rt^2
check('hex_at_r1: LHS poly == r1 and RHS poly == rt^2  (i.e. claim IS r1 = rt^2)',
      sides_sym['hex_at_r1'][0] == PR1 and
      sides_sym['hex_at_r1'][1] == {(0,2): KKO})
res1 = pk_sub(*sides_sym['hex_at_r1'])
check('residual1 (LHS-RHS at tau,tau,tau,1,tau,tau) == r1 - rt^2 verbatim, unit +1',
      res1 == pk_add(PR1, pk_neg({(0,2): KKO})), pk_show(res1))

# the 15 valid hexagon instances collapse to how many distinct residuals?
canon = lambda p: tuple(sorted(p.items()))
allres = {}
for tp in product(LABELS, repeat=6):
    if hexagonValid(*tp):
        l, r = hexagonSides(polyRng, FsymmP, PR1, PRT, *tp)
        allres.setdefault(canon(pk_sub(l, r)), []).append(tp)
nonzero = [k for k in allres if dict(k)]
nzero_insts = len(allres.get((), []))
check('15 valid instances collapse to exactly 5 distinct NONZERO residual polys '
      '(plus the 0 residual on identically-satisfied instances)',
      len(nonzero) == 5 and sum(len(v) for v in allres.values()) == 15,
      f'{len(nonzero)} nonzero residuals; {nzero_insts} instances identically satisfied')
_res3_early = pk_sub(*sides_sym['hex_at_3'])
check('residual3 has nonzero constant term (= b), the fact that makes rt invertible',
      _res3_early.get((0, 0), KKZ) == bK and bK != KKZ)

# ======================================================================
# F. The two derivation chains (exact signs)
# ======================================================================
res3 = pk_sub(*sides_sym['hex_at_3'])
res5 = pk_sub(*sides_sym['hex_at_5'])
bphi = kk_mul(bK, phiK)

m3 = pk_mul(res3, pk_const(bphi))
T3 = pk_sub(pk_mul(pk_mul(pk_const(invPhiK), PRT), pk_sub(PR1, PRT)), PK1)
#    T3 = invPhi*rt*(r1 - rt) - 1
sign3 = '+1' if m3 == T3 else ('-1' if m3 == pk_neg(T3) else 'NEITHER')
check('chain 3: (LHS3-RHS3)*(b*phi) == +/-(invPhi*rt*(r1-rt) - 1)',
      sign3 in ('+1','-1'), f'sign = {sign3}; product = {pk_show(m3)}')

m5 = pk_mul(res5, pk_const(phiK))
T5 = pk_mul(PRT, pk_add(PR1, pk_add(pk_mul(pk_const(invPhiK), PRT), PK1)))
#    T5 = rt*(r1 + invPhi*rt + 1)
sign5 = '+1' if m5 == T5 else ('-1' if m5 == pk_neg(T5) else 'NEITHER')
check('chain 5: (LHS5-RHS5)*phi == +/-(rt*(r1 + invPhi*rt + 1))',
      sign5 in ('+1','-1'), f'sign = {sign5}; product = {pk_show(m5)}')

# multipliers are units (so multiplying by them is reversible)
check('multiplier b*phi is a unit: b*(b*phi) = 1  [= b_unit]',
      kk_mul(bK, bphi) == KKO)
check('multiplier phi is a unit: invPhi*phi = 1  [= invPhi_unit]',
      kk_mul(invPhiK, phiK) == KKO)

# consequences at the golden constants (the chain's conclusions, concretely)
check('golden: invPhi*rt*(r1-rt) == 1  (rt explicitly invertible)',
      kk_mul(kk_mul(invPhiK, rtK), kk_add(r1K, kk_neg(rtK))) == KKO)
check('golden: r1 + invPhi*rt + 1 == 0  (the linear relation after cancelling rt)',
      kk_add(kk_add(r1K, kk_mul(invPhiK, rtK)), KKO) == KKZ)
check('golden residual3 evaluates to 0 (hexagon holds there)',
      pk_eval(res3, r1K, rtK) == KKZ)
check('golden residual5 evaluates to 0 (hexagon holds there)',
      pk_eval(res5, r1K, rtK) == KKZ)

# ======================================================================
# G. b_unit / invPhi_unit exact statements (already used above; restate)
# ======================================================================
check('b_unit: KK.mul b (KK.mul b (emb phi)) == 1',
      kk_mul(bK, kk_mul(bK, kk_emb(PHI5))) == KKO)
check('invPhi_unit: KK.mul invPhi (emb phi) == 1',
      kk_mul(invPhiK, kk_emb(PHI5)) == KKO)
check('b as computed = (0, invPhi) i.e. invPhi * t', bK == (Z50, INV5))

# ======================================================================
# report
# ======================================================================
nfail = 0
for name, ok, detail in results:
    tag = 'PASS' if ok else 'FAIL'
    if not ok: nfail += 1
    line = f'[{tag}] {name}'
    if detail: line += f'   -- {detail}'
    print(line)
print()
print(f'residual1 = {pk_show(res1)}')
print(f'residual3 = {pk_show(res3)}')
print(f'residual5 = {pk_show(res5)}')
print(f'res3*(b*phi) = {pk_show(m3)}')
print(f'res5*phi     = {pk_show(m5)}')
print(f'sign3={sign3}  sign5={sign5}')
print(f'b*phi = {bphi}')
print()
print(f'{len(results)} checks, {nfail} failures')
sys.exit(1 if nfail else 0)
