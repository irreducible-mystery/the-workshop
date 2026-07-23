#!/usr/bin/env python3
"""Independent re-verification of /home/claude/workshop/lean/Anyon.lean.
Everything reimplemented FROM THE LEAN DEFINITIONS ONLY, exact int arithmetic.
"""
import itertools, random

# ────────────────────────── Anyon labels & fusion ──────────────────────────
ONE, TAU = 'one', 'tau'
LABELS = [ONE, TAU]

def fuse(a, b):
    # Lean pattern order: (.one, b) => [b] ; (a, .one) => [a] ; (.tau,.tau) => [one,tau]
    if a == ONE:
        return [b]
    if b == ONE:
        return [a]
    return [ONE, TAU]

def memA(a, xs):
    for x in xs:
        if a == x:
            return True
    return False

def isOne(a):
    return a == ONE

# ────────────────────────── Rng record ──────────────────────────
class Rng:
    def __init__(self, zero, one, add, mul, beq):
        self.zero, self.one, self.add, self.mul, self.beq = zero, one, add, mul, beq

def sumOver(K, f, us):
    # Lean: sumOver [] = zero ; sumOver (u::us) = add (f u) (sumOver us)  (right fold)
    acc = K.zero
    for u in reversed(us):
        acc = K.add(f(u), acc)
    return acc

# ────────────────────────── F-move and braiding phase ──────────────────────────
def Fs(K, F, a, b, c, d, x, y):
    if (memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and
        memA(y, fuse(b, c)) and memA(d, fuse(a, y))):
        if isOne(a) or isOne(b) or isOne(c):
            return K.one
        elif isOne(d):
            return K.one if ((not isOne(x)) and (not isOne(y))) else K.zero
        else:
            return F[(x, y)]
    return K.zero

def Rb(K, r1, rt, x, y, c):
    if isOne(x) or isOne(y):
        return K.one
    return r1 if isOne(c) else rt

# ────────────────────────── Coherence checks ──────────────────────────
def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and memA(t, fuse(y, dd)) and
            memA(w, fuse(c, dd)) and memA(v, fuse(b, w)) and memA(t, fuse(a, v)))

def pentagonCheck(K, F, a, b, c, dd, x, y, t, w, v):
    if pentagonValid(a, b, c, dd, x, y, t, w, v):
        lhs = sumOver(K,
                      lambda u: K.mul(K.mul(Fs(K, F, a, b, c, y, x, u),
                                            Fs(K, F, a, u, dd, t, y, v)),
                                      Fs(K, F, b, c, dd, v, u, w)),
                      fuse(b, c))
        rhs = K.mul(Fs(K, F, x, c, dd, t, y, w), Fs(K, F, a, b, w, t, x, v))
        return K.beq(lhs, rhs)
    return True

def hexagonValid(a, b, c, d, e, z):
    return (memA(e, fuse(a, b)) and memA(d, fuse(e, c)) and
            memA(z, fuse(a, c)) and memA(d, fuse(z, b)))

def hexagonCheck(K, F, r1, rt, a, b, c, d, e, z):
    if hexagonValid(a, b, c, d, e, z):
        lhs = K.mul(Rb(K, r1, rt, e, c, d), Fs(K, F, c, a, b, d, z, e))
        rhs = sumOver(K,
                      lambda g: K.mul(K.mul(K.mul(Fs(K, F, a, b, c, d, e, g),
                                                  Rb(K, r1, rt, b, c, g)),
                                            Fs(K, F, a, c, b, d, z, g)),
                                      Rb(K, r1, rt, a, c, z)),
                      fuse(b, c))
        return K.beq(lhs, rhs)
    return True

# ────────────────────────── 2x2 matrices ──────────────────────────
def matMul(K, A, B):
    return {(i, j): K.add(K.mul(A[(i, ONE)], B[(ONE, j)]),
                          K.mul(A[(i, TAU)], B[(TAU, j)]))
            for i in LABELS for j in LABELS}

def matEq(K, A, B):
    return (K.beq(A[(ONE, ONE)], B[(ONE, ONE)]) and K.beq(A[(ONE, TAU)], B[(ONE, TAU)]) and
            K.beq(A[(TAU, ONE)], B[(TAU, ONE)]) and K.beq(A[(TAU, TAU)], B[(TAU, TAU)]))

def matId(K):
    return {(i, j): (K.one if i == j else K.zero) for i in LABELS for j in LABELS}

# ────────────────────────── Tier 3a: Zp = Z[phi], pairs m + n*phi ──────────────────────────
zp_zero = (0, 0)
zp_one = (1, 0)
zp_phi = (0, 1)

def zp_add(u, v):
    return (u[0] + v[0], u[1] + v[1])

def zp_neg(u):
    return (-u[0], -u[1])

def zp_mul(u, v):
    # (a+b phi)(c+d phi) = (ac+bd) + (ad+bc+bd) phi
    return (u[0] * v[0] + u[1] * v[1], u[0] * v[1] + u[1] * v[0] + u[1] * v[1])

def zp_beq(u, v):
    return u == v

zp_invPhi = (-1, 1)
zpRng = Rng(zp_zero, zp_one, zp_add, zp_mul, zp_beq)

Frat = {(ONE, ONE): zp_invPhi, (ONE, TAU): zp_invPhi,
        (TAU, ONE): zp_one, (TAU, TAU): zp_neg(zp_invPhi)}

# ────────────────────────── Tier 3b: Z5 = Z[zeta_5], 4-tuples ──────────────────────────
z5_zero = (0, 0, 0, 0)
z5_one = (1, 0, 0, 0)

def z5_add(u, v):
    return tuple(u[i] + v[i] for i in range(4))

def z5_neg(u):
    return tuple(-u[i] for i in range(4))

def z5_mul(u, v):
    # convolve to degree 6, then reduce with zeta^4 = -(1+z+z^2+z^3), zeta^5=1, zeta^6=zeta
    c0 = u[0] * v[0]
    c1 = u[0] * v[1] + u[1] * v[0]
    c2 = u[0] * v[2] + u[1] * v[1] + u[2] * v[0]
    c3 = u[0] * v[3] + u[1] * v[2] + u[2] * v[1] + u[3] * v[0]
    c4 = u[1] * v[3] + u[2] * v[2] + u[3] * v[1]
    c5 = u[2] * v[3] + u[3] * v[2]
    c6 = u[3] * v[3]
    return (c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4)

def z5_beq(u, v):
    return u == v

z5_zeta = (0, 1, 0, 0)
z5_zeta2 = (0, 0, 1, 0)
z5_zeta3 = (0, 0, 0, 1)
z5_zeta4 = (-1, -1, -1, -1)
z5_phi = (0, 0, -1, -1)
z5_invPhi = (-1, 0, -1, -1)

# ────────────────────────── KK = Z5[t]/(t^2 - phi), pairs x + y*t ──────────────────────────
kk_zero = (z5_zero, z5_zero)
kk_one = (z5_one, z5_zero)

def kk_emb(u):
    return (u, z5_zero)

kk_t = (z5_zero, z5_one)

def kk_add(u, v):
    return (z5_add(u[0], v[0]), z5_add(u[1], v[1]))

def kk_neg(u):
    return (z5_neg(u[0]), z5_neg(u[1]))

def kk_mul(u, v):
    # (x1+y1 t)(x2+y2 t) = (x1 x2 + phi y1 y2) + (x1 y2 + x2 y1) t
    return (z5_add(z5_mul(u[0], v[0]), z5_mul(z5_phi, z5_mul(u[1], v[1]))),
            z5_add(z5_mul(u[0], v[1]), z5_mul(v[0], u[1])))

def kk_beq(u, v):
    return u == v

kk_invPhi = kk_emb(z5_invPhi)
kk_b = kk_mul(kk_t, kk_invPhi)
kk_r1 = kk_emb(z5_zeta2)
kk_rt = kk_emb(z5_neg(z5_zeta))
kk_theta = kk_emb(z5_zeta3)

kRng = Rng(kk_zero, kk_one, kk_add, kk_mul, kk_beq)

Fsymm = {(ONE, ONE): kk_invPhi, (ONE, TAU): kk_b,
         (TAU, ONE): kk_b, (TAU, TAU): kk_neg(kk_invPhi)}
Fid = matId(kRng)
Fwrong = {(ONE, ONE): kk_one, (ONE, TAU): kk_one,
          (TAU, ONE): kk_one, (TAU, TAU): kk_neg(kk_one)}

B1 = {(ONE, ONE): kk_r1, (ONE, TAU): kk_zero,
      (TAU, ONE): kk_zero, (TAU, TAU): kk_rt}
B2 = matMul(kRng, matMul(kRng, Fsymm, B1), Fsymm)

# Mirror constants
r1p = kk_emb(z5_zeta3)
rtp = kk_emb(z5_neg(z5_zeta4))
thetap = kk_emb(z5_zeta2)

# ────────────────────────── Counters ──────────────────────────
def countPentValid():
    return sum(1 for tup in itertools.product(LABELS, repeat=9) if pentagonValid(*tup))

def countHexValid():
    return sum(1 for tup in itertools.product(LABELS, repeat=6) if hexagonValid(*tup))

def countPentViolations(K, F):
    return sum(0 if pentagonCheck(K, F, *tup) else 1
               for tup in itertools.product(LABELS, repeat=9))

def pentViolationTuples(K, F):
    return [tup for tup in itertools.product(LABELS, repeat=9)
            if not pentagonCheck(K, F, *tup)]

def countHexViolations(r1, rt):
    return sum(0 if hexagonCheck(kRng, Fsymm, r1, rt, *tup) else 1
               for tup in itertools.product(LABELS, repeat=6))

def hexagonCheckCharge(r1, rt, a, b, c, d, e, z):
    # Charge ordering: LHS F-move is Fs(c,a,b,d,e,z) — last two swapped vs bench
    if hexagonValid(a, b, c, d, e, z):
        lhs = kRng.mul(Rb(kRng, r1, rt, e, c, d), Fs(kRng, Fsymm, c, a, b, d, e, z))
        rhs = sumOver(kRng,
                      lambda g: kRng.mul(kRng.mul(kRng.mul(Fs(kRng, Fsymm, a, b, c, d, e, g),
                                                           Rb(kRng, r1, rt, b, c, g)),
                                                  Fs(kRng, Fsymm, a, c, b, d, z, g)),
                                         Rb(kRng, r1, rt, a, c, z)),
                      fuse(b, c))
        return kRng.beq(lhs, rhs)
    return True

def countHexViolationsCharge(r1, rt):
    return sum(0 if hexagonCheckCharge(r1, rt, *tup) else 1
               for tup in itertools.product(LABELS, repeat=6))

# ────────────────────────── The checks ──────────────────────────
results = []

def check(name, ok, detail=""):
    results.append((name, bool(ok), detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{detail}]" if detail else ""))

# Zp receipts
check("zp_phi_sq", zp_mul(zp_phi, zp_phi) == zp_add(zp_phi, zp_one),
      f"phi^2={zp_mul(zp_phi, zp_phi)}")
check("zp_invPhi_mul", zp_mul(zp_phi, zp_invPhi) == zp_one,
      f"phi*invPhi={zp_mul(zp_phi, zp_invPhi)}")
check("invPhi_spec",
      (2 * zp_invPhi[0] + zp_invPhi[1], zp_invPhi[1]) == (-1, 1),
      f"doubled coords={(2 * zp_invPhi[0] + zp_invPhi[1], zp_invPhi[1])}")
check("Frat_sq", matEq(zpRng, matMul(zpRng, Frat, Frat), matId(zpRng)))

# Z5 receipts
check("z5_zeta4_eq", z5_mul(z5_zeta3, z5_zeta) == z5_zeta4,
      f"zeta3*zeta={z5_mul(z5_zeta3, z5_zeta)}")
check("z5_zeta5_eq", z5_mul(z5_zeta4, z5_zeta) == z5_one,
      f"zeta4*zeta={z5_mul(z5_zeta4, z5_zeta)}")
check("z5_phi_eq", z5_add(z5_add(z5_one, z5_zeta), z5_zeta4) == z5_phi,
      f"1+zeta+zeta4={z5_add(z5_add(z5_one, z5_zeta), z5_zeta4)}")
check("z5_invPhi_eq", z5_add(z5_zeta, z5_zeta4) == z5_invPhi,
      f"zeta+zeta4={z5_add(z5_zeta, z5_zeta4)}")
check("z5_invPhi_mul", z5_mul(z5_phi, z5_invPhi) == z5_one,
      f"phi*invPhi={z5_mul(z5_phi, z5_invPhi)}")
check("z5_phi_sq", z5_mul(z5_phi, z5_phi) == z5_add(z5_phi, z5_one),
      f"phi^2={z5_mul(z5_phi, z5_phi)} phi+1={z5_add(z5_phi, z5_one)}")

# KK receipts
check("kk_t_sq", kk_mul(kk_t, kk_t) == kk_emb(z5_phi), f"t^2={kk_mul(kk_t, kk_t)}")
check("kk_b_sq", kk_mul(kk_b, kk_b) == kk_invPhi, f"b^2={kk_mul(kk_b, kk_b)}")
check("Fsymm_sq", matEq(kRng, matMul(kRng, Fsymm, Fsymm), matId(kRng)))

# Anti-vacuity counts
cpv, chv = countPentValid(), countHexValid()
check("pentagon_live_instances=50/512", cpv == 50, f"count={cpv} of 512")
check("hexagon_live_instances=15/64", chv == 15, f"count={chv} of 64")

# Pentagon violation counts
gp = countPentViolations(kRng, Fsymm)
check("golden_pentagon_clean=0", gp == 0, f"violations={gp}")
rp = countPentViolations(zpRng, Frat)
check("rational_pentagon_clean=0", rp == 0, f"violations={rp}")

sp = countPentViolations(kRng, Fid)
named = [
    (TAU, TAU, TAU, TAU, ONE, TAU, TAU, ONE, TAU),   # strictness_fails_1
    (TAU, TAU, TAU, TAU, ONE, TAU, TAU, TAU, ONE),   # strictness_fails_2
    (TAU, TAU, TAU, TAU, TAU, ONE, TAU, ONE, TAU),   # strictness_fails_3
    (TAU, TAU, TAU, TAU, TAU, ONE, TAU, TAU, ONE),   # strictness_fails_4
]
actual_fail = pentViolationTuples(kRng, Fid)
each_named_fails = all(pentagonCheck(kRng, Fid, *t) is False for t in named)
check("strict_pentagon_violations=4", sp == 4, f"violations={sp}")
check("strictness_fails_1..4 each false", each_named_fails)
check("strict violations exactly the 4 named tuples",
      sorted(actual_fail) == sorted(named),
      f"actual={actual_fail}")

wp = countPentViolations(kRng, Fwrong)
check("wrong_pentagon_violations=5", wp == 5, f"violations={wp}")

# Braid group
B1B2 = matMul(kRng, B1, B2)
B2B1 = matMul(kRng, B2, B1)
check("yang_baxter B1B2B1=B2B1B2",
      matEq(kRng, matMul(kRng, B1B2, B1), matMul(kRng, B2B1, B2)))
check("braiding_nonabelian B1B2!=B2B1", matEq(kRng, B1B2, B2B1) is False)

# Scalar receipts
check("r1_eq_rt_sq", kk_mul(kk_rt, kk_rt) == kk_r1, f"rt^2={kk_mul(kk_rt, kk_rt)}")
check("frobenius_schur r1*theta=1", kk_mul(kk_r1, kk_theta) == kk_one,
      f"r1*theta={kk_mul(kk_r1, kk_theta)}")
check("ribbon r1*invPhi+rt=theta",
      kk_add(kk_mul(kk_r1, kk_invPhi), kk_rt) == kk_theta,
      f"lhs={kk_add(kk_mul(kk_r1, kk_invPhi), kk_rt)}")

# Chirality
cr = countHexViolations(kk_r1, kk_rt)
check("chirality_right=0", cr == 0, f"violations={cr}")
cl = countHexViolations(r1p, rtp)
check("chirality_left=0 (mirror)", cl == 0, f"violations={cl}")
check("chiralities_distinct", kk_beq(kk_r1, r1p) is False)
check("mirror_receipts",
      kk_mul(rtp, rtp) == r1p and
      kk_add(kk_mul(r1p, kk_invPhi), rtp) == thetap and
      kk_mul(r1p, thetap) == kk_one)

tb = countHexViolations(kk_one, kk_one)
check("trivial_braiding_fails=4", tb == 4, f"violations={tb}")
sb = countHexViolations(kk_rt, kk_r1)
check("swapped_braiding_fails=5", sb == 5, f"violations={sb}")

grid = (countHexViolations(kk_one, kk_one),
        countHexViolations(kk_one, kk_neg(kk_one)),
        countHexViolations(kk_neg(kk_one), kk_one),
        countHexViolations(kk_neg(kk_one), kk_neg(kk_one)))
check("no_real_sign_braiding=(4,4,5,5)", grid == (4, 4, 5, 5), f"grid={grid}")

co = countHexViolationsCharge(kk_r1, kk_rt)
check("charge_hexagon_order_fails=4", co == 4, f"violations={co}")
bo = countHexViolations(kk_r1, kk_rt)
check("bench_hexagon_order_holds=0", bo == 0, f"violations={bo}")

# Quadratic receipts
def Q(x):
    return kk_add(kk_add(kk_mul(x, x), kk_mul(kk_invPhi, x)), kk_one)

check("rt_root_quadratic", Q(kk_rt) == kk_zero, f"Q(rt)={Q(kk_rt)}")
check("rt'_root_quadratic", Q(rtp) == kk_zero, f"Q(rt')={Q(rtp)}")
check("roots_product_one rt*rt'=1", kk_mul(kk_rt, rtp) == kk_one,
      f"rt*rt'={kk_mul(kk_rt, rtp)}")
check("r1_roots_product_one r1*r1'=1", kk_mul(kk_r1, r1p) == kk_one,
      f"r1*r1'={kk_mul(kk_r1, r1p)}")
disc_lhs = z5_add(z5_mul(z5_invPhi, z5_invPhi), z5_neg((4, 0, 0, 0)))
disc_rhs = z5_neg(z5_add(z5_phi, (2, 0, 0, 0)))
check("discriminant invPhi^2-4=-(phi+2)", disc_lhs == disc_rhs,
      f"lhs={disc_lhs} rhs={disc_rhs}")

# ────────────────────────── numpy cross-check of Z5.mul ──────────────────────────
import numpy as np
zeta_c = np.exp(2j * np.pi / 5)

def z5_val(u):
    return u[0] + u[1] * zeta_c + u[2] * zeta_c**2 + u[3] * zeta_c**3

random.seed(20260720)
max_err = 0.0
for _ in range(50):
    u = tuple(random.randint(-50, 50) for _ in range(4))
    v = tuple(random.randint(-50, 50) for _ in range(4))
    exact = z5_mul(u, v)
    err = abs(z5_val(u) * z5_val(v) - z5_val(exact))
    max_err = max(max_err, err)
check("z5_mul numpy crosscheck (50 random pairs)", max_err < 1e-8,
      f"max abs error={max_err:.3e}")

# ────────────────────────── summary ──────────────────────────
fails = [r for r in results if not r[1]]
print()
print(f"TOTAL: {len(results)} checks, {len(results) - len(fails)} passed, {len(fails)} failed")
print(f"PENT_VALID={cpv} HEX_VALID={chv} GOLDEN_PV={gp} RAT_PV={rp} STRICT_PV={sp} "
      f"WRONG_PV={wp} TRIV_HV={tb} SWAP_HV={sb} GRID={grid} CHARGE_HV={co} "
      f"MAX_CROSSCHECK_ERR={max_err:.3e}")
if fails:
    print("FAILED CHECKS:")
    for name, _, detail in fails:
        print(f"  - {name}: {detail}")
