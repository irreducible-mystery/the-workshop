#!/usr/bin/env python3
"""r3_pentagon_complete.py — round-3 audit, completion of P8-P10 plus the
source-fidelity spot checks the salvaged r3_pentagon_poly.py did not cover.

Everything below is reimplemented FROM THE LEAN SOURCE
/home/claude/workshop/lean/Anyon.lean (round 3), exact integer arithmetic only.

Rings transcribed verbatim:
  Zp  (lines 175-197):  (m, n) = m + n*phi,  phi^2 = phi + 1
      mul: (ac+bd, ad+bc+bd);  invPhi = (-1, 1)
  Z5  (lines 240-277):  (a0,a1,a2,a3) = a0 + a1 z + a2 z^2 + a3 z^3,
      z^4 = -(1+z+z^2+z^3); mul = convolve to deg 6, reduce
      (c0-c4+c5, c1-c4+c6, c2-c4, c3-c4);  phi = (0,0,-1,-1),
      invPhi = (-1,0,-1,-1)
  KK  (lines 303-341):  (x, y) = x + y*t over Z5, t^2 = phi;
      mul: (x1x2 + phi*y1y2, x1y2 + y1x2);  b = t*invPhi;  t*b = 1

Associators (verbatim):
  Frat  (216-220)  over Zp : [[invPhi, invPhi], [1, -invPhi]]
  Fsymm (353-357)  over KK : [[invPhi, b], [b, -invPhi]]
  Fid   (426)      = matId;   Fwrong (508-512) = [[1,1],[1,-1]]
  Fg p q r s (1311-1315);  FratK = toKK . Frat (2238)
  toZ5 (m,n) = (m, 0, -n, -n)  (2119);  toKK = emb . toZ5 (2177)

Coherence code (Fs 96-103, pentagonValid 119-121, pentagonCheck 125-133,
sumOver 84-86, matMul/matEq/matId 157-168) transcribed as in the salvaged
script; shared here by re-transcription (independent copy, same source).
"""
import re
import sys
from itertools import product

LEAN = "/home/claude/workshop/lean/Anyon.lean"
PROOFS = "/home/claude/workshop/lean/PROOFS.md"

ONE, TAU = 0, 1
LABELS = (ONE, TAU)

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok), detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ---------------- fusion grammar (lines 54-67) ----------------
def fuse(a, b):
    if a == ONE: return (b,)
    if b == ONE: return (a,)
    return (ONE, TAU)
def memA(x, lst): return x in lst
def isOne(a): return a == ONE

# ---------------- Zp = Z[phi]  (lines 175-197) ----------------
ZP0, ZP1 = (0, 0), (1, 0)
def zp_add(u, v): return (u[0] + v[0], u[1] + v[1])
def zp_neg(u): return (-u[0], -u[1])
def zp_mul(u, v):
    m, n = u; p, q = v
    return (m * p + n * q, m * q + n * p + n * q)
ZP_PHI = (0, 1)
ZP_INVPHI = (-1, 1)
RingZp = dict(zero=ZP0, one=ZP1, add=zp_add, mul=zp_mul, beq=lambda a, b: a == b)

# ---------------- Z5 = Z[zeta5]  (lines 240-277) ----------------
Z5_0 = (0, 0, 0, 0); Z5_1 = (1, 0, 0, 0)
def z5_add(u, v): return tuple(a + b for a, b in zip(u, v))
def z5_neg(u): return tuple(-a for a in u)
def z5_mul(u, v):
    c0 = u[0]*v[0]
    c1 = u[0]*v[1] + u[1]*v[0]
    c2 = u[0]*v[2] + u[1]*v[1] + u[2]*v[0]
    c3 = u[0]*v[3] + u[1]*v[2] + u[2]*v[1] + u[3]*v[0]
    c4 = u[1]*v[3] + u[2]*v[2] + u[3]*v[1]
    c5 = u[2]*v[3] + u[3]*v[2]
    c6 = u[3]*v[3]
    return (c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4)
ZETA  = (0, 1, 0, 0); ZETA2 = (0, 0, 1, 0)
ZETA3 = (0, 0, 0, 1); ZETA4 = (-1, -1, -1, -1)
Z5_PHI    = (0, 0, -1, -1)
Z5_INVPHI = (-1, 0, -1, -1)

# ---------------- KK = Z5[t]/(t^2 - phi)  (lines 303-341) ----------------
KK0 = (Z5_0, Z5_0); KK1 = (Z5_1, Z5_0)
def emb(u): return (u, Z5_0)
KT = (Z5_0, Z5_1)                                   # t
def kk_add(u, v): return (z5_add(u[0], v[0]), z5_add(u[1], v[1]))
def kk_neg(u): return (z5_neg(u[0]), z5_neg(u[1]))
def kk_mul(u, v):
    return (z5_add(z5_mul(u[0], v[0]), z5_mul(Z5_PHI, z5_mul(u[1], v[1]))),
            z5_add(z5_mul(u[0], v[1]), z5_mul(u[1], v[0])))
KK_INVPHI = emb(Z5_INVPHI)
KB = kk_mul(KT, KK_INVPHI)                          # b = mul t invPhi (line 333)
RingKK = dict(zero=KK0, one=KK1, add=kk_add, mul=kk_mul, beq=lambda a, b: a == b)

# ---------------- coherence code (Fs / pentagonValid / pentagonCheck) ----------------
def Fs(K, F, a, b, c, d, x, y):
    if memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and \
       memA(y, fuse(b, c)) and memA(d, fuse(a, y)):
        if isOne(a) or isOne(b) or isOne(c): return K['one']
        if isOne(d):
            return K['one'] if (not isOne(x)) and (not isOne(y)) else K['zero']
        return F[(x, y)]
    return K['zero']

def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and
            memA(t, fuse(y, dd)) and memA(w, fuse(c, dd)) and
            memA(v, fuse(b, w)) and memA(t, fuse(a, v)))

def sumOver(K, f, lst):
    if not lst: return K['zero']
    return K['add'](f(lst[0]), sumOver(K, f, lst[1:]))

def pent_sides(K, F, a, b, c, dd, x, y, t, w, v):
    lhs = sumOver(K, lambda u: K['mul'](K['mul'](Fs(K, F, a, b, c, y, x, u),
                                                 Fs(K, F, a, u, dd, t, y, v)),
                                        Fs(K, F, b, c, dd, v, u, w)), fuse(b, c))
    rhs = K['mul'](Fs(K, F, x, c, dd, t, y, w), Fs(K, F, a, b, w, t, x, v))
    return lhs, rhs

def pentagonCheck(K, F, *tup):
    if pentagonValid(*tup):
        lhs, rhs = pent_sides(K, F, *tup)
        return K['beq'](lhs, rhs)
    return True

def countPentViolations(K, F):
    return sum(0 if pentagonCheck(K, F, *tp) else 1
               for tp in product(LABELS, repeat=9))

def failing_set(K, F):
    return [tp for tp in product(LABELS, repeat=9)
            if not pentagonCheck(K, F, *tp)]

ALL = list(product(LABELS, repeat=9))
VALID = [tp for tp in ALL if pentagonValid(*tp)]

# matMul / matEq / matId (lines 157-168)
def matMul(K, A, B):
    return {(i, j): K['add'](K['mul'](A[(i, ONE)], B[(ONE, j)]),
                             K['mul'](A[(i, TAU)], B[(TAU, j)]))
            for i in LABELS for j in LABELS}
def matEq(K, A, B):
    return all(K['beq'](A[(i, j)], B[(i, j)]) for i in LABELS for j in LABELS)
def matId(K):
    return {(i, j): (K['one'] if i == j else K['zero'])
            for i in LABELS for j in LABELS}

# ---------------- associators ----------------
Frat = {(ONE, ONE): ZP_INVPHI, (ONE, TAU): ZP_INVPHI,
        (TAU, ONE): ZP1, (TAU, TAU): zp_neg(ZP_INVPHI)}
Fsymm = {(ONE, ONE): KK_INVPHI, (ONE, TAU): KB,
         (TAU, ONE): KB, (TAU, TAU): kk_neg(KK_INVPHI)}
Fid = matId(RingKK)
Fwrong = {(ONE, ONE): KK1, (ONE, TAU): KK1,
          (TAU, ONE): KK1, (TAU, TAU): kk_neg(KK1)}
def Fg(p, q, r, s):
    return {(ONE, ONE): p, (ONE, TAU): q, (TAU, ONE): r, (TAU, TAU): s}
def toZ5(u):       # Zp.toZ5 (line 2119): (m,n) -> (m, 0, -n, -n)
    m, n = u
    return (m, 0, -n, -n)
def toKK(u): return emb(toZ5(u))
FratK = {k: toKK(v) for k, v in Frat.items()}

# =====================================================================
# V. source-fidelity receipts (exact re-check of the file's rfl theorems)
# =====================================================================
check("V1.z5_zeta4", z5_mul(ZETA3, ZETA) == ZETA4, "zeta3*zeta == zeta4 vector (z5_zeta4_eq)")
check("V1.z5_zeta5", z5_mul(ZETA4, ZETA) == Z5_1, "zeta^5 == 1 (z5_zeta5_eq)")
check("V1.z5_phi", z5_add(z5_add(Z5_1, ZETA), ZETA4) == Z5_PHI,
      "1+zeta+zeta4 == phi == (0,0,-1,-1) (z5_phi_eq)")
check("V1.z5_invPhi", z5_add(ZETA, ZETA4) == Z5_INVPHI,
      "zeta+zeta4 == invPhi == (-1,0,-1,-1) (z5_invPhi_eq)")
check("V1.z5_invPhi_mul", z5_mul(Z5_PHI, Z5_INVPHI) == Z5_1, "phi*invPhi == 1 (z5_invPhi_mul)")
check("V1.z5_phi_sq", z5_mul(Z5_PHI, Z5_PHI) == z5_add(Z5_PHI, Z5_1), "phi^2 == phi+1 (z5_phi_sq)")
check("V1.zp_invPhi_mul", zp_mul(ZP_PHI, ZP_INVPHI) == ZP1, "Zp: phi*invPhi == 1 (zp_invPhi_mul)")

check("V2.kk_t_sq", kk_mul(KT, KT) == emb(Z5_PHI), "t^2 == emb phi (kk_t_sq)")
check("V2.b_is_0_invPhi", KB == (Z5_0, Z5_INVPHI),
      "b = t*invPhi == (0, invPhi) in KK — task's claimed form")
check("V2.kk_b_sq", kk_mul(KB, KB) == KK_INVPHI, "b^2 == invPhi (kk_b_sq)")
check("V2.t_mul_b", kk_mul(KT, KB) == KK1 and kk_mul(KB, KT) == KK1,
      "t*b == b*t == 1 (t_mul_b, b_mul_t)")
check("V3.Fsymm_sq", matEq(RingKK, matMul(RingKK, Fsymm, Fsymm), matId(RingKK)),
      "Fsymm*Fsymm == id over KK (Fsymm_sq)")
check("V3.Frat_sq", matEq(RingZp, matMul(RingZp, Frat, Frat), matId(RingZp)),
      "Frat*Frat == id over Zp (Frat_sq)")

# V4: ALL 11 pent_at displayed forms (file lines 1341-1415), free-ring check.
# Instrument: dict-based sparse poly ring on generators 0=p,1=q,2=r,3=s.
PZERO = {}
def pconst(c): return {(): c} if c else {}
PONE = pconst(1)
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
RingP = dict(zero=PZERO, one=PONE, add=padd, mul=pmul, beq=lambda a, b: a == b)
p_, q_, r_, s_ = pvar(0), pvar(1), pvar(2), pvar(3)
FgP = Fg(p_, q_, r_, s_)

FILE11 = [(ONE,TAU,ONE,ONE,TAU),(ONE,TAU,ONE,TAU,TAU),(ONE,TAU,TAU,ONE,TAU),
          (ONE,TAU,TAU,TAU,ONE),(ONE,TAU,TAU,TAU,TAU),(TAU,ONE,TAU,ONE,TAU),
          (TAU,ONE,TAU,TAU,ONE),(TAU,TAU,ONE,ONE,TAU),(TAU,TAU,ONE,TAU,TAU),
          (TAU,TAU,TAU,ONE,TAU),(TAU,TAU,TAU,TAU,TAU)]
FILE11 = [(TAU,TAU,TAU,TAU) + t for t in FILE11]

O, Z = PONE, PZERO
# (LHS-expr, RHS-expr) exactly as displayed in pent_at_01..pent_at_11:
A, M = padd, pmul
DISPLAY = {
 1:  (A(M(M(p_,O),p_), A(M(M(q_,O),r_), Z)), M(O,O)),
 2:  (A(M(M(p_,O),q_), A(M(M(q_,O),s_), Z)), M(Z,Z)),
 3:  (A(M(M(p_,O),p_), A(M(M(q_,s_),r_), Z)), M(Z,Z)),
 4:  (A(M(M(p_,Z),Z), A(M(M(q_,r_),O), Z)), M(O,p_)),
 5:  (A(M(M(p_,O),q_), A(M(M(q_,s_),s_), Z)), M(O,q_)),
 6:  (A(M(M(Z,Z),p_), A(M(M(O,q_),r_), Z)), M(p_,O)),
 7:  (A(M(M(Z,Z),Z), A(M(M(O,p_),O), Z)), M(q_,r_)),
 8:  (A(M(M(r_,O),p_), A(M(M(s_,O),r_), Z)), M(Z,Z)),
 9:  (A(M(M(r_,O),q_), A(M(M(s_,O),s_), Z)), M(O,O)),
 10: (A(M(M(r_,O),p_), A(M(M(s_,s_),r_), Z)), M(r_,O)),
 11: (A(M(M(r_,O),q_), A(M(M(s_,s_),s_), Z)), M(s_,s_)),
}
v4ok, v4bad = True, []
for i, tp in enumerate(FILE11, start=1):
    lhs, rhs = pent_sides(RingP, FgP, *tp)
    dl, dr = DISPLAY[i]
    if not (lhs == dl and rhs == dr):
        v4ok = False; v4bad.append(i)
check("V4.pent_at_display_all_11", v4ok,
      "pent_at_01..11 displayed LHS/RHS forms == pentagonCheck sides in the "
      "free ring, side-for-side" + (f"; MISMATCH {v4bad}" if v4bad else ""))
# and the docstring residuals of the 8 instances the salvage script skipped:
DOC = {2: psub(pmul(p_,q_), pneg(pmul(q_,s_))),                     # pq+qs
       5: padd(pmul(p_,q_), padd(pmul(pmul(q_,s_),s_), pneg(q_))),  # pq+qs^2-q
       6: psub(pmul(q_,r_), p_),                                    # qr-p
       7: psub(p_, pmul(q_,r_)),                                    # p-qr
       8: padd(pmul(r_,p_), pmul(s_,r_)),                           # pr+rs
       9: padd(pmul(q_,r_), padd(pmul(s_,s_), pconst(-1))),         # qr+s^2-1
       10: padd(pmul(r_,p_), padd(pmul(pmul(s_,s_),r_), pneg(r_))), # pr+s^2 r-r
       11: padd(pmul(q_,r_), padd(pmul(pmul(s_,s_),s_),
                                  pneg(pmul(s_,s_))))}              # qr+s^3-s^2
docok = all(psub(*pent_sides(RingP, FgP, *FILE11[i-1])) == DOC[i] for i in DOC)
check("V4.docstring_residuals_8_more", docok,
      "residuals #2,5,6,7,8,9,10,11 == docstring polynomials (completes "
      "salvage P3 which did #1,#3,#4)")

# V5: Fg specializations (Fg_symm, Fg_id, Fg_wrong), entrywise in exact KK.
check("V5.Fg_symm", Fg(KK_INVPHI, KB, KB, kk_neg(KK_INVPHI)) == Fsymm,
      "Fg invPhi b b (-invPhi) == Fsymm entrywise")
check("V5.Fg_id", Fg(KK1, KK0, KK0, KK1) == Fid, "Fg 1 0 0 1 == matId")
check("V5.Fg_wrong", Fg(KK1, KK1, KK1, kk_neg(KK1)) == Fwrong,
      "Fg 1 1 1 (-1) == Fwrong")

# =====================================================================
# P8. negative controls: strict fails exactly 4, wrong fails exactly 5
# =====================================================================
def idx_of(tp):  # file index #1..#11 if tp is one of the 11, else None
    return FILE11.index(tp) + 1 if tp in FILE11 else None

fail_id = failing_set(RingKK, Fid)
fail_wr = failing_set(RingKK, Fwrong)
check("P8.strict_count_4", len(fail_id) == 4,
      f"countPentViolations(KK, Fid) = {len(fail_id)} "
      "(strict_pentagon_violations / strict_is_Fg_and_fails)")
check("P8.wrong_count_5", len(fail_wr) == 5,
      f"countPentViolations(KK, Fwrong) = {len(fail_wr)} "
      "(wrong_pentagon_violations / wrong_is_Fg_and_fails)")
idx_id = sorted(idx_of(tp) for tp in fail_id)
idx_wr = sorted(idx_of(tp) for tp in fail_wr)
check("P8.strict_set", idx_id == [3, 4, 6, 7],
      f"strict failing set = file instances {idx_id} = "
      "(x,y,t,w,v) in {(1,t,t,1,t),(1,t,t,t,1),(t,1,t,1,t),(t,1,t,t,1)}, "
      "all at (a,b,c,d)=(tttt)")
check("P8.wrong_set", idx_wr == [1, 5, 9, 10, 11],
      f"wrong failing set = file instances {idx_wr}, all at (tttt)")
# the file's four named strictness witnesses (lines 431-449) == the strict set
WITNESSES = [(TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE,TAU),
             (TAU,TAU,TAU,TAU,ONE,TAU,TAU,TAU,ONE),
             (TAU,TAU,TAU,TAU,TAU,ONE,TAU,ONE,TAU),
             (TAU,TAU,TAU,TAU,TAU,ONE,TAU,TAU,ONE)]
check("P8.named_witnesses", sorted(fail_id) == sorted(WITNESSES),
      "strictness_fails_1..4 tuples are EXACTLY the failing set (no others)")
# claimed sides: witness 1: left 1 right 0; witness 2: left 0 right 1
l1, r1_ = pent_sides(RingKK, Fid, *WITNESSES[0])
l2, r2_ = pent_sides(RingKK, Fid, *WITNESSES[1])
check("P8.witness_sides", l1 == KK1 and r1_ == KK0 and l2 == KK0 and r2_ == KK1,
      "witness1 LHS=1,RHS=0; witness2 LHS=0,RHS=1 (docstrings, lines 428-439)")
# golden passes exactly where strict fails; both clean overall
check("P8.golden_passes_there",
      all(pentagonCheck(RingKK, Fsymm, *tp) for tp in fail_id),
      "Fsymm passes the 4 strict-failing instances (golden_passes_where_strict_fails)")
check("P8.golden_clean", countPentViolations(RingKK, Fsymm) == 0,
      "countPentViolations(KK, Fsymm) = 0 (golden_pentagon_clean)")
check("P8.rational_clean", countPentViolations(RingZp, Frat) == 0,
      "countPentViolations(Zp, Frat) = 0 (rational_pentagon_clean)")
check("P8.sets_disjoint", not (set(fail_id) & set(fail_wr)),
      "strict and wrong failing sets are disjoint: {3,4,6,7} vs {1,5,9,10,11}")
check("P8.all_at_tttt",
      all(tp[:4] == (TAU,)*4 for tp in fail_id + fail_wr),
      "all 9 failures at total charge (tau,tau,tau,tau)")

# =====================================================================
# P9. two-solution witness; the connecting lambda, exactly
# =====================================================================
# FratK entries (FratK_entries, lines 2244-2249)
check("P9.toZ5_invPhi", toZ5(ZP_INVPHI) == Z5_INVPHI,
      "Zp.invPhi (-1,1) -> Z5.invPhi (-1,0,-1,-1) under toZ5")
check("P9.FratK_entries",
      FratK == Fg(KK_INVPHI, KK_INVPHI, KK1, kk_neg(KK_INVPHI)),
      "FratK == [[invPhi, invPhi], [1, -invPhi]] over KK (FratK_entries)")
check("P9.FratK_ne_Fsymm", not matEq(RingKK, FratK, Fsymm),
      "FratK != Fsymm (FratK_ne_Fsymm) — the two gauges genuinely differ")
# both satisfy EVERY live pentagon instance over the same exact ring KK
viol_symm = countPentViolations(RingKK, Fsymm)
viol_ratK = countPentViolations(RingKK, FratK)
check("P9.both_solve_all_live", viol_symm == 0 and viol_ratK == 0,
      f"violations: Fsymm={viol_symm}, FratK={viol_ratK} over all 50 live "
      "instances (pentagon_symmetric_gauge, pentagon_FratK)")
q_symm, r_symm = Fsymm[(ONE, TAU)], Fsymm[(TAU, ONE)]
q_rat,  r_rat  = FratK[(ONE, TAU)], FratK[(TAU, ONE)]
check("P9.qr_pairs_differ", q_symm != q_rat and r_symm != r_rat,
      "(q,r)_symm = (b,b) != (invPhi,1) = (q,r)_rat")
check("P9.q_ne_r_witness", q_rat != r_rat and q_symm == r_symm,
      "FratK has q != r while solving the pentagon => q = r is NOT forced")
check("P9.products_equal",
      kk_mul(q_symm, r_symm) == kk_mul(q_rat, r_rat) == KK_INVPHI,
      "q*r == invPhi in BOTH gauges (the gauge invariant)")
# lambda with q_rat = lambda*q_symm, r_rat = (1/lambda)*r_symm
lam = kk_mul(q_rat, KT)          # q_symm = b is a unit, b^-1 = t
check("P9.lambda_solves_q", kk_mul(lam, q_symm) == q_rat,
      "lambda*q_symm == q_rat with lambda := q_rat * b^-1 = invPhi*t")
lam_inv = KT
check("P9.lambda_inverse", kk_mul(lam, lam_inv) == KK1,
      "lambda * t == 1, so lambda^-1 = t")
check("P9.lambda_solves_r", kk_mul(lam_inv, r_symm) == r_rat,
      "(1/lambda)*r_symm = t*b == 1 == r_rat")
check("P9.lambda_is_b", lam == KB == (Z5_0, Z5_INVPHI),
      f"lambda == b == (0, invPhi) in KK, i.e. x=0, y=(-1,0,-1,-1): "
      "lambda = t*invPhi = t/phi = 1/sqrt(phi) = t^-1")
check("P9.lambda_sq", kk_mul(lam, lam) == KK_INVPHI,
      "lambda^2 == invPhi (= b^2), consistent with qr preserved")
# uniqueness of lambda: q_symm = b is a unit, so the solution is unique
check("P9.lambda_unique",
      all(not (kk_mul((xv, yv), q_symm) == q_rat and (xv, yv) != lam)
          for xv in [Z5_0, Z5_1, Z5_INVPHI, Z5_PHI]
          for yv in [Z5_0, Z5_1, Z5_INVPHI, Z5_PHI]) and
      kk_mul(kk_mul(KT, q_rat), q_symm) == q_rat and lam == kk_mul(KT, q_rat),
      "b a unit => lambda unique; spot-scan of 16 candidates finds only b")
# negative control: the task convention with lambda = t FAILS
check("P9.negctrl_t_wrong_direction", kk_mul(KT, q_symm) != q_rat,
      "t*q_symm = t*b = 1 != invPhi = q_rat: lambda = t is the WRONG element "
      "for the symm->rat direction")
# ...but t connects rat->symm, which is PROOFS.md C5's reading
check("P9.proofsmd_t_reversed",
      kk_mul(KT, q_rat) == q_symm and kk_mul(KB, r_rat) == r_symm,
      "t*q_rat == q_symm and t^-1*r_rat == r_symm: PROOFS.md C5's 'lambda = t "
      "connects them' is exact for the rat->symm direction (inverse of task's)")
# the file's own vertex gauge diag(1,t): gauge_relation, all four entries
lamV = {ONE: KK1, TAU: KT}; lamVinv = {ONE: KK1, TAU: KB}
gauge_ok = all(kk_mul(lamV[x], Fsymm[(x, y)]) == kk_mul(FratK[(x, y)], lamV[y])
               for x in LABELS for y in LABELS)
check("P9.gauge_relation_diag_1_t", gauge_ok,
      "lam_x*Fsymm(x,y) == FratK(x,y)*lam_y for lam=diag(1,t), all 4 entries "
      "(gauge_relation)")
def gaugeFails(l):
    return sum(0 if kk_mul(l[x], Fsymm[(x, y)]) == kk_mul(FratK[(x, y)], l[y])
               else 1 for x in LABELS for y in LABELS)
gf = (gaugeFails(lamV), gaugeFails({ONE: KK1, TAU: KK1}),
      gaugeFails({ONE: KT, TAU: KK1}), gaugeFails({ONE: KK1, TAU: KK_INVPHI}))
check("P9.gaugeFails_counts", gf == (0, 2, 2, 2),
      f"gaugeFails(diag(1,t), trivial, diag(t,1), diag(1,invPhi)) = {gf} "
      "(gauge_clean=0, trivial_gauge_fails=2, sketch_gauge_fails=2, "
      "nonunit_gauge_fails=2)")
ratio = {(ONE,ONE): KK1, (ONE,TAU): KB, (TAU,ONE): KT, (TAU,TAU): KK1}
check("P9.ratio_table",
      all(FratK[(x,y)] == kk_mul(ratio[(x,y)], Fsymm[(x,y)])
          for x in LABELS for y in LABELS) and
      all(kk_mul(ratio[(x,y)], lamV[y]) == lamV[x] for x in LABELS for y in LABELS),
      "FratK = [[1,b],[t,1]] .* Fsymm and ratio(x,y)*lam_y == lam_x "
      "(gauge_ratio_table, gauge_ratio_is_lambda_quotient)")

# =====================================================================
# P10. declarations exist; sufficiency declared as gap, not claimed
# =====================================================================
src = open(LEAN).read()
proofs = open(PROOFS).read()
decls = {
 "pentagon_forces_golden":  r"theorem pentagon_forces_golden \(p q r s : KK\)",
 "resid_09_of_forced":      r"theorem resid_09_of_forced \(p q r s : KK\)",
 "strict_is_Fg_and_fails":  r"theorem strict_is_Fg_and_fails :",
 "wrong_is_Fg_and_fails":   r"theorem wrong_is_Fg_and_fails :",
 "pentagon_symmetric_gauge": r"theorem pentagon_symmetric_gauge :",
 "pentagon_rational_gauge": r"theorem pentagon_rational_gauge :",
 "Fg_symm":                 r"theorem Fg_symm : Fg KK\.invPhi KK\.b KK\.b \(KK\.neg KK\.invPhi\) = Fsymm",
 "Fg_id":                   r"theorem Fg_id : Fg KK\.one KK\.zero KK\.zero KK\.one = Fid",
 "Fg_wrong":                r"theorem Fg_wrong : Fg KK\.one KK\.one KK\.one \(KK\.neg KK\.one\) = Fwrong",
 "pentagon_live_instances_50": r"theorem pentagon_live_instances : countPentValid = 50 := rfl",
 "pentagon_nontrivial_instances_11":
     r"theorem pentagon_nontrivial_instances :\s*\n\s*countPentViolations PentPoly\.polyRng PentPoly\.FgP = 11 := rfl",
 "strict_pentagon_violations_4":
     r"theorem strict_pentagon_violations : countPentViolations kRng Fid = 4 := rfl",
 "wrong_pentagon_violations_5":
     r"theorem wrong_pentagon_violations : countPentViolations kRng Fwrong = 5 := rfl",
}
missing = [n for n, pat in decls.items() if not re.search(pat, src)]
check("P10.declarations_present", not missing,
      f"all {len(decls)} declarations found verbatim" +
      (f"; MISSING {missing}" if missing else ""))
# count-form statements of the two negative-control theorems
check("P10.negctrl_statements",
      "countPentViolations kRng (Fg KK.one KK.zero KK.zero KK.one) = 4" in src
      and "countPentViolations kRng (Fg KK.one KK.one KK.one (KK.neg KK.one)) = 5" in src,
      "strict_is_Fg_and_fails states =4 and wrong_is_Fg_and_fails states =5 via Fg")
# sufficiency: PROOFS.md declares the gap...
gap = ("Declared gap, pentagon side" in proofs
       and "sufficiency is NOT proved" in proofs
       and "What is missing is sufficiency for a generic" in proofs)
check("P10.gap_declared_in_ledger", gap,
      "PROOFS.md: 'Declared gap, pentagon side — sufficiency is NOT proved' "
      "+ 'converse ... not formalized' present")
# ...and Anyon.lean does not quietly claim it: every theorem whose conclusion
# is a universally quantified pentagonCheck over kRng is for a CONCRETE
# associator (Fsymm, FratK, Fg at golden constants), never generic p q r s
# under the three relations.
stmts = re.findall(r"theorem\s+(\w+)[^:]*?:\s*(.*?):=", src, re.S)
suspects = []
for name, body in stmts:
    if "pentagonCheck" in body and "∀" in body:
        # generic-sufficiency shape would quantify over instance labels with
        # Fg p q r s for VARIABLE p q r s in the conclusion
        concl = body.split("→")[-1]  # last arrow segment (the conclusion)
        if re.search(r"Fg p q r s", concl):
            suspects.append(name)
allow = {"pentagon_forces_golden", "pentagon_forces_p_unit"}  # Fg in HYPOTHESIS
quiet = [s for s in suspects if s not in allow]
# verify the two allowed ones have Fg p q r s only in the hypothesis h : ...
hyp_ok = all(
    re.search(rf"theorem {n} \(p q r s : KK\)\s*\n\s*\(h : ∀", src)
    for n in allow)
check("P10.no_quiet_sufficiency_claim", not quiet and hyp_ok,
      "no theorem concludes 'pentagonCheck ... (Fg p q r s) ... = true' for "
      "generic p q r s; Fg-generic pentagonCheck appears only as HYPOTHESIS of "
      "pentagon_forces_golden / pentagon_forces_p_unit"
      + (f"; SUSPECTS {quiet}" if quiet else ""))
check("P10.word_sufficiency_absent_in_sec7",
      "sufficien" not in src[src.index("## 7.  PENTAGON UNIQUENESS"):
                            src.index("## 8.  GALOIS")].lower(),
      "section 7 never uses the word 'sufficiency' — the file does not even "
      "informally claim the converse (ledger PROOFS.md carries the gap)")

# =====================================================================
# P11. co-sign with the floor: grammar_stone3.py
# =====================================================================
# (a) exact counterpart of the bench's sum-of-squared-residuals: for Fid and
# Fwrong all entries are 0, +-1, so every live residual lies in Z*1 c KK.
def sq_resid_sum(F):
    tot = KK0
    for tp in VALID:
        lhs, rhs = pent_sides(RingKK, F, *tp)
        d = kk_add(lhs, kk_neg(rhs))
        tot = kk_add(tot, kk_mul(d, d))
    return tot
check("P11.strict_sq_residual_4", sq_resid_sum(Fid) == emb((4, 0, 0, 0)),
      "exact sum of squared residuals for Fid == 4*1 in KK — the bench's "
      "float 4.0000 is this integer")
check("P11.wrong_sq_residual_5", sq_resid_sum(Fwrong) == emb((5, 0, 0, 0)),
      "exact sum of squared residuals for Fwrong == 5*1")
per_inst = []
for tp in sorted(fail_id, key=idx_of):
    lhs, rhs = pent_sides(RingKK, Fid, *tp)
    d = kk_add(lhs, kk_neg(rhs))
    per_inst.append(d == KK1 or d == kk_neg(KK1))
check("P11.strict_each_off_by_one", all(per_inst) and len(per_inst) == 4,
      "each of the 4 strict failures misses by exactly +-1 (file docstring: "
      "'four instances, each failing by exactly one, 4*1^2 = 4')")

# (b) the bench's SECOND cluster (Yang-Lee shadow: a=-phi, d=+phi, b*c=-phi)
# satisfies the three forced relations exactly, and an exact KK witness built
# from it passes ALL live instances: p := -phi, q := -phi, r := 1, s := +phi.
NEG_PHI = emb(z5_neg(Z5_PHI)); POS_PHI = emb(Z5_PHI)
yl_relations = (kk_mul(NEG_PHI, KK1) == NEG_PHI and                    # qr = p
                kk_add(kk_mul(NEG_PHI, NEG_PHI), NEG_PHI) == KK1 and   # p^2+p=1
                POS_PHI == kk_neg(NEG_PHI))                            # s = -p
FYL = Fg(NEG_PHI, NEG_PHI, KK1, POS_PHI)
yl_clean = countPentViolations(RingKK, FYL) == 0
check("P11.yang_lee_exact", yl_relations and yl_clean,
      "bench's non-unitary cluster (-phi, +phi, qr=-phi) satisfies the three "
      "forced relations EXACTLY and Fg(-phi,-phi,1,phi) has 0/50 violations "
      "in KK: pentagon_forces_golden pins p to A root of X^2+X-1, and both "
      "roots really occur (the declared which-root gap is real)")

# (c) run the bench itself and parse its printed numbers
import subprocess
bench = subprocess.run(
    [sys.executable, "/home/claude/workshop/grammar_stone3.py"],
    capture_output=True, text=True, timeout=560)
out = bench.stdout
check("P11.bench_exit_0", bench.returncode == 0,
      f"grammar_stone3.py exit code {bench.returncode} (assertions inside all held)")
check("P11.bench_strict_4", "pentagon residual 4.0000" in out,
      "bench prints strict residual 4.0000 == exact 4 above")
m = re.search(r"a=\+0\.618034\s+d=-0\.618034\s+b\*c=\+0\.618034\s+\[unitarizable\]", out)
check("P11.bench_golden_class", bool(m),
      "unitarizable class: a=1/phi, d=-1/phi, b*c=1/phi — exactly "
      "(p, s, qr) = (invPhi, -invPhi, invPhi), the forced relations")
m2 = re.search(r"a=-1\.618034\s+d=\+1\.618034\s+b\*c=-1\.618034\s+\[non-unitary", out)
check("P11.bench_yang_lee_class", bool(m2),
      "non-unitary class: a=-phi, d=+phi, b*c=-phi — the other root, "
      "matching P11.yang_lee_exact")
check("P11.bench_two_classes", "2 gauge classes" in out,
      "bench: found solutions fall into exactly 2 gauge classes "
      "(invariants a, d, b*c — same invariants as pentagon_forces_golden)")
check("P11.bench_golden_residual", "golden pentagon residual 5.5e-32" in out
      or re.search(r"golden pentagon residual \d\.\de-3\d", out) is not None,
      "bench: golden residual ~1e-32 (float shadow of the exact 0/50)")
check("P11.bench_qdim_phi", "= 1.618034 = phi" in out.replace("\n", " ")
      or "1.618034 = phi" in out,
      "bench: quantum dimension = phi (parked/not formalized in Lean, "
      "declared in PROOFS.md gaps table)")

print()
nfail = sum(1 for _, ok, _ in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  "
      f"({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
