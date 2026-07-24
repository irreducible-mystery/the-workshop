#!/usr/bin/env python3
"""r3_hexagon.py — round-3 adversarial audit, hexagon-uniqueness assembly of Anyon.lean.

Checks H0 (algebra handshake), H1..H12.  Exact integer arithmetic only; the one
float block is an explicitly non-load-bearing sanity cross-check.

Reimplemented FROM THE LEAN SOURCE (round-3 /home/claude/workshop/lean/Anyon.lean):

  Z5 (lines 240-277): 4-tuples (a0,a1,a2,a3) = a0 + a1*z + a2*z^2 + a3*z^3,
    mul = convolution c0..c6 then reduce with z^4 = -(1+z+z^2+z^3), z^5 = 1,
    z^6 = z:  (c0-c4+c5, c1-c4+c6, c2-c4, c3-c4).
    phi = (0,0,-1,-1);  invPhi = (-1,0,-1,-1).
  KK (lines 303-341): pairs (x,y) = x + y*t with t^2 = phi;
    mul = (x1x2 + phi*y1y2, x1y2 + y1x2).
    t=(0,1);  b = t*invPhi = (0, invPhi);  r1 = emb zeta2;  rt = emb (neg zeta);
    theta = emb zeta3;  mirror r1' = emb zeta3, rt' = emb (neg zeta4) = (1,1,1,1).
  hexagonValid (137-139): e in fuse(a,b) && d in fuse(e,c) && z in fuse(a,c)
    && d in fuse(z,b).  15 of 64 tuples pass.
  hexagonCheck (143-152):
    LHS = Rb(e,c,d) * Fs(c,a,b,d,z,e)
    RHS = sum_{g in fuse(b,c)} ((Fs(a,b,c,d,e,g)*Rb(b,c,g))*Fs(a,c,b,d,z,g))*Rb(a,c,z)
  RESIDUAL CONVENTION: residual := LHS - RHS (beq's first arg minus its second).

  INSTANCE-INDEXING CONVENTION (recovered from the file):
    tuples (a,b,c,d,e,z) are enumerated in the `sumB` nest order of
    `countHexViolations` (lines 502-505): a outermost ... z innermost, `.one`
    before `.tau` — lexicographic with one < tau.  Of the 15 guard-valid
    tuples, the 10 with a vacuum among (a,b,c) have identically-zero residual;
    the 5 live ones all sit at (a,b,c) = (tau,tau,tau) and are numbered #1..#5
    in that same enumeration order:
      #1 (tau,tau,tau, d=1,  e=tau, z=tau)   <- hex_at_r1, "residual #1"
      #2 (tau,tau,tau, d=tau,e=1,   z=1  )
      #3 (tau,tau,tau, d=tau,e=1,   z=tau)   <- hex_at_3,  "residual #3"
      #4 (tau,tau,tau, d=tau,e=tau, z=1  )
      #5 (tau,tau,tau, d=tau,e=tau, z=tau)   <- hex_at_5,  "residual #5"
    (Equivalently: valid instances 0-indexed 0..14 in nest order put the live
    five at 10..14; the e=1 pair #2,#3 are valid-instances 11,12 — the
    "instance 11 or 12" of the PROOFS.md auditor quote.)
    NOTE: the audit charge's H9 phrase "(tau,tau,tau; d=tau, z=1, e=tau)" uses
    swapped e/z NAMES relative to the file; the tuple it denotes is the file's
    #3 = (tau,tau,tau,tau, e=1, z=tau).  Both candidates are computed below and
    the identity picks out (#3,#5) uniquely — see H9.scan.
"""
import sys, re

LEAN = "/home/claude/workshop/lean/Anyon.lean"
PROOFS = "/home/claude/workshop/lean/PROOFS.md"

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok), detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ══════════════════════════════════════════════════════════════════════════
# Scalar-generic transcription of Z5 / KK (one transcription serves ints,
# symbolic Z-polynomials, and is evaluated nowhere else).
# ══════════════════════════════════════════════════════════════════════════
class SInt:                          # scalar ring: python ints
    zero = 0
    @staticmethod
    def of(c): return c
    add = staticmethod(lambda a, b: a + b)
    sub = staticmethod(lambda a, b: a - b)
    neg = staticmethod(lambda a: -a)
    mul = staticmethod(lambda a, b: a * b)

# sparse Z-polynomials: {sorted tuple of var ids: int}
class SPoly:
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

def z5_zero(S): return (S.zero,) * 4
def z5_of(S, t): return tuple(S.of(c) for c in t)
def z5_add(S, u, v): return tuple(S.add(a, b) for a, b in zip(u, v))
def z5_neg(S, u): return tuple(S.neg(a) for a in u)
def z5_mul(S, u, v):
    # verbatim Anyon.lean lines 256-264
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

def kk_zero(S): return (z5_zero(S), z5_zero(S))
def kk_of(S, u): return (z5_of(S, u[0]), z5_of(S, u[1]))
def kk_add(S, u, v): return (z5_add(S, u[0], v[0]), z5_add(S, u[1], v[1]))
def kk_neg(S, u): return (z5_neg(S, u[0]), z5_neg(S, u[1]))
def kk_sub(S, u, v): return kk_add(S, u, kk_neg(S, v))
def kk_mul(S, u, v):
    # verbatim Anyon.lean lines 324-326: (x1x2 + phi*(y1y2), x1y2 + y1x2)
    phiS = z5_of(S, (0, 0, -1, -1))
    return (z5_add(S, z5_mul(S, u[0], v[0]), z5_mul(S, phiS, z5_mul(S, u[1], v[1]))),
            z5_add(S, z5_mul(S, u[0], v[1]), z5_mul(S, u[1], v[0])))

# ---- concrete (int) constants, all built through the one transcription ----
I = SInt
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
def km(u, v): return kk_mul(I, u, v)
def ka(u, v): return kk_add(I, u, v)
def kn(u): return kk_neg(I, u)
def ks(u, v): return kk_sub(I, u, v)
K_INVPHI = emb(INVPHI5)
K_PHI    = emb(PHI5)
K_B      = km(K_T, K_INVPHI)          # def b := mul t invPhi
K_R1     = emb(ZETA2)                 # r1 = zeta^2
K_RT     = emb(z5n(ZETA))             # rt = -zeta
K_THETA  = emb(ZETA3)
K_R1P    = emb(ZETA3)                 # mirror r1' = zeta^3
K_RTP    = emb(z5n(ZETA4))            # mirror rt' = -zeta^4 -> (1,1,1,1)

# unit test: determinant of multiplication-by-u on the Z-basis
# (z^i, 0), (0, z^i), i = 0..3  — exact Bareiss.
BASIS = [emb(ZETA), emb(ZETA2), emb(ZETA3)]
BASIS = [K_ONE] + BASIS + [K_T] + [km(K_T, emb(z))
                                   for z in (ZETA, ZETA2, ZETA3)]
def kk_coords(u): return list(u[0]) + list(u[1])
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
def kk_norm(u):
    cols = [kk_coords(km(u, e)) for e in BASIS]
    return det_int([[cols[j][i] for j in range(8)] for i in range(8)])
def is_unit(u): return kk_norm(u) in (1, -1)

# ══════════════════════════════════════════════════════════════════════════
# H0 — algebra handshake: the charge's ALGEBRA block matches the Lean source
# ══════════════════════════════════════════════════════════════════════════
check("H0.zeta4", z5m(ZETA3, ZETA) == ZETA4, "zeta^3*zeta == (-1,-1,-1,-1)")
check("H0.zeta5", z5m(ZETA4, ZETA) == Z5_ONE, "zeta^5 == 1")
check("H0.phi_def", z5a(z5a(Z5_ONE, ZETA), ZETA4) == PHI5, "1+z+z^4 == (0,0,-1,-1)")
check("H0.invPhi_def", z5a(ZETA, ZETA4) == INVPHI5, "z+z^4 == (-1,0,-1,-1)")
check("H0.phi_invPhi", z5m(PHI5, INVPHI5) == Z5_ONE, "phi*invPhi == 1 in Z5")
check("H0.t_sq", km(K_T, K_T) == K_PHI, "t^2 == emb phi")
check("H0.b_tuple", K_B == (Z5_ZERO, INVPHI5), "b = t*invPhi == (0, invPhi)")
check("H0.b_sq", km(K_B, K_B) == K_INVPHI, "b^2 == invPhi")
check("H0.t_mul_b", km(K_T, K_B) == K_ONE and km(K_B, K_T) == K_ONE,
      "t*b == 1 == b*t")
check("H0.rt_prime", K_RTP == ((1, 1, 1, 1), Z5_ZERO), "-zeta^4 reduces to (1,1,1,1)")

LEAN_TXT = open(LEAN, encoding="utf-8").read()
NORM = re.sub(r"\s+", " ", LEAN_TXT)
def in_file(s): return re.sub(r"\s+", " ", s) in NORM

# ══════════════════════════════════════════════════════════════════════════
# H1 — ring layer: presence (grep of the exact Lean statement) + symbolic proof
# ══════════════════════════════════════════════════════════════════════════
# fresh indeterminates per coordinate: u,v,w at Z5 level use vars 0-3,4-7,8-11;
# at KK level 0-7, 8-15, 16-23.
P = SPoly
def z5_sym(k): return tuple(P.var(4 * k + i) for i in range(4))
def kk_sym(k): return (tuple(P.var(8 * k + i) for i in range(4)),
                       tuple(P.var(8 * k + 4 + i) for i in range(4)))
Z5_LAWS = {
    "add_comm":      ("theorem add_comm (u v : Z5) : add u v = add v u",
                      lambda u, v, w: z5_add(P, u, v) == z5_add(P, v, u)),
    "add_assoc":     ("theorem add_assoc (u v w : Z5) : add (add u v) w = add u (add v w)",
                      lambda u, v, w: z5_add(P, z5_add(P, u, v), w) == z5_add(P, u, z5_add(P, v, w))),
    "add_mul":       ("theorem add_mul (u v w : Z5) : mul (add u v) w = add (mul u w) (mul v w)",
                      lambda u, v, w: z5_mul(P, z5_add(P, u, v), w) == z5_add(P, z5_mul(P, u, w), z5_mul(P, v, w))),
    "mul_left_comm": ("theorem mul_left_comm (u v w : Z5) : mul u (mul v w) = mul v (mul u w)",
                      lambda u, v, w: z5_mul(P, u, z5_mul(P, v, w)) == z5_mul(P, v, z5_mul(P, u, w))),
    "mul_right_comm":("theorem mul_right_comm (u v w : Z5) : mul (mul u v) w = mul (mul u w) v",
                      lambda u, v, w: z5_mul(P, z5_mul(P, u, v), w) == z5_mul(P, z5_mul(P, u, w), v)),
    "add_left_comm": ("theorem add_left_comm (u v w : Z5) : add u (add v w) = add v (add u w)",
                      lambda u, v, w: z5_add(P, u, z5_add(P, v, w)) == z5_add(P, v, z5_add(P, u, w))),
    "neg_mul":       ("theorem neg_mul (u v : Z5) : mul (neg u) v = neg (mul u v)",
                      lambda u, v, w: z5_mul(P, z5_neg(P, u), v) == z5_neg(P, z5_mul(P, u, v))),
    "mul_neg":       ("theorem mul_neg (u v : Z5) : mul u (neg v) = neg (mul u v)",
                      lambda u, v, w: z5_mul(P, u, z5_neg(P, v)) == z5_neg(P, z5_mul(P, u, v))),
    "neg_neg":       ("theorem neg_neg (u : Z5) : neg (neg u) = u",
                      lambda u, v, w: z5_neg(P, z5_neg(P, u)) == u),
    "add_neg":       ("theorem add_neg (u : Z5) : add u (neg u) = zero",
                      lambda u, v, w: z5_add(P, u, z5_neg(P, u)) == z5_zero(P)),
    "neg_add_cancel":("theorem neg_add_cancel (u : Z5) : add (neg u) u = zero",
                      lambda u, v, w: z5_add(P, z5_neg(P, u), u) == z5_zero(P)),
    "neg_add":       ("theorem neg_add (u v : Z5) : neg (add u v) = add (neg u) (neg v)",
                      lambda u, v, w: z5_neg(P, z5_add(P, u, v)) == z5_add(P, z5_neg(P, u), z5_neg(P, v))),
    # supporting (pre-round-3) laws the assembly also leans on:
    "mul_comm":      ("theorem mul_comm (u v : Z5) : mul u v = mul v u",
                      lambda u, v, w: z5_mul(P, u, v) == z5_mul(P, v, u)),
    "mul_assoc":     ("theorem mul_assoc (u v w : Z5) : mul (mul u v) w = mul u (mul v w)",
                      lambda u, v, w: z5_mul(P, z5_mul(P, u, v), w) == z5_mul(P, u, z5_mul(P, v, w))),
    "mul_add":       ("theorem mul_add (u v w : Z5) : mul u (add v w) = add (mul u v) (mul u w)",
                      lambda u, v, w: z5_mul(P, u, z5_add(P, v, w)) == z5_add(P, z5_mul(P, u, v), z5_mul(P, u, w))),
}
KK_LAWS = {
    "add_comm":      ("theorem add_comm (u v : KK) : add u v = add v u",
                      lambda u, v, w: kk_add(P, u, v) == kk_add(P, v, u)),
    "add_assoc":     ("theorem add_assoc (u v w : KK) : add (add u v) w = add u (add v w)",
                      lambda u, v, w: kk_add(P, kk_add(P, u, v), w) == kk_add(P, u, kk_add(P, v, w))),
    "add_mul":       ("theorem add_mul (u v w : KK) : mul (add u v) w = add (mul u w) (mul v w)",
                      lambda u, v, w: kk_mul(P, kk_add(P, u, v), w) == kk_add(P, kk_mul(P, u, w), kk_mul(P, v, w))),
    "mul_left_comm": ("theorem mul_left_comm (u v w : KK) : mul u (mul v w) = mul v (mul u w)",
                      lambda u, v, w: kk_mul(P, u, kk_mul(P, v, w)) == kk_mul(P, v, kk_mul(P, u, w))),
    "mul_right_comm":("theorem mul_right_comm (u v w : KK) : mul (mul u v) w = mul (mul u w) v",
                      lambda u, v, w: kk_mul(P, kk_mul(P, u, v), w) == kk_mul(P, kk_mul(P, u, w), v)),
    "add_left_comm": ("theorem add_left_comm (u v w : KK) : add u (add v w) = add v (add u w)",
                      lambda u, v, w: kk_add(P, u, kk_add(P, v, w)) == kk_add(P, v, kk_add(P, u, w))),
    "neg_mul":       ("theorem neg_mul (u v : KK) : mul (neg u) v = neg (mul u v)",
                      lambda u, v, w: kk_mul(P, kk_neg(P, u), v) == kk_neg(P, kk_mul(P, u, v))),
    "mul_neg":       ("theorem mul_neg (u v : KK) : mul u (neg v) = neg (mul u v)",
                      lambda u, v, w: kk_mul(P, u, kk_neg(P, v)) == kk_neg(P, kk_mul(P, u, v))),
    "neg_neg":       ("theorem neg_neg (u : KK) : neg (neg u) = u",
                      lambda u, v, w: kk_neg(P, kk_neg(P, u)) == u),
    "add_neg":       ("theorem add_neg (u : KK) : add u (neg u) = zero",
                      lambda u, v, w: kk_add(P, u, kk_neg(P, u)) == kk_zero(P)),
    "neg_add_cancel":("theorem neg_add_cancel (u : KK) : add (neg u) u = zero",
                      lambda u, v, w: kk_add(P, kk_neg(P, u), u) == kk_zero(P)),
    "neg_add":       ("theorem neg_add (u v : KK) : neg (add u v) = add (neg u) (neg v)",
                      lambda u, v, w: kk_neg(P, kk_add(P, u, v)) == kk_add(P, kk_neg(P, u), kk_neg(P, v))),
    "mul_comm":      ("theorem mul_comm (u v : KK) : mul u v = mul v u",
                      lambda u, v, w: kk_mul(P, u, v) == kk_mul(P, v, u)),
    "mul_assoc":     ("theorem mul_assoc (u v w : KK) : mul (mul u v) w = mul u (mul v w)",
                      lambda u, v, w: kk_mul(P, kk_mul(P, u, v), w) == kk_mul(P, u, kk_mul(P, v, w))),
    "mul_add":       ("theorem mul_add (u v w : KK) : mul u (add v w) = add (mul u v) (mul u w)",
                      lambda u, v, w: kk_mul(P, u, kk_add(P, v, w)) == kk_add(P, kk_mul(P, u, v), kk_mul(P, u, w))),
}
EXPECT_ABSENT = {("Z5", "mul_right_comm"), ("KK", "neg_add")}
uZ, vZ, wZ = z5_sym(0), z5_sym(1), z5_sym(2)
uK, vK, wK = kk_sym(0), kk_sym(1), kk_sym(2)
presence = {}
all_sym_ok = True
for lvl, laws, (u_, v_, w_) in (("Z5", Z5_LAWS, (uZ, vZ, wZ)),
                                ("KK", KK_LAWS, (uK, vK, wK))):
    for name, (stmt, fn) in laws.items():
        present = in_file(stmt)
        holds = fn(u_, v_, w_)
        presence[(lvl, name)] = present
        if not holds: all_sym_ok = False
        tag = "present" if present else "ABSENT-from-file"
        check(f"H1.{lvl}.{name}", holds and (present or (lvl, name) in EXPECT_ABSENT),
              f"{tag}; symbolic identity {'holds' if holds else 'FAILS'} "
              f"(fresh indeterminates per coordinate)")
absent = sorted(k for k, p in presence.items() if not p)
check("H1.presence_table", set(absent) == EXPECT_ABSENT,
      f"absent from file: {absent} — exactly Z5.mul_right_comm and KK.neg_add "
      "(PROOFS.md C2' claims both levels: ledger overclaim)")
# negative controls: bogus laws must FAIL symbolically
check("H1.negctrl_bogus1",
      not (z5_mul(P, z5_neg(P, uZ), vZ) == z5_mul(P, uZ, vZ)),
      "mul (neg u) v == mul u v correctly REJECTED at Z5 level")
check("H1.negctrl_bogus2",
      not (kk_add(P, uK, kk_neg(P, vK)) == kk_zero(P)),
      "add u (neg v) == zero correctly REJECTED at KK level")
def z5_mul_broken(S, u, v):    # z^4 := +(1+z+z^2+z^3), c5/c6 rules kept
    a0, a1, a2, a3 = u; b0, b1, b2, b3 = v
    c0 = S.mul(a0, b0)
    c1 = S.add(S.mul(a0, b1), S.mul(a1, b0))
    c2 = S.add(S.add(S.mul(a0, b2), S.mul(a1, b1)), S.mul(a2, b0))
    c3 = S.add(S.add(S.add(S.mul(a0, b3), S.mul(a1, b2)), S.mul(a2, b1)), S.mul(a3, b0))
    c4 = S.add(S.add(S.mul(a1, b3), S.mul(a2, b2)), S.mul(a3, b1))
    c5 = S.add(S.mul(a2, b3), S.mul(a3, b2))
    c6 = S.mul(a3, b3)
    return (S.add(S.add(c0, c4), c5), S.add(S.add(c1, c4), c6),
            S.add(c2, c4), S.add(c3, c4))
check("H1.negctrl_broken_reduction",
      not (z5_mul_broken(P, z5_mul_broken(P, uZ, vZ), wZ)
           == z5_mul_broken(P, uZ, z5_mul_broken(P, vZ, wZ))),
      "flipping the z^4 reduction sign breaks mul_assoc symbolically "
      "(the reduction rules are load-bearing)")

# ══════════════════════════════════════════════════════════════════════════
# H2 — bphi_is_t
# ══════════════════════════════════════════════════════════════════════════
check("H2.bphi_is_t", km(K_B, K_PHI) == K_T, "b * emb(phi) == t exactly in KK")
check("H2.stmt", in_file("theorem bphi_is_t : KK.mul KK.b (KK.emb Z5.phi) = KK.t := rfl"),
      "Lean statement is verbatim b*phi = t, proof rfl")
check("H2.negctrl", km(K_B, K_INVPHI) != K_T and km(K_T, K_PHI) != K_T,
      "b*invPhi != t and t*phi != t (phi != 1)")

# ══════════════════════════════════════════════════════════════════════════
# The coherence machinery over an arbitrary ring record, verbatim transcription
# ══════════════════════════════════════════════════════════════════════════
ONE_, TAU_ = 0, 1
LABELS = (ONE_, TAU_)                     # .one before .tau == sumB order
def fuse(a, b):
    if a == ONE_: return (b,)
    if b == ONE_: return (a,)
    return (ONE_, TAU_)
def memA(x, l): return x in l
def isOne(a): return a == ONE_
def hexagonValid(a, b, c, d, e, z):
    return (memA(e, fuse(a, b)) and memA(d, fuse(e, c)) and
            memA(z, fuse(a, c)) and memA(d, fuse(z, b)))
def Fs(R, F, a, b, c, d, x, y):
    if memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and \
       memA(y, fuse(b, c)) and memA(d, fuse(a, y)):
        if isOne(a) or isOne(b) or isOne(c): return R["one"]
        if isOne(d):
            return R["one"] if (not isOne(x)) and (not isOne(y)) else R["zero"]
        return F[(x, y)]
    return R["zero"]
def Rb(R, r1v, rtv, x, y, c):
    if isOne(x) or isOne(y): return R["one"]
    if isOne(c): return r1v
    return rtv
def sumOver(R, f, l):
    if not l: return R["zero"]
    return R["add"](f(l[0]), sumOver(R, f, l[1:]))
def hex_sides(R, F, r1v, rtv, a, b, c, d, e, z):
    lhs = R["mul"](Rb(R, r1v, rtv, e, c, d), Fs(R, F, c, a, b, d, z, e))
    rhs = sumOver(R, lambda g:
                  R["mul"](R["mul"](R["mul"](Fs(R, F, a, b, c, d, e, g),
                                             Rb(R, r1v, rtv, b, c, g)),
                                    Fs(R, F, a, c, b, d, z, g)),
                           Rb(R, r1v, rtv, a, c, z)), fuse(b, c))
    return lhs, rhs
def hex_sides_charge(R, F, r1v, rtv, a, b, c, d, e, z):
    # the WRONG (charge) ordering: Fs(..., d, e, z) on the LHS — negative control
    lhs = R["mul"](Rb(R, r1v, rtv, e, c, d), Fs(R, F, c, a, b, d, e, z))
    _, rhs = hex_sides(R, F, r1v, rtv, a, b, c, d, e, z)
    return lhs, rhs

# --- ring 1: plain KK (for boolean checks at constant braidings) ---
RK = dict(zero=K_ZERO, one=K_ONE, add=ka, mul=km)
FsymmK = {(ONE_, ONE_): K_INVPHI, (ONE_, TAU_): K_B,
          (TAU_, ONE_): K_B, (TAU_, TAU_): kn(K_INVPHI)}
def hex_check(r1v, rtv, tup, charge=False):
    if not hexagonValid(*tup): return True
    l, r = (hex_sides_charge if charge else hex_sides)(RK, FsymmK, r1v, rtv, *tup)
    return l == r
def viol_count(r1v, rtv, charge=False):
    return sum(0 if hex_check(r1v, rtv, tup, charge) else 1 for tup in ALL64)

# --- ring 2: K[R1,RT], sparse dict {(i,j): KK coeff} ---
def kp_norm(p): return {m: c for m, c in p.items() if c != K_ZERO}
KP_ZERO = {}
def kp_const(c): return kp_norm({(0, 0): c})
KP_ONE = kp_const(K_ONE)
PR1 = {(1, 0): K_ONE}; PRT = {(0, 1): K_ONE}
def kp_add(p, q):
    w = dict(p)
    for m, c in q.items():
        t = ka(w.get(m, K_ZERO), c)
        if t != K_ZERO: w[m] = t
        else: w.pop(m, None)
    return w
def kp_neg(p): return {m: kn(c) for m, c in p.items()}
def kp_sub(p, q): return kp_add(p, kp_neg(q))
def kp_mul(p, q):
    w = {}
    for (i1, j1), c1 in p.items():
        for (i2, j2), c2 in q.items():
            m = (i1 + i2, j1 + j2)
            t = ka(w.get(m, K_ZERO), km(c1, c2))
            if t != K_ZERO: w[m] = t
            else: w.pop(m, None)
    return w
def kp_eval(p, r1v, rtv):
    acc = K_ZERO
    for (i, j), c in p.items():
        term = c
        for _ in range(i): term = km(term, r1v)
        for _ in range(j): term = km(term, rtv)
        acc = ka(acc, term)
    return acc
RP = dict(zero=KP_ZERO, one=KP_ONE, add=kp_add, mul=kp_mul)
FsymmP = {k: kp_const(v) for k, v in FsymmK.items()}

from itertools import product as iproduct
ALL64 = [t for t in iproduct(LABELS, repeat=6)]      # nest order (a,b,c,d,e,z)
VALID = [t for t in ALL64 if hexagonValid(*t)]
INVALID = [t for t in ALL64 if not hexagonValid(*t)]

SIDES = {}; RES = {}
for tup in VALID:
    l, r = hex_sides(RP, FsymmP, PR1, PRT, *tup)
    SIDES[tup] = (l, r); RES[tup] = kp_sub(l, r)

# ══════════════════════════════════════════════════════════════════════════
# H3 — live/trivial split + instance indexing
# ══════════════════════════════════════════════════════════════════════════
check("H3.total", len(ALL64) == 64, "64 tuples")
check("H3.valid_15", len(VALID) == 15, f"guard-valid = {len(VALID)}")
check("H3.nest_guard", len(VALID) + len(INVALID) == 64,
      f"{len(VALID)}+{len(INVALID)}=64")
zero_res = [t for t in VALID if not RES[t]]
live_res = [t for t in VALID if RES[t]]
vacuum = [t for t in VALID if isOne(t[0]) or isOne(t[1]) or isOne(t[2])]
alltau = [t for t in VALID if t[:3] == (TAU_, TAU_, TAU_)]
check("H3.zero_iff_vacuum", set(zero_res) == set(vacuum),
      f"identically-zero residuals == tuples with a vacuum among (a,b,c): "
      f"{len(zero_res)} of them")
check("H3.live_iff_alltau", set(live_res) == set(alltau),
      f"nonzero residuals == the (tau,tau,tau) tuples: {len(live_res)}")
check("H3.split_10_5", len(zero_res) == 10 and len(live_res) == 5,
      "10 trivial + 5 live")
check("H3.nest_split", len(zero_res) + len(live_res) == 15, "10+5=15")
T, O = TAU_, ONE_
FILE5 = [(T, T, T, O, T, T), (T, T, T, T, O, O), (T, T, T, T, O, T),
         (T, T, T, T, T, O), (T, T, T, T, T, T)]
check("H3.indexing", live_res == FILE5,
      "nest-order live tuples == #1..#5 as documented (hex_at_r1=#1, "
      "hex_at_3=#3, hex_at_5=#5)")
R = {i + 1: RES[t] for i, t in enumerate(FILE5)}
S = {i + 1: SIDES[t] for i, t in enumerate(FILE5)}
check("H3.file_names_1_3_5",
      in_file("hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .one .tau .tau") and
      in_file("hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .tau .one .tau") and
      in_file("hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .tau .tau .tau"),
      "hex_at_r1/hex_at_3/hex_at_5 read exactly tuples #1/#3/#5")
check("H3.valid_positions", [VALID.index(t) for t in FILE5] == [10, 11, 12, 13, 14],
      "live five are valid-instances 10..14 (0-indexed) — e=1 pair at 11,12")
# semantic check of the three extraction theorems' displayed sides
def C(x): return kp_const(x)
disp1 = (kp_mul(PR1, C(K_ONE)),
         kp_add(kp_mul(kp_mul(kp_mul(C(K_ZERO), PR1), C(K_ZERO)), PRT),
                kp_add(kp_mul(kp_mul(kp_mul(C(K_ONE), PRT), C(K_ONE)), PRT),
                       KP_ZERO)))
disp3 = (kp_mul(C(K_ONE), C(K_B)),
         kp_add(kp_mul(kp_mul(kp_mul(C(K_INVPHI), PR1), C(K_B)), PRT),
                kp_add(kp_mul(kp_mul(kp_mul(C(K_B), PRT), C(kn(K_INVPHI))), PRT),
                       KP_ZERO)))
disp5 = (kp_mul(PRT, C(kn(K_INVPHI))),
         kp_add(kp_mul(kp_mul(kp_mul(C(K_B), PR1), C(K_B)), PRT),
                kp_add(kp_mul(kp_mul(kp_mul(C(kn(K_INVPHI)), PRT),
                                     C(kn(K_INVPHI))), PRT), KP_ZERO)))
check("H3.hex_at_r1_semantics", S[1] == disp1,
      "machinery sides at #1 == hex_at_r1's displayed beq args, as polynomials")
check("H3.hex_at_3_semantics", S[3] == disp3,
      "machinery sides at #3 == hex_at_3's displayed beq args")
check("H3.hex_at_5_semantics", S[5] == disp5,
      "machinery sides at #5 == hex_at_5's displayed beq args")
# negative controls for the machinery itself
def brokenValid(a, b, c, d, e, z):
    return (memA(e, fuse(a, b)) and memA(d, fuse(e, c)) and memA(z, fuse(a, c)))
nbroke = sum(1 for t in ALL64 if brokenValid(*t))
check("H3.negctrl_guard", nbroke != 15,
      f"guard minus last conjunct -> {nbroke} valid (not 15): guard-sensitive")
check("H3.negctrl_charge_order", viol_count(K_R1, K_RT, charge=True) == 4,
      "charge-ordered LHS (Fs ... d e z) fails 4/15 at golden — matches "
      "charge_hexagon_order_fails; my transcription would catch an index swap")
check("H3.golden_zero_viols", viol_count(K_R1, K_RT) == 0,
      "bench ordering, golden constants: 0 violations (chirality_right)")
# tie the two instruments: beq result == (residual evaluates to zero)
tie = all((hex_check(rv[0], rv[1], t)) == (kp_eval(RES[t], rv[0], rv[1]) == K_ZERO)
          for rv in ((K_R1, K_RT), (K_R1P, K_RTP), (K_ZERO, K_ZERO), (K_ONE, K_ONE))
          for t in VALID)
check("H3.instruments_agree", tie,
      "boolean hexagonCheck == (residual == 0) for 4 braidings x 15 instances")

# ══════════════════════════════════════════════════════════════════════════
# H4 — exactly one live residual is a unit multiple of (R1 - RT^2)
# ══════════════════════════════════════════════════════════════════════════
R1_minus_RT2 = kp_sub(PR1, kp_mul(PRT, PRT))
def unit_multiple_of_target(p):
    if set(p.keys()) != {(1, 0), (0, 2)}: return None
    u = p[(1, 0)]
    if p == kp_mul(kp_const(u), R1_minus_RT2) and is_unit(u): return u
    return None
hits = {i: unit_multiple_of_target(R[i]) for i in range(1, 6)}
found = {i: u for i, u in hits.items() if u is not None}
check("H4.exactly_one", list(found.keys()) == [1],
      f"unit-multiple-of-(R1-RT^2) residuals: instances {sorted(found)} (only #1)")
check("H4.unit_is_plus_one", found.get(1) == K_ONE,
      "the unit is +1: residual #1 IS R1 - RT^2 verbatim")
check("H4.res1_verbatim", R[1] == R1_minus_RT2, "R[1] == R1 - RT^2 as kp dicts")
check("H4.norm_one", kk_norm(K_ONE) == 1, "norm(+1) = 1")
check("H4.negctrl_norms", kk_norm(emb((2, 0, 0, 0))) == 256 and
      not is_unit(emb((2, 0, 0, 0))) and is_unit(emb(ZETA)) and is_unit(K_B),
      "norm(2)=256 (not a unit); zeta and b are units — the unit test has teeth")
others_form = [i for i in range(2, 6)
               if set(R[i].keys()) == {(1, 0), (0, 2)}]
check("H4.no_other_support", others_form == [],
      "no other live residual even has monomial support {R1, RT^2}; "
      "10 trivial residuals are 0 (not unit multiples)")

# ══════════════════════════════════════════════════════════════════════════
# H5 — (LHS3-RHS3)*(b*phi) == -((invPhi*RT*(R1-RT)) - 1)
# ══════════════════════════════════════════════════════════════════════════
BPHI = km(K_B, K_PHI)                     # == t by H2
lhs5c = kp_mul(R[3], kp_const(BPHI))
target5 = kp_neg(kp_sub(kp_mul(kp_mul(kp_const(K_INVPHI), PRT),
                               kp_sub(PR1, PRT)), KP_ONE))
check("H5.identity", lhs5c == target5,
      "(LHS3-RHS3)*(b*phi) == -((invPhi*RT*(R1-RT)) - 1) exactly in K[R1,RT]")
W = kp_mul(kp_const(K_INVPHI), kp_sub(PR1, PRT))       # invPhi*(R1-RT)
check("H5.unit_conclusion",
      kp_sub(kp_mul(W, PRT), KP_ONE) == kp_neg(kp_mul(kp_const(K_T), R[3])),
      "(invPhi*(R1-RT))*RT - 1 == -t*Res3: Res3=0 forces RT a unit with "
      "exhibited inverse invPhi*(R1-RT)")
check("H5.negctrl_wrong_mult", kp_mul(R[3], kp_const(K_PHI)) != target5,
      "multiplying Res3 by phi instead of b*phi does NOT give the target")

# ══════════════════════════════════════════════════════════════════════════
# H6 — (LHS5-RHS5)*phi == -(RT*(R1 + invPhi*RT + 1))
# ══════════════════════════════════════════════════════════════════════════
L_lin = kp_add(kp_add(PR1, kp_mul(kp_const(K_INVPHI), PRT)), KP_ONE)
target6 = kp_neg(kp_mul(PRT, L_lin))
check("H6.identity", kp_mul(R[5], kp_const(K_PHI)) == target6,
      "(LHS5-RHS5)*phi == -(RT*(R1 + invPhi*RT + 1)) exactly")
check("H6.negctrl_wrong_mult", kp_mul(R[5], kp_const(BPHI)) != target6,
      "multiplying Res5 by b*phi does NOT give the target")

# ══════════════════════════════════════════════════════════════════════════
# H7 — the chain, hypotheses read from the file, every step an exact identity
# ══════════════════════════════════════════════════════════════════════════
e3_str = ("KK.mul KK.one KK.b = KK.add (KK.mul (KK.mul (KK.mul KK.invPhi r1) KK.b) rt) "
          "(KK.add (KK.mul (KK.mul (KK.mul KK.b rt) (KK.neg KK.invPhi)) rt) KK.zero)")
e5_str = ("KK.mul rt (KK.neg KK.invPhi) = KK.add (KK.mul (KK.mul (KK.mul KK.b r1) KK.b) rt) "
          "(KK.add (KK.mul (KK.mul (KK.mul (KK.neg KK.invPhi) rt) (KK.neg KK.invPhi)) rt) KK.zero)")
check("H7.e3_verbatim",
      in_file("theorem rt_unit_of_e3 (r1 rt : KK) (e3 : " + e3_str),
      "rt_unit_of_e3's hypothesis e3 is verbatim hex_at_3's equation")
check("H7.e5_verbatim",
      in_file("(e5 : " + e5_str) and in_file("theorem quad_times_rt_of_e5 (r1 rt : KK)"),
      "quad_times_rt_of_e5's hypothesis e5 is verbatim hex_at_5's equation")
check("H7.concl_rt_unit",
      in_file("KK.mul (KK.mul KK.invPhi (KK.add r1 (KK.neg rt))) rt = KK.one"),
      "conclusion of rt_unit_of_e3: (invPhi*(r1-rt))*rt = 1")
check("H7.concl_quad_times_rt",
      in_file("KK.mul rt (KK.add (KK.add r1 (KK.mul KK.invPhi rt)) KK.one) = KK.zero"),
      "conclusion of quad_times_rt_of_e5: rt*((r1+invPhi*rt)+1) = 0")
check("H7.concl_linear",
      in_file("KK.add (KK.add r1 (KK.mul KK.invPhi rt)) KK.one = KK.zero"),
      "conclusion of linear_of_e3_e5: (r1+invPhi*rt)+1 = 0")
check("H7.cancel_of_inv_sig",
      in_file("theorem cancel_of_inv (w rt X : KK) (hw : KK.mul w rt = KK.one) "
              "(h : KK.mul rt X = KK.zero) : X = KK.zero"),
      "cancel_of_inv: one-sided inverse hypothesis, conclusion X = 0")
# cancel_of_inv is valid in ANY commutative ring: skeleton identity, symbolic
skel = kk_add(P, kk_mul(P, uK, kk_mul(P, vK, wK)),
              kk_mul(P, kk_add(P, kk_of(P, K_ONE), kk_neg(P, kk_mul(P, uK, vK))), wK))
check("H7.cancel_skeleton", skel == wK,
      "X == w*(rt*X) + (1 - w*rt)*X symbolically (w,rt,X fresh 8-coord vars): "
      "cancellation needs only ring laws, no domain property")
# step identities in K[R1,RT] (certificates with exhibited coefficients):
step_rtunit = kp_sub(kp_mul(W, PRT), KP_ONE) == kp_neg(kp_mul(kp_const(K_T), R[3]))
step_quad = kp_mul(PRT, L_lin) == kp_neg(kp_mul(kp_const(K_PHI), R[5]))
check("H7.step1_rt_unit", step_rtunit, "w*RT - 1 == -t*Res3   (w := invPhi*(R1-RT))")
check("H7.step2_quad_times_rt", step_quad, "RT*L == -phi*Res5   (L := R1+invPhi*RT+1)")
cert_L = kp_add(kp_mul(kp_mul(kp_const(K_T), L_lin), R[3]),
                kp_neg(kp_mul(kp_mul(kp_const(K_PHI), W), R[5])))
check("H7.step3_linear_cert", L_lin == cert_L,
      "L == (t*L)*Res3 - (phi*w)*Res5 exactly: e3, e5 => L = 0 in any comm. ring")
Q_POLY = kp_add(kp_add(kp_mul(PRT, PRT), kp_mul(kp_const(K_INVPHI), PRT)), KP_ONE)
check("H7.step4_substitute_res1", Q_POLY == kp_sub(L_lin, R[1]),
      "Q == L - Res1: the r1:=rt^2 rewrite is exactly subtracting residual #1")
cert_Q = kp_sub(cert_L, R[1])
check("H7.step5_quadratic_cert", Q_POLY == cert_Q,
      "Q == (t*L)*Res3 - (phi*w)*Res5 - Res1: full certificate for "
      "hexagon_forces_quadratic")
# no domain property smuggled in: scan the four proof bodies
def body_of(name):
    # statement+proof only: stop at the next top-level declaration OR comment
    # block, so following docstrings are NOT swallowed into the proof text
    m = re.search(r"^theorem " + name +
                  r"\b.*?(?=^(?:theorem\b|def\b|end\b|namespace\b|/--|/-!))",
                  LEAN_TXT, re.S | re.M)
    return m.group(0) if m else ""
BODIES = {n: body_of(n) for n in
          ("cancel_of_inv", "rt_unit_of_e3", "quad_times_rt_of_e5",
           "linear_of_e3_e5", "hexagon_forces_rt_unit", "hexagon_forces_quadratic")}
seg = "".join(BODIES.values())
forbidden = ["IsDomain", "NoZeroDivisors", "mul_eq_zero", "zero_divisor",
             r"\bField\b", r"\bdiv\b", "inv_mul_cancel", "⁻¹", r"\bsorry\b",
             "Classical"]
bad = [f for f in forbidden if re.search(f, seg)]
check("H7.no_domain_grep", all(BODIES.values()) and bad == [],
      f"all 6 proof bodies extracted nonempty; none contains {forbidden}")
ALLOW = set("""theorem cancel_of_inv rt_unit_of_e3 quad_times_rt_of_e5 linear_of_e3_e5
  hexagon_forces_rt_unit hexagon_forces_quadratic hexagon_uniqueness r1 rt w X hw h e3 e5
  KK KK.mul KK.add KK.zero KK.one KK.neg KK.invPhi KK.b KK.emb KK.t Z5.phi Z5 phi
  KK.one_mul KK.mul_one KK.mul_zero KK.mul_assoc KK.add_zero KK.mul_right_comm
  KK.mul_comm KK.mul_add KK.add_mul KK.mul_neg KK.neg_mul KK.neg_neg KK.neg_add_cancel
  by calc rw at have exact fun of_decide_eq_true congrArg b_unit cancel_b cancel_invPhi
  kk_b_sq hex_at_3 hex_at_5 hexagonCheck kRng Fsymm a b c d e z true hA hB hA2 hB2 hL
  e3' e5' hlin h3 h5 hexagon_forces_r1_eq_rt_sq symm tau one""".split())
ALLOW.add("symm")
toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", seg))
def tok_ok(t):
    return t in ALLOW or all(p in ALLOW for p in t.split("."))
unexpected = sorted(t for t in toks if not tok_ok(t) and not t.startswith("_"))
check("H7.identifier_allowlist", unexpected == [],
      f"every identifier in the six proof bodies is a proved ring law / named "
      f"shim / hypothesis; unexpected={unexpected}")

# ══════════════════════════════════════════════════════════════════════════
# H8 — THE TRAP at (R1,RT) = (0,0)
# ══════════════════════════════════════════════════════════════════════════
at00 = {t: kp_eval(RES[t], K_ZERO, K_ZERO) for t in VALID}
fail00 = [t for t in VALID if at00[t] != K_ZERO]
check("H8.thirteen_vanish", sum(1 for t in VALID if at00[t] == K_ZERO) == 13,
      "13 of the 15 valid residuals vanish at (0,0)")
check("H8.nest", len(fail00) + 13 == 15, "2 failures + 13 = 15")
check("H8.failures_are_e1",
      set(fail00) == {FILE5[1], FILE5[2]} and
      all(t[4] == ONE_ for t in fail00) and
      [i for i in range(1, 6) if FILE5[i - 1][4] == ONE_] == [2, 3],
      "failures == instances #2,#3 == exactly the live e=1 instances")
check("H8.count_matches_theorem", viol_count(K_ZERO, K_ZERO) == 2,
      "countHexViolations(0,0) == 2 (zero_braiding_fails_only_two)")
route = [(T, T, T, O, T, T), (T, T, T, T, T, O), (T, T, T, T, T, T)]  # #1,#4,#5
check("H8.tempting_route_accepts",
      all(hex_check(K_ZERO, K_ZERO, t) for t in route),
      "instances #1,#4,#5 (the naive route) all ACCEPT (0,0)")
check("H8.e1_rejects",
      not hex_check(K_ZERO, K_ZERO, (T, T, T, T, O, T)) and
      not hex_check(K_ZERO, K_ZERO, (T, T, T, T, O, O)),
      "(t,t,t,t,1,t) and (t,t,t,t,1,1) REJECT (0,0)")
check("H8.stmt_fails_only_two",
      in_file("theorem zero_braiding_fails_only_two : countHexViolations KK.zero KK.zero = 2 := rfl"),
      "Lean states countHexViolations 0 0 = 2")
check("H8.stmt_tempting_route",
      in_file("hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .one .tau .tau = true") and
      in_file("hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .tau .one = true") and
      in_file("hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .tau .tau = true"),
      "zero_braiding_passes_the_tempting_route names tuples #1,#4,#5 = true")
check("H8.stmt_e1_reject",
      in_file("hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .one .tau = false") and
      in_file("hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .one .one = false"),
      "only_the_e_one_instances_reject_zero names tuples #3,#2 = false")
check("H8.negctrl_golden_all15", all(kp_eval(RES[t], K_R1, K_RT) == K_ZERO
                                     for t in VALID),
      "golden passes all 15 — the 2-failure count is specific to (0,0)")

# ══════════════════════════════════════════════════════════════════════════
# H9 — the cleaner cancellation: Res3 - b*Res5 == b*Q
# ══════════════════════════════════════════════════════════════════════════
BQ = kp_mul(kp_const(K_B), Q_POLY)
check("H9.identity", kp_sub(R[3], kp_mul(kp_const(K_B), R[5])) == BQ,
      "Res#3 - b*Res#5 == b*(RT^2 + invPhi*RT + 1) exactly "
      "(file instances #3=(t,t,t,t,1,t) and #5=(t,t,t,t,t,t); the charge's "
      "H9 tuple labels swap the e/z NAMES but denote these two)")
pairs = [(i, j) for i in range(1, 6) for j in range(1, 6) if i != j
         and kp_sub(R[i], kp_mul(kp_const(K_B), R[j])) == BQ]
check("H9.scan_unique", pairs == [(3, 5)],
      f"scan over all ordered live pairs: Res_i - b*Res_j == b*Q only for {pairs}")
c3 = R[3].get((1, 1), K_ZERO); c5 = kp_mul(kp_const(kn(K_B)), R[5]).get((1, 1), K_ZERO)
check("H9.cross_terms_cancel", c3 != K_ZERO and c5 != K_ZERO and ka(c3, c5) == K_ZERO,
      "R1*RT coefficients: Res3 has -invPhi*b, -b*Res5 has +invPhi*b — "
      "both nonzero, sum zero")
check("H9.rt2_coefficient",
      R[3].get((0, 2)) == km(K_B, K_INVPHI) and
      kp_mul(kp_const(kn(K_B)), R[5]).get((0, 2)) == km(K_B, km(K_INVPHI, K_INVPHI)) and
      z5a(INVPHI5, z5m(INVPHI5, INVPHI5)) == Z5_ONE,
      "RT^2 coeff = b*invPhi + b*invPhi^2 = b, because invPhi + invPhi^2 == 1")
check("H9.q_from_3_5", Q_POLY == kp_sub(kp_mul(kp_const(K_T), R[3]), R[5]),
      "Q == t*Res3 - Res5 (b a unit, t*b=1): instances #3,#5 alone force Q=0")
check("H9.negctrl_pair", kp_sub(R[4], kp_mul(kp_const(K_B), R[5])) != BQ,
      "Res#4 - b*Res#5 != b*Q (instance #4 carries an R1^2 term)")

# ══════════════════════════════════════════════════════════════════════════
# H10 — IDEAL(15 residuals) == (R1 - RT^2, Q)
# ══════════════════════════════════════════════════════════════════════════
check("H10.gen1_in_ideal", R[1] == R1_minus_RT2,
      "containment (i)a: R1 - RT^2 == 1 * Res#1 (unit coefficient +1)")
check("H10.gen2_in_ideal", Q_POLY == kp_sub(kp_mul(kp_const(K_T), R[3]), R[5])
      and is_unit(K_T) and kk_norm(K_T) in (1, -1),
      "containment (i)b: Q == t*Res#3 + (-1)*Res#5, coefficients t and -1 "
      f"both units (norm(t) = {kk_norm(K_T)})")
def reduce_by_gen1(p):
    """p = q1*(R1-RT^2) + s with s free of R1; returns (q1, s)."""
    q1 = KP_ZERO; work = dict(p)
    while True:
        cand = [(i, j) for (i, j) in work if i >= 1]
        if not cand: break
        i, j = max(cand)
        c = work[(i, j)]
        mono = {(i - 1, j): c}
        q1 = kp_add(q1, mono)
        work = kp_sub(work, kp_mul(mono, R1_minus_RT2))
    return q1, work
def divmod_by_Q(s):
    """s univariate in RT; s = q2*Q + r, Q monic; returns (q2, r)."""
    q2 = KP_ZERO; work = dict(s)
    while True:
        degs = [j for (i, j) in work if i == 0]
        if not degs or max(degs) < 2: break
        d = max(degs)
        c = work[(0, d)]
        mono = {(0, d - 2): c}
        q2 = kp_add(q2, mono)
        work = kp_sub(work, kp_mul(mono, Q_POLY))
    return q2, work
all_reduce = True; recompose = True
for t in VALID:
    q1, s = reduce_by_gen1(RES[t])
    q2, rem = divmod_by_Q(s)
    if rem != KP_ZERO: all_reduce = False
    if RES[t] != kp_add(kp_add(kp_mul(q1, R1_minus_RT2), kp_mul(q2, Q_POLY)), rem):
        recompose = False
check("H10.all_15_reduce", all_reduce,
      "containment (ii): every one of the 15 residuals has remainder 0 after "
      "R1 := RT^2 then exact division by monic Q")
check("H10.recomposition", recompose,
      "each residual == q1*(R1-RT^2) + q2*Q exactly (certificates recomposed)")
q1_, s_ = reduce_by_gen1(R[3]); q2_, _ = divmod_by_Q(s_)
check("H10.res3_quotient",
      kp_mul(q2_, Q_POLY) == kp_sub(s_, KP_ZERO) and
      s_ == kp_mul(kp_mul(kp_const(K_B),
                          kp_sub(KP_ONE, kp_mul(kp_const(K_INVPHI), PRT))), Q_POLY),
      "spot certificate: Res#3|_{R1:=RT^2} == b*(1 - invPhi*RT)*Q")
Q_WRONG = kp_add(kp_add(kp_mul(PRT, PRT), kp_mul(kp_const(K_INVPHI), PRT)),
                 kp_const(emb((2, 0, 0, 0))))
def divmod_by(s, D):
    q = KP_ZERO; work = dict(s)
    while True:
        degs = [j for (i, j) in work if i == 0]
        if not degs or max(degs) < 2: break
        d = max(degs); c = work[(0, d)]
        mono = {(0, d - 2): c}
        q = kp_add(q, mono); work = kp_sub(work, kp_mul(mono, D))
    return q, work
bad_rem = 0
for i in range(2, 6):
    _, s = reduce_by_gen1(R[i])
    _, rem = divmod_by(s, Q_WRONG)
    if rem != KP_ZERO: bad_rem += 1
check("H10.negctrl_wrong_Q", bad_rem > 0,
      f"wrong quadratic RT^2+invPhi*RT+2: {bad_rem}/4 live residuals leave "
      "nonzero remainder — the division test has teeth")
_, remRT = divmod_by_Q(dict(PRT))
check("H10.negctrl_rt_not_zero", remRT != KP_ZERO,
      "RT itself does NOT reduce to 0 — reduction is not vacuous")

# ══════════════════════════════════════════════════════════════════════════
# H11 — anti-vacuity + negative controls at constant braidings
# ══════════════════════════════════════════════════════════════════════════
def qk(x): return ka(ka(km(x, x), km(K_INVPHI, x)), K_ONE)
check("H11.golden_all15", viol_count(K_R1, K_RT) == 0 and
      all(kp_eval(RES[t], K_R1, K_RT) == K_ZERO for t in VALID),
      "golden (r1=zeta^2, rt=-zeta): all 15 residuals vanish")
check("H11.mirror_all15", viol_count(K_R1P, K_RTP) == 0 and
      all(kp_eval(RES[t], K_R1P, K_RTP) == K_ZERO for t in VALID),
      "mirror (r1'=zeta^3, rt'=(1,1,1,1)): all 15 residuals vanish")
check("H11.quadratic_roots", qk(K_RT) == K_ZERO and qk(K_RTP) == K_ZERO,
      "Q(rt) == 0 == Q(rt') in KK")
check("H11.sum_product", ka(K_RT, K_RTP) == kn(K_INVPHI) and
      km(K_RT, K_RTP) == K_ONE,
      "rt + rt' == -invPhi and rt*rt' == 1 exactly")
check("H11.r1_eq_rt_sq", km(K_RT, K_RT) == K_R1 and km(K_RTP, K_RTP) == K_R1P,
      "r1 == rt^2 and r1' == rt'^2")
v11 = viol_count(K_ONE, K_ONE)
two, three = emb((2, 0, 0, 0)), emb((3, 0, 0, 0))
v23 = viol_count(two, three)
vswap = viol_count(K_RT, K_R1)
check("H11.negctrl_11", v11 == 4,
      f"constant pair (1,1): {v11} of 15 violated (matches trivial_braiding_fails = 4)")
check("H11.negctrl_23", v23 > 0, f"constant pair (2,3): {v23} of 15 violated")
check("H11.negctrl_swap", vswap == 5,
      f"swapped (rt,r1): {vswap} of 15 violated (matches swapped_braiding_fails = 5)")

# optional, NON-LOAD-BEARING float sanity cross-check
try:
    import cmath, math
    z_c = cmath.exp(2j * cmath.pi / 5)
    phi_f = (1 + math.sqrt(5)) / 2
    def z5c(u): return sum(u[k] * z_c ** k for k in range(4))
    def kkc(u): return z5c(u[0]) + math.sqrt(phi_f) * z5c(u[1])
    mx = 0.0
    for t in VALID:
        val = sum(kkc(c) * kkc(K_R1) ** i * kkc(K_RT) ** j
                  for (i, j), c in RES[t].items())
        mx = max(mx, abs(val))
    print(f"info  H11.float_sanity  max |residual| at golden (complex floats) = "
          f"{mx:.2e}  [not load-bearing]")
except Exception as ex:                                   # pragma: no cover
    print(f"info  H11.float_sanity skipped: {ex}")

# ══════════════════════════════════════════════════════════════════════════
# H12 — the PROOFS.md hexagon-section names exist as declarations; prose fixes
# ══════════════════════════════════════════════════════════════════════════
NAMES = ["cancel_b", "cancel_invPhi", "bphi_is_t", "rt_unit_of_e3",
         "quad_times_rt_of_e5", "linear_of_e3_e5", "hexagon_forces_rt_unit",
         "hexagon_forces_quadratic", "hexagon_uniqueness",
         "golden_quadratic_by_necessity", "mirror_satisfies_hexagon",
         "mirror_quadratic_by_necessity", "golden_chains_cleared",
         "roots_sum_and_product", "zero_braiding_fails_only_two",
         "zero_braiding_passes_the_tempting_route",
         "only_the_e_one_instances_reject_zero", "cancel_of_inv"]
missing = [n for n in NAMES
           if not re.search(r"^theorem " + n + r"\b", LEAN_TXT, re.M)]
check("H12.declarations", missing == [],
      f"all 18 hexagon-section names declared as theorems; missing={missing}")
PROOFS_TXT = open(PROOFS, encoding="utf-8").read()
in_ledger = [n for n in NAMES if n in PROOFS_TXT]
check("H12.ledger_lists_them", len(in_ledger) == 18,
      f"{len(in_ledger)}/18 names appear in PROOFS.md")
ghosts = [n for n in ("factors_exactly", "hexagon_exactly_two", "K_is_domain")
          if re.search(r"^theorem " + n + r"\b", LEAN_TXT, re.M)]
check("H12.negctrl_ghost_names", ghosts == [],
      "no declaration named factors_exactly / hexagon_exactly_two / K_is_domain")
def docstring_before(name):
    m = re.search(r"^theorem " + name + r"\b", LEAN_TXT, re.M)
    if not m: return ""
    pre = LEAN_TXT[:m.start()]
    k = pre.rfind("/--")
    return pre[k:] if k >= 0 else ""
d_coi = docstring_before("cancel_of_inv")
check("H12.cancel_of_inv_one_sided",
      "**left** inverse" in d_coi and "one-sided" in d_coi,
      "cancel_of_inv docstring says LEFT/one-sided inverse "
      "(and flags the old two-sided wording as inaccurate)")
d_rsp = re.sub(r"\s+", " ", docstring_before("roots_sum_and_product"))
check("H12.roots_prose_withdrawn",
      "withdrawn" in d_rsp and "not asserted by any declaration" in d_rsp
      and "realizes" in d_rsp and "FACTORS EXACTLY" not in d_rsp
      and "only possible pair" in d_rsp,  # quoted only as the withdrawn wording
      "roots_sum_and_product prose: only-possible-pair quoted-as-withdrawn; "
      "factorization stated as not-a-declaration; no FACTORS-EXACTLY headline")
iretr = LEAN_TXT.find("ROUND-3 RETRACTION")
idom = LEAN_TXT.find("K is a\ndomain")
if idom < 0: idom = LEAN_TXT.find("K is a domain")
check("H12.domain_retraction_marker",
      iretr >= 0 and idom >= 0 and abs(idom - iretr) < 1500 and
      "withdrawn" in LEAN_TXT[iretr:iretr + 1500],
      "stale K-is-a-domain / exactly-two prose sits under an explicit "
      "ROUND-3 RETRACTION marker with 'withdrawn'")
code_only = LEAN_TXT
prev = None
while prev != code_only:                       # strip /- ... -/ blocks, then --
    prev = code_only
    code_only = re.sub(r"/-[^\0]*?-/", "", code_only, count=1)
code_only = re.sub(r"--.*", "", code_only)
check("H12.no_sorry_in_code", not re.search(r"\bsorry\b", code_only),
      "no `sorry` term in Anyon.lean code (the string occurs only in header "
      "prose, inside comments)")

print()
nfail = sum(1 for _, ok, _ in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  ({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
