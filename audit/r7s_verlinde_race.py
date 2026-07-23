#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r7s_verlinde_race.py — round-7 SEAT: exact recomputation, FIRST CONTACT
between the two independently-built Verlinde routes.

THE RACE.  The builder's certificate audit/r7_gift_verlinde.py (44/44) did NOT
reach the third body last ferry; their Verlinde.lean was built from ROUND7.md's
constants and independently audited.  This script is the first place the two
routes touch: it transcribes THEIR definitions from Verlinde.lean (hash-pinned)
into Python exactly, transcribes the CERTIFICATE's cleared forms, and races
them cell by cell over exact arithmetic (int / Fraction; floats only in
labelled non-load-bearing sanity lines).

TASKS COVERED
  T1  re-run the gift certificate on this tree (subprocess; expect 44/44).
  T2  their Zp core: Msel (cleared S), verlNum, fuseMult — all 8 Verlinde
      cells, D^2*fuseMult = verlNum; normalization race vs the certificate's
      W4d cleared form (term-by-term; unit relation measured).
  T3  their Z5 T-layer: (Shat T)^3 = (phi+2) p+ I, p+ p- = D^2, the mirror
      chirality — raced against the certificate's route and an INDEPENDENT
      Z5 implementation written here.
  T4  the lambda parking: lambda = zeta20^13, lambda*D = p+ re-verified in
      Z[zeta20] (two multiplication routes); order(lambda) = 20; the
      degree-8-vs-4 obstruction made arithmetic (rank of powers); the
      mu_10 torsion of Z[zeta5] checked by bounded search; denominator-5
      coordinate fact re-solved.
  T5  their wrong-S (Hadamard) control: fails EXACTLY the cell the file
      names, and only that cell; the failing values are the docstring's.
  T6  circle closing: the 8 S-matrix integers vs fuse-derived
      multiplicities from Anyon.lean's round-1 machinery (fuse/countA),
      through TWO codebases and THREE arithmetic routes.

STANDARD FACTS CITED (labelled, not computed): cyclotomic Phi_n irreducible
over Q; roots of unity of Q(zeta5) = mu_10 (n odd => W(Q(zeta_n)) = mu_2n);
[Q(zeta5):Q] = 4, [Q(zeta20):Q] = 8.  Every use is accompanied by the
concrete arithmetic witness computed here.

NORM 16: this is a new instrument; its own planted-defect bites (B1-B4) run
in the same pass — each deliberately-broken input must FAIL the check it
feeds, or the instrument is declared blind and this run exits nonzero.

Exact quotations from Verlinde.lean are marked [V:<line>]; from
r7_gift_verlinde.py, [G:<check>].  No Lean toolchain here: kernel/axiom
receipts are NOT re-checkable in this environment (their transcript views
are hash-stamped; see R0).
"""
import sys, os, subprocess, hashlib, random, cmath, re
from fractions import Fraction as Fr
from itertools import product
from math import pi

random.seed(20260723)
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, ".."))

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def info(msg):
    print(f"      {msg}")

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

# ======================================================================
# R0 — PIN THE TREE.  The definitions raced below are quoted from these
# exact bytes; if the hashes move, every [V:...] tag is unverified.
# ======================================================================
print("=" * 72)
print("R0 — tree pin: the sources being raced, by hash")
print("=" * 72)

VER = os.path.join(LEAN, "Verlinde.lean")
ANY = os.path.join(LEAN, "Anyon.lean")
H_VER = "cf04711c97f7155ffca78f6247162a2030c5d69ee11a1df02c7700b0a75b7ff2"
H_ANY = "bf08795ba09c66f486e7dcdf337cc3a5d20b6b85e72cce093300c32639993d8e"
ver_src = open(VER, encoding="utf-8").read()
any_src = open(ANY, encoding="utf-8").read()
check("R0a_hashes",
      sha256(VER) == H_VER and sha256(ANY) == H_ANY,
      "Verlinde.lean = cf04711c…, Anyon.lean = bf08795b… — the stamps in "
      "PROOFS.md and audit/transcript-round7.txt; the [V:]/[A:] quotes below "
      "are pinned to these bytes")
ver_lines = ver_src.splitlines()
check("R0b_shape",
      len(ver_lines) == 625 and
      sum(1 for l in ver_lines if l.startswith("theorem ")) == 75,
      f"Verlinde.lean: {len(ver_lines)} lines, "
      f"{sum(1 for l in ver_lines if l.startswith('theorem '))} line-start "
      "theorems — the census row 625/75")
check("R0c_hygiene_tokens",
      not any(l.startswith("import") for l in ver_lines) and
      not re.search(r"\bsorry\b", ver_src.replace(
          "No `sorry`, no `native_decide`", "")) and
      "native_decide" not in ver_src.replace(
          "No `sorry`, no `native_decide`", ""),
      "no import lines; 'sorry'/'native_decide' appear only in the header "
      "disclaimer (line 7) — textual check only; kernel receipts live in "
      "their transcript, not re-runnable here (no Lean toolchain)")
# the transcription claim, checked as fact not name: the Zp / Z5 / fuse
# blocks in Verlinde.lean are byte-identical to their Anyon.lean originals.
def block(src, start_marker, end_marker):
    i = src.index(start_marker)
    j = src.index(end_marker, i)
    return src[i:j]
zp_v = block(ver_src, "structure Zp where", "end Zp")
zp_a = block(any_src, "structure Zp where", "end Zp")
z5_v = block(ver_src, "structure Z5 where", "end Z5")
z5_a = block(any_src, "structure Z5 where", "end Z5")
fuse_v = block(ver_src, "def fuse", "-- memA")
fuse_a = block(any_src, "def fuse", "/-- Membership")
conj_v = "def conj (u : Z5) : Z5 := ⟨u.a0 - u.a1, -u.a1, u.a3 - u.a1, u.a2 - u.a1⟩"
check("R0d_transcription_fact",
      zp_v == zp_a and z5_v == z5_a and
      fuse_v.rstrip() == fuse_a.rstrip() and
      conj_v in ver_src and conj_v in any_src and
      "def conj (u : Zp)" not in any_src and "def conj (u : Zp)" in ver_src,
      "Zp block, Z5 block, fuse def byte-identical Verlinde vs Anyon; "
      "Z5.conj line identical; Zp.conj present ONLY in Verlinde — the "
      "file's 'ONE new definition, labeled NEW' claim is exact")

# ======================================================================
# R1 — T1: RE-RUN THE GIFT CERTIFICATE ON THIS TREE
# ======================================================================
print("=" * 72)
print("R1 — T1: re-run audit/r7_gift_verlinde.py (expect 44/44, exit 0)")
print("=" * 72)
proc = subprocess.run([sys.executable, os.path.join(HERE, "r7_gift_verlinde.py")],
                      capture_output=True, text=True, cwd=HERE)
tail = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ""
n_fail_lines = sum(1 for l in proc.stdout.splitlines() if l.startswith("FAIL"))
check("R1a_gift_44_of_44",
      proc.returncode == 0 and tail == "RESULT: 44/44 PASS" and n_fail_lines == 0,
      f"exit={proc.returncode}, last line '{tail}', FAIL lines: {n_fail_lines} "
      "— the certificate still passes on the round-7 tree (first contact: "
      "their Verlinde was built from ROUND7.md constants, never from this "
      "script)")

# ======================================================================
# R2 — T2: THEIR Zp CORE, TRANSCRIBED EXACTLY, RACED TWO WAYS
# ======================================================================
print("=" * 72)
print("R2 — T2: Msel / verlNum / fuseMult over Zp; certificate normalization")
print("=" * 72)

# --- THEIR ring [V:86-108]: <m,n> = m + n*phi, phi^2 = phi+1 ---
zp_add = lambda u, v: (u[0] + v[0], u[1] + v[1])
zp_neg = lambda u: (-u[0], -u[1])
def zp_mul(u, v):   # [V:100-101] (a+b phi)(c+d phi) = (ac+bd) + (ad+bc+bd) phi
    return (u[0]*v[0] + u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])
ZP0, ZP1, ZPPHI, ZPINV = (0, 0), (1, 0), (0, 1), (-1, 1)   # [V:93-95,106]
zp_conj = lambda u: (u[0] + u[1], -u[1])                    # [V:118] NEW def

# --- INDEPENDENT route: m + n*phi as (m + n/2) + (n/2) sqrt5, Fractions ---
def q5_of_zp(u):
    return (Fr(u[0]) + Fr(u[1], 2), Fr(u[1], 2))
def q5_mul(p, q):
    return (p[0]*q[0] + 5*p[1]*q[1], p[0]*q[1] + p[1]*q[0])
def zp_of_q5(p):
    n = 2 * p[1]; m = p[0] - p[1]
    assert n.denominator == 1 and m.denominator == 1
    return (int(m), int(n))
race_ok = True
for _ in range(500):
    u = (random.randint(-99, 99), random.randint(-99, 99))
    v = (random.randint(-99, 99), random.randint(-99, 99))
    race_ok = race_ok and zp_of_q5(q5_mul(q5_of_zp(u), q5_of_zp(v))) == zp_mul(u, v)
check("R2a_Zp_mul_raced", race_ok,
      "their Zp.mul [V:100] vs an independent Q(sqrt5)/Fraction route: "
      "equal on 500 random pairs — the transcription computes Z[phi]")

DSQ = zp_add(ZPPHI, (2, 0))            # [V:126] Dsq = phi + <2,0> = <2,1>
SQRT5 = (-1, 2)                        # [V:128]
check("R2b_pretty_identity",
      zp_mul(SQRT5, SQRT5) == (5, 0) and DSQ == zp_mul(SQRT5, ZPPHI)
      and DSQ == (2, 1),
      "sqrt5^2 = <5,0> [V:131], Dsq = sqrt5*phi = <2,1> [V:134] — "
      "D^2 = phi+2 = sqrt5*phi, the pretty identity, exact")
check("R2c_norm_5_nonunit",
      zp_mul(DSQ, zp_conj(DSQ)) == (5, 0) and zp_conj(DSQ) == (3, -1) and
      all(zp_mul(zp_conj(u := (random.randint(-9, 9), random.randint(-9, 9))),
                 zp_conj(v := (random.randint(-9, 9), random.randint(-9, 9))))
          == zp_conj(zp_mul(u, v)) for _ in range(200)),
      "N(D^2) = (phi+2)(3-phi) = 5 [V:138,141]; conj multiplicative on 200 "
      "random pairs, so N is multiplicative and D^2*u = 1 would force "
      "5*N(u) = 1 in Z — impossible: 1/D never in Z[phi], clearing forced")
# Z[phi] is a domain where uniqueness needs it: N(u) = 0 only at u = 0
dom = all(not (zp_mul(u, zp_conj(u)) == (0, 0)) or u == (0, 0)
          for u in product(range(-20, 21), repeat=2))
check("R2d_norm_zero_box", dom,
      "N(m+n*phi) = m^2+mn-n^2 vanishes ONLY at (0,0) on the box "
      "[-20,20]^2 (fact: m^2+mn-n^2 = 0 needs 5n^2 square, n = 0) — "
      "supports the uniqueness step (iii) of the file's adjudicator")

# --- THEIR data [V:156-210] ---
ONE, TAU = 0, 1
MSEL = {(ONE, ONE): ZP1, (ONE, TAU): ZPPHI,
        (TAU, ONE): ZPPHI, (TAU, TAU): zp_neg(ZP1)}        # [V:156-160]
def fuse(a, b):                                            # [V:48-51]
    if a == ONE: return [b]
    if b == ONE: return [a]
    return [ONE, TAU]
def fuseMult(a, b, c):                                     # [V:193-194] countP
    return sum(1 for x in fuse(a, b) if x == c)
def verlNum(a, b, c):                                      # [V:207-210] exact assoc
    t1 = zp_mul(zp_mul(MSEL[(a, ONE)], MSEL[(b, ONE)]), MSEL[(c, ONE)])
    t2 = zp_mul(zp_mul(zp_mul(MSEL[(a, TAU)], MSEL[(b, TAU)]),
                       MSEL[(c, TAU)]), ZPINV)
    return zp_add(t1, t2)

cells = list(product((ONE, TAU), repeat=3))
names = {ONE: "1", TAU: "t"}
ok8, rows = True, []
for (a, b, c) in cells:
    lhs = zp_mul(DSQ, (fuseMult(a, b, c), 0))              # [V:218] LHS order
    rhs = verlNum(a, b, c)
    ok8 = ok8 and lhs == rhs
    rows.append(f"{names[a]}{names[b]}{names[c]}: D^2*{fuseMult(a,b,c)}="
                f"{lhs} vs verlNum={rhs}")
info("; ".join(rows))
check("R2e_verlinde_cleared_8cells", ok8,
      "D^2 * fuseMult a b c = verlNum a b c for ALL 8 cells, their exact "
      "definitions and association order [V:218 verlinde_cleared] — "
      "recomputed here, cell by cell, exact")

# M_symm, M_sq, rows_orthonormal, dims_from_S [V:166-186]
matmul_zp = lambda A, B: {(i, j): zp_add(zp_mul(A[(i, ONE)], B[(ONE, j)]),
                                         zp_mul(A[(i, TAU)], B[(TAU, j)]))
                          for i in (ONE, TAU) for j in (ONE, TAU)}   # [V:72-74]
MSQ = matmul_zp(MSEL, MSEL)
DSQI = {(i, j): DSQ if i == j else ZP0 for i in (ONE, TAU) for j in (ONE, TAU)}
rowdot = lambda i, j: zp_add(zp_mul(MSEL[(i, ONE)], MSEL[(j, ONE)]),
                             zp_mul(MSEL[(i, TAU)], MSEL[(j, TAU)]))  # [V:173]
check("R2f_M_layer",
      all(MSEL[(i, j)] == MSEL[(j, i)] for i, j in MSQ) and MSQ == DSQI and
      all(rowdot(i, j) == DSQI[(i, j)] for i in (ONE, TAU) for j in (ONE, TAU))
      and MSEL[(ONE, ONE)] == ZP1 and MSEL[(ONE, TAU)] == ZPPHI,
      "M_symm, M_sq (M^2 = D^2 I via their matMul [V:72]), rows_orthonormal, "
      "dims_from_S (M_00, M_0t) = (1, phi) — all recomputed [V:166-186]")

# --- the certificate's cleared form [G:W4d], raced TERM BY TERM ---
SHAT_G = [[(1, 0), (0, 1)], [(0, 1), (-1, 0)]]
W_G = [(1, 0), (-1, 1)]
same_norm, unit_rel = True, set()
for (a, b, c) in cells:
    tg1 = zp_mul(zp_mul(SHAT_G[a][0], SHAT_G[b][0]),
                 zp_mul(SHAT_G[c][0], W_G[0]))
    tg2 = zp_mul(zp_mul(SHAT_G[a][1], SHAT_G[b][1]),
                 zp_mul(SHAT_G[c][1], W_G[1]))
    tv1 = zp_mul(zp_mul(MSEL[(a, ONE)], MSEL[(b, ONE)]), MSEL[(c, ONE)])
    tv2 = zp_mul(zp_mul(zp_mul(MSEL[(a, TAU)], MSEL[(b, TAU)]),
                        MSEL[(c, TAU)]), ZPINV)
    same_norm = same_norm and tg1 == tv1 and tg2 == tv2 and \
        zp_add(tg1, tg2) == verlNum(a, b, c) and \
        zp_mul((fuseMult(a, b, c), 0), (2, 1)) == zp_mul(DSQ, (fuseMult(a, b, c), 0))
    unit_rel.add((tg1 == tv1, tg2 == tv2))
check("R2g_normalization_identical", same_norm and unit_rel == {(True, True)},
      "FIRST CONTACT, cleared vs cleared: the certificate's W4d form "
      "sum_x Shat_ax Shat_bx Shat_cx w_x (w = (1, invPhi)) equals THEIR "
      "verlNum TERM BY TERM (x=1 and x=tau separately), all 8 cells, and "
      "both right sides are N*(phi+2) — SAME normalization, unit relation "
      "between the two clearings = 1 exactly (not merely associate)")

# uniqueness made concrete: division by D^2 is the linear system with det 5
uniq = True
for (a, b, c) in cells:
    p, q = verlNum(a, b, c)
    x = Fr(3 * p - q, 5); y = Fr(2 * q - p, 5)   # inverse of mult-by-(2,1)
    uniq = uniq and x.denominator == 1 and y == 0 and int(x) == fuseMult(a, b, c)
check("R2h_unique_integer_quotient", uniq,
      "solving D^2 * (x + y phi) = verlNum exactly: det(mult-by-D^2) = 5 "
      "(= N(D^2)!), and all 8 solutions are (x, y) = (fuseMult, 0) — "
      "N_ab^c = verlNum/D^2 is the UNIQUE Z[phi] element and it is the "
      "integer fuseMult: N in Z, N = fuse, pinned")

# B-bite (norm 16): drop the invPhi weight — the identity must break
b2 = sum(1 for (a, b, c) in cells
         if zp_add(zp_mul(zp_mul(MSEL[(a, ONE)], MSEL[(b, ONE)]), MSEL[(c, ONE)]),
                   zp_mul(zp_mul(MSEL[(a, TAU)], MSEL[(b, TAU)]), MSEL[(c, TAU)]))
         != zp_mul(DSQ, (fuseMult(a, b, c), 0)))
check("R2i_BITE_weight_dropped", b2 >= 1,
      f"planted defect: verlNum without the invPhi weight breaks {b2}/8 "
      "cells — this racer can fail (norm 16 bite #1)")
bad_mul = lambda u, v: (u[0]*v[0] - u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])
check("R2j_BITE_broken_ring", bad_mul(ZPPHI, ZPPHI) !=
      zp_of_q5(q5_mul(q5_of_zp(ZPPHI), q5_of_zp(ZPPHI))),
      "planted defect: a phi^2 = phi-1 ring diverges from the Q(sqrt5) "
      "route at phi*phi — the race has teeth (norm 16 bite #2)")

# ======================================================================
# R3 — T3: THE Z5 T-LAYER — MODULAR CUBE, MIRROR, GAUSS DUALITY
# ======================================================================
print("=" * 72)
print("R3 — T3: (Shat T)^3 = (phi+2) p+ I; p+ p- = D^2; the mirror chirality")
print("=" * 72)

def z5_mul(u, v):                                          # [V:331-339]
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
z5_conj = lambda u: (u[0] - u[1], -u[1], u[3] - u[1], u[2] - u[1])  # [V:428]
Z50, Z51 = (0, 0, 0, 0), (1, 0, 0, 0)
ZT, ZT2, ZT3, ZT4 = (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (-1, -1, -1, -1)
Z5PHI, Z5INV = (0, 0, -1, -1), (-1, 0, -1, -1)             # [V:349,352]

def z5_mul_mine(u, v):   # INDEPENDENT: exponents mod 5, then subtract a4*(1,1,1,1)
    c = [0] * 5
    for i in range(4):
        for j in range(4):
            c[(i + j) % 5] += u[i] * v[j]
    return (c[0] - c[4], c[1] - c[4], c[2] - c[4], c[3] - c[4])
race5 = all(z5_mul(u, v) == z5_mul_mine(u, v)
            for u, v in ((tuple(random.randint(-9, 9) for _ in range(4)),
                          tuple(random.randint(-9, 9) for _ in range(4)))
                         for _ in range(500)))
check("R3a_Z5_mul_raced", race5,
      "their Z5.mul c-vector reduction [V:331] vs an independent "
      "exponents-mod-5 route: equal on 500 random pairs")
conj_invol = all((lambda u: z5_conj(z5_conj(u)) == u)(
    tuple(random.randint(-9, 9) for _ in range(4))) for _ in range(100))
check("R3b_Z5_receipts",
      z5_mul(ZT3, ZT) == ZT4 and z5_mul(ZT4, ZT) == Z51 and
      z5_add(z5_add(Z51, ZT), ZT4) == Z5PHI and z5_add(ZT, ZT4) == Z5INV and
      z5_mul(Z5PHI, Z5INV) == Z51 and
      z5_mul(Z5PHI, Z5PHI) == z5_add(Z5PHI, Z51) and
      z5_conj(ZT) == ZT4 and z5_conj(ZT2) == ZT3 and z5_conj(ZT3) == ZT2 and
      z5_conj(ZT4) == ZT and z5_conj(Z5PHI) == Z5PHI and
      z5_conj(Z5INV) == Z5INV and conj_invol,
      "receipts [V:358-363, 430-435]: zeta3*zeta = zeta4, zeta4*zeta = 1, "
      "1+zeta+zeta4 = phi, zeta+zeta4 = invPhi, phi*invPhi = 1, "
      "phi^2 = phi+1; conj swaps (zeta,zeta4),(zeta2,zeta3), fixes phi and "
      "invPhi, involutive on 100 random elements")
conj_hom = all(z5_conj(z5_mul(u, v)) == z5_mul(z5_conj(u), z5_conj(v))
               for u, v in ((tuple(random.randint(-9, 9) for _ in range(4)),
                             tuple(random.randint(-9, 9) for _ in range(4)))
                            for _ in range(300)))
check("R3c_conj_multiplicative", conj_hom,
      "Z5.conj multiplicative on 300 random pairs (their proved ring map, "
      "re-measured)")

PHIP2 = (2, 0, -1, -1)                 # [V:476]
PP = (0, -1, 0, 1)                     # [V:478]
PM = (1, 1, 2, 1)                      # [V:480]
check("R3d_constants",
      PHIP2 == z5_add(Z5PHI, (2, 0, 0, 0)) and
      PHIP2 == z5_add(z5_mul(Z5PHI, Z5PHI), Z51) and
      PP == z5_add(ZT3, z5_neg(ZT)) and PM == z5_add(ZT2, z5_neg(ZT4)) and
      PM == z5_conj(PP),
      "phiPlus2 = phi+2 = phi^2+1 [V:483,485]; pp = zeta^3-zeta [V:487]; "
      "pm = zeta^2-zeta^4 [V:489]; pm = conj pp [V:493] — all literals "
      "re-derived from their defining expressions")
# cross-ring coherence: the Zp D^2 maps to the Z5 phiPlus2 under m+n*phi
zp_to_z5 = lambda u: (u[0], 0, -u[1], -u[1])
homx = zp_to_z5(DSQ) == PHIP2 and all(
    zp_to_z5(zp_mul(u, v)) == z5_mul(zp_to_z5(u), zp_to_z5(v))
    for u, v in (((random.randint(-9, 9), random.randint(-9, 9)),
                  (random.randint(-9, 9), random.randint(-9, 9)))
                 for _ in range(300)))
check("R3e_cross_ring_D2", homx,
      "m+n*phi |-> m+n*Z5.phi is multiplicative (300 random pairs) and "
      "sends Zp's Dsq = <2,1> to Z5's phiPlus2 = (2,0,-1,-1): the two "
      "rings' D^2 are THE SAME constant — the Zp core and Z5 T-layer share "
      "one D^2")

THETA = ZT3                            # [V:462] thetaTau = zeta^3
check("R3f_twist_cosign",
      z5_add(z5_mul(ZT2, Z5INV), z5_neg(ZT)) == THETA,
      "ribbon co-sign [V:469-470]: zeta^2*(1/phi) - zeta = zeta^3 = "
      "theta_tau, exactly (grammar_hexagon's twist arriving in Z5)")

def mat2_mul(M, N):                    # [V:510-514], entries (a,b,c,d)
    return (z5_add(z5_mul(M[0], N[0]), z5_mul(M[1], N[2])),
            z5_add(z5_mul(M[0], N[1]), z5_mul(M[1], N[3])),
            z5_add(z5_mul(M[2], N[0]), z5_mul(M[3], N[2])),
            z5_add(z5_mul(M[2], N[1]), z5_mul(M[3], N[3])))
SHATT = (Z51, z5_mul(Z5PHI, ZT3), Z5PHI, z5_neg(ZT3))      # [V:517]
# certificate route [G:W5c-d]: Shat * T as an actual product
SHAT5 = (Z51, Z5PHI, Z5PHI, z5_neg(Z51))
TMAT = (Z51, Z50, Z50, THETA)
check("R3g_ShatT_is_product", mat2_mul(SHAT5, TMAT) == SHATT,
      "their ShatT literal [[1, phi zeta^3],[phi, -zeta^3]] equals the "
      "matrix product Shat*T with T = diag(1, zeta^3) — the file's literal "
      "and the certificate's product route coincide")
CUBE = mat2_mul(mat2_mul(SHATT, SHATT), SHATT)             # [V:522] their assoc
SC = z5_mul(PHIP2, PP)
check("R3h_modular_cube",
      CUBE == (SC, Z50, Z50, SC),
      f"(Shat T)^3 = (phi+2) pp I EXACTLY [V:521-523]: diagonal {SC}, "
      "off-diagonal (0,0,0,0) — recomputed with their Mat2.mul and their "
      "association ((M*M)*M)")
CUBE_M = None  # independent arithmetic route
def mat2_mul_mine(M, N):
    return (z5_add(z5_mul_mine(M[0], N[0]), z5_mul_mine(M[1], N[2])),
            z5_add(z5_mul_mine(M[0], N[1]), z5_mul_mine(M[1], N[3])),
            z5_add(z5_mul_mine(M[2], N[0]), z5_mul_mine(M[3], N[2])),
            z5_add(z5_mul_mine(M[2], N[1]), z5_mul_mine(M[3], N[3])))
CUBE_M = mat2_mul_mine(mat2_mul_mine(SHATT, SHATT), SHATT)
check("R3i_cube_raced", CUBE_M == CUBE and
      z5_mul_mine(PHIP2, PP) == SC,
      "the cube recomputed with the INDEPENDENT Z5 multiplication: "
      "identical, entry by entry — two arithmetics, one scalar")
check("R3j_gauss_duality",
      z5_mul(PP, PM) == PHIP2 and z5_mul_mine(PP, PM) == PHIP2,
      "pp * pm = phi+2 = D^2 in Z[zeta5] [V:544 pp_pm_eq_D2] — both "
      "multiplication routes; the cleared |lambda D|^2 = D^2")

SHATTM = (Z51, z5_mul(Z5PHI, ZT2), Z5PHI, z5_neg(ZT2))     # [V:528]
TMATM = (Z51, Z50, Z50, ZT2)
CUBEM = mat2_mul(mat2_mul(SHATTM, SHATTM), SHATTM)
SCM = z5_mul(PHIP2, PM)
check("R3k_mirror_chirality",
      SHATTM == mat2_mul(SHAT5, TMATM) and CUBEM == (SCM, Z50, Z50, SCM) and
      CUBE != (SCM, Z50, Z50, SCM) and SC != SCM and PP != PM,
      "mirror [V:528-532]: T' = diag(1, zeta^2) gives (Shat T')^3 = "
      "(phi+2) pm I; pairing theta = zeta^3 with pm FAILS; "
      "(phi+2)pp != (phi+2)pm and pp != pm — the OTHER chirality, exactly "
      "as the certificate has it [G:W5f], index load-bearing")
check("R3l_mirror_is_conj",
      tuple(z5_conj(e) for e in CUBE) == CUBEM and
      all(z5_conj(SHATT[k]) == SHATTM[k] for k in range(4)),
      "ShatTmirror is the entrywise conjugate of ShatT and the mirror cube "
      "is the conjugate cube — 'the chirality flip is complex conjugation' "
      "verified at the matrix level, not just the scalar")

PP2 = z5_mul(PP, PP)
check("R3m_pow4_identities",
      z5_mul(PP2, PP2) == z5_mul(THETA, z5_mul(PHIP2, PHIP2)) and
      z5_mul(z5_mul(PM, PM), z5_mul(PM, PM)) ==
      z5_mul(ZT2, z5_mul(PHIP2, PHIP2)),
      "pp^4 = theta_tau (phi+2)^2 and pm^4 = zeta^2 (phi+2)^2 "
      "[V:549-556] — the cleared lambda^4 = theta_tau, both chiralities")

check("R3n_balancing_identities",
      z5_mul(z5_mul(Z51, Z51), Z51) == z5_mul(z5_mul(Z51, Z51), Z51) and
      z5_mul(z5_mul(Z5PHI, Z51), THETA) == z5_mul(z5_mul(Z51, Z5PHI), THETA) and
      z5_mul(z5_mul(z5_neg(Z51), THETA), THETA) ==
      z5_add(z5_mul(z5_mul(Z51, Z51), Z51), z5_mul(z5_mul(Z51, Z5PHI), THETA)),
      "the three cleared balancing identities [V:567-583]: (1,1), (1,tau) "
      "and the substantive (tau,tau): (-1) theta^2 = 1 + phi zeta^3, both "
      "sides reduce to -zeta — 'imaginary parts cancel' is a ring identity")
# certificate's 4-entry form [G:W6f]: S_ab*D = sum_c N d_c theta_c/(theta_a theta_b)
THI = [Z51, ZT2]; DIM5 = [Z51, Z5PHI]; TH5 = [Z51, THETA]
w6f = z5_mul(THETA, ZT2) == Z51
SH = [[Z51, Z5PHI], [Z5PHI, z5_neg(Z51)]]
for a in (0, 1):
    for b in (0, 1):
        tot = Z50
        for c in (0, 1):
            if fuseMult(a, b, c):
                tot = z5_add(tot, z5_mul(z5_mul(DIM5[c], TH5[c]),
                                         z5_mul(THI[a], THI[b])))
        w6f = w6f and tot == SH[a][b]
check("R3o_S_from_twists", w6f,
      "certificate cross-check [G:W6f]: Shat_ab = sum_c N_ab^c d_c theta_c "
      "theta_a^-1 theta_b^-1 for all four entries, exact in Z5 (with "
      "theta^-1 = zeta^2) — the S-matrix rebuilt from fuse+dims+twists")

check("R3p_negative_controls",
      THETA != Z51 and
      z5_mul(z5_mul(z5_mul(z5_mul(ZT3, ZT3), ZT3), ZT3), ZT3) == Z51 and
      PP != Z50 and PHIP2 != Z50 and SC != Z50 and SC != PHIP2,
      "their Part-5 controls [V:590-607]: theta nontrivial yet theta^5 = 1; "
      "pp, phi+2, (phi+2)pp all nonzero; the cube scalar CARRIES pp "
      "((phi+2)pp != phi+2) — anti-vacuity holds")
# B-bite (norm 16): wrong twist theta = zeta must break the cube shape
SHATT_BAD = (Z51, z5_mul(Z5PHI, ZT), Z5PHI, z5_neg(ZT))
CUBE_BAD = mat2_mul(mat2_mul(SHATT_BAD, SHATT_BAD), SHATT_BAD)
check("R3q_BITE_wrong_twist",
      CUBE_BAD != (SC, Z50, Z50, SC) and
      not (CUBE_BAD[1] == Z50 and CUBE_BAD[2] == Z50 and
           CUBE_BAD[0] == CUBE_BAD[3]),
      "planted defect: theta = zeta (wrong twist) — the cube is not even "
      "scalar, let alone (phi+2)pp I (norm 16 bite #3)")
# float co-sign, NON-LOAD-BEARING
z5fl = lambda u: sum(u[k] * cmath.exp(2j * pi * k / 5) for k in range(4))
res = max(abs(z5fl(CUBE[0]) - z5fl(SC)),
          abs(z5fl(z5_mul(PP, PM)) - z5fl(PHIP2)),
          abs(z5fl(PP) * z5fl(PM) - z5fl(PHIP2)))
info(f"FLOAT SANITY (non-load-bearing): zeta = e^(2 pi i/5) residuals "
     f"<= {res:.2e}; |pp| = {abs(z5fl(PP)):.10f} = D = "
     f"{(z5fl(PHIP2).real) ** 0.5:.10f}")

# ======================================================================
# R4 — T4: THE LAMBDA PARKING — ORDER 20, DEGREE 8, TORSION mu_10
# ======================================================================
print("=" * 72)
print("R4 — T4: lambda = zeta20^13, lambda*D = p+; why lambda cannot live in Z[zeta5]")
print("=" * 72)

# Z[zeta20] two ways: certificate's unrolled fold [G:W5g] vs generic
# polynomial remainder mod Phi20 = x^8 - x^6 + x^4 - x^2 + 1.
def c20_mul_gift(u, v):
    c = [0] * 15
    for i in range(8):
        if u[i] == 0: continue
        for j in range(8):
            c[i + j] += u[i] * v[j]
    for k in range(14, 7, -1):
        t = c[k]
        if t:
            c[k - 2] += t; c[k - 4] -= t; c[k - 6] += t; c[k - 8] -= t
        c[k] = 0
    return tuple(c[:8])
PHI20 = [1, 0, -1, 0, 1, 0, -1, 0, 1]        # x^8 - x^6 + x^4 - x^2 + 1 (low->high)
def c20_mul_mine(u, v):
    c = [0] * 15
    for i in range(8):
        for j in range(8):
            c[i + j] += u[i] * v[j]
    for d in range(14, 7, -1):               # generic monic remainder
        lead = c[d]
        if lead:
            for k in range(9):
                c[d - 8 + k] -= lead * PHI20[k]
    return tuple(c[:8])
C1 = (1, 0, 0, 0, 0, 0, 0, 0)
Z20 = (0, 1, 0, 0, 0, 0, 0, 0)
race20 = all(c20_mul_gift(u, v) == c20_mul_mine(u, v)
             for u, v in ((tuple(random.randint(-9, 9) for _ in range(8)),
                           tuple(random.randint(-9, 9) for _ in range(8)))
                          for _ in range(300)))
check("R4a_C20_raced", race20,
      "certificate's Z[zeta20] fold [G:W5g] vs a generic poly-remainder "
      "implementation: equal on 300 random pairs")
pw = [C1]
for _ in range(21):
    pw.append(c20_mul_mine(pw[-1], Z20))
phi20_at = c20_mul_mine(pw[4], pw[4])        # z^8
phi20_val = tuple(a - b + c - d + e for a, b, c, d, e in
                  zip(pw[8], pw[6], pw[4], pw[2], pw[0]))
phi20_num = abs(sum(c * cmath.exp(1j * pi / 10) ** k
                    for k, c in enumerate(PHI20)))
check("R4b_C20_ring",
      pw[20] == C1 and pw[10] == tuple(-a for a in C1) and
      all(pw[j] != C1 for j in range(1, 20)) and
      phi20_val == (0,) * 8 and phi20_num < 1e-12,
      "zeta20^20 = 1, zeta20^10 = -1, primitive (no earlier power hits 1); "
      "Phi20(zeta20) = 0 in-ring AND |Phi20(e^{i pi/10})| < 1e-12 "
      "numerically.  STANDARD FACT cited: Phi20 is irreducible over Q, so "
      "this 8-tuple ring IS Z[e^{i pi/10}] faithfully")
emb5 = lambda u: tuple(sum(u[i] * pw[4 * i][k] for i in range(4))
                       for k in range(8))
c20_add = lambda u, v: tuple(a + b for a, b in zip(u, v))
hom20 = c20_add(c20_add(C1, c20_add(pw[4], pw[8])),
                c20_add(pw[12], pw[16])) == (0,) * 8 and \
    all(emb5(z5_mul(u, v)) == c20_mul_mine(emb5(u), emb5(v))
        for u, v in ((tuple(random.randint(-9, 9) for _ in range(4)),
                      tuple(random.randint(-9, 9) for _ in range(4)))
                     for _ in range(200)))
check("R4c_zeta5_embeds", hom20,
      "zeta5 := zeta20^4: 1 + z^4 + z^8 + z^12 + z^16 = 0 and Z5 -> C20 "
      "multiplicative on 200 random pairs — Q(zeta5) sits inside Q(zeta20)")

D20 = c20_add(pw[1], pw[19])
D20sq = c20_mul_mine(D20, D20)
D20_4 = c20_mul_mine(D20sq, D20sq)
minpoly_D = c20_add(c20_add(D20_4, tuple(-5 * a for a in D20sq)),
                    tuple(5 * a for a in C1))
conj20 = lambda u: tuple(sum(u[j] * pw[(19 * j) % 20][k] for j in range(8))
                         for k in range(8))
Dfl = sum(c * cmath.exp(1j * pi * k / 10) for k, c in enumerate(D20)).real
check("R4d_D_element",
      D20sq == emb5(PHIP2) and minpoly_D == (0,) * 8 and
      conj20(D20) == D20 and abs(Dfl - (z5fl(PHIP2).real) ** 0.5) < 1e-12,
      f"D := zeta20 + zeta20^-1: D^2 = phi+2 exactly, D^4 - 5 D^2 + 5 = 0, "
      f"conj-fixed (real); numerically D = {Dfl:.10f} = +sqrt(phi+2) — "
      "the POSITIVE root (positivity is the one analytic fact, checked as "
      "a labelled float, exactly as the file's adjudicator excludes it)")

LAM = pw[13]
lam_pows = [C1]
for _ in range(20):
    lam_pows.append(c20_mul_mine(lam_pows[-1], LAM))
order = next(k for k in range(1, 21) if lam_pows[k] == C1)
check("R4e_lambda_D_eq_pp",
      c20_mul_mine(LAM, D20) == emb5(PP) and
      c20_mul_gift(LAM, D20) == emb5(PP),
      "lambda * D = p+ EXACTLY in Z[zeta20], re-verified with BOTH "
      "multiplication routes [G:W5k re-run] — the central-charge identity "
      "lambda = p+/D, integral")
check("R4f_mirror_index",
      c20_mul_mine(pw[7], D20) == emb5(PM) and
      c20_mul_mine(pw[7], D20) != emb5(PP) and
      conj20(LAM) == pw[7],
      "zeta20^7 * D = p- and NOT p+; conj(zeta20^13) = zeta20^7 — the "
      "mirror chirality, index load-bearing [G:W5l re-run]")
check("R4g_lambda_order_20",
      order == 20 and lam_pows[10] == tuple(-a for a in C1) and
      lam_pows[4] == emb5(ZT3),
      "order(lambda) = 20 exactly (first power hitting 1 is the 20th); "
      "lambda^10 = -1; lambda^4 = zeta20^52 = zeta20^12 = zeta5^3 = "
      "theta_tau — lambda's 4th power IS the twist (the content pp^4 = "
      "theta (phi+2)^2 clears)")

# --- the DEGREE obstruction, arithmetic: rank of the first five powers ---
def rank_frac(rows):
    A = [[Fr(x) for x in r] for r in rows]
    m, n = len(A), len(A[0]); r = 0
    for col in range(n):
        piv = next((i for i in range(r, m) if A[i][col] != 0), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][col]
        A[r] = [e / pv for e in A[r]]
        for i in range(m):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [ei - f * ej for ei, ej in zip(A[i], A[r])]
        r += 1
        if r == m: break
    return r
rk = rank_frac([list(lam_pows[k]) for k in range(5)])
check("R4h_degree_obstruction_rank",
      rk == 5,
      "rank_Q{1, lambda, lambda^2, lambda^3, lambda^4} = 5 in Q^8: lambda "
      "satisfies NO rational polynomial of degree <= 4.  But EVERY element "
      "of Q(zeta5) does — five powers are five vectors in the 4-dimensional "
      "Q(zeta5), always dependent.  So lambda is not in Q(zeta5), a fortiori "
      "not in Z[zeta5]: the degree-8-vs-4 obstruction as one rank computation")
# demonstrate the Q(zeta5) side concretely: five powers ARE dependent there
def nullvec_frac(rows):
    # rows: k vectors of length n with k > rank; return rational combo = 0
    import itertools
    k = len(rows); n = len(rows[0])
    A = [[Fr(rows[i][j]) for i in range(k)] for j in range(n)]   # n x k
    piv_cols, r = [], 0
    for col in range(k):
        piv = next((i for i in range(r, n) if A[i][col] != 0), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][col]
        A[r] = [e / pv for e in A[r]]
        for i in range(n):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [ei - f * ej for ei, ej in zip(A[i], A[r])]
        piv_cols.append(col); r += 1
    free = [c for c in range(k) if c not in piv_cols][0]
    v = [Fr(0)] * k; v[free] = Fr(1)
    for i, c in enumerate(piv_cols):
        v[c] = -A[i][free]
    return v
dep_ok = True
for x in [PP, PM, Z5PHI, ZT, z5_add(ZT, z5_mul((2, 0, 0, 0), Z5PHI)),
          tuple(random.randint(-9, 9) for _ in range(4))]:
    pows = [Z51]
    for _ in range(4):
        pows.append(z5_mul(pows[-1], x))
    v = nullvec_frac([list(p) for p in pows])
    den = 1
    for c in v: den = den * c.denominator // __import__("math").gcd(den, c.denominator)
    ints = [int(c * den) for c in v]
    acc = Z50
    for k, ck in enumerate(ints):
        acc = z5_add(acc, z5_mul((ck, 0, 0, 0), pows[k]))
    dep_ok = dep_ok and acc == Z50 and any(ints)
check("R4i_every_Z5_element_deg_le_4", dep_ok,
      "for x in {pp, pm, phi, zeta, zeta+2phi, random}: an explicit nonzero "
      "integer relation c0 + c1 x + ... + c4 x^4 = 0 found and VERIFIED in "
      "Z5 arithmetic — the degree <= 4 side of R4h, witnessed, not cited")

# --- the TORSION route: mu_10 by bounded search + the standard fact ---
sols = []
for u in product(range(-3, 4), repeat=4):
    x2 = z5_mul(u, u); x4 = z5_mul(x2, x2); x5 = z5_mul(x4, u)
    x10 = z5_mul(x5, x5)
    if z5_mul(x10, x10) == Z51:
        sols.append((u, x10))
mu10 = set()
zp_ = Z51
for k in range(5):
    mu10.add(zp_); mu10.add(z5_neg(zp_))
    zp_ = z5_mul(zp_, ZT)
check("R4j_torsion_box_search",
      len(sols) == 10 and {s[0] for s in sols} == mu10 and
      all(s[1] == Z51 for s in sols),
      "x^20 = 1 solved over the coefficient box [-3,3]^4 (2401 elements): "
      "EXACTLY the 10 elements ±zeta^k, and every one already satisfies "
      "x^10 = 1.  STANDARD FACT cited for the full ring: the roots of "
      "unity of Q(zeta5) are exactly mu_10 (n odd => mu_2n); the box holds "
      "all of mu_10, so the search confirms the fact's face")
check("R4k_lambda_not_in_Z5_torsion",
      lam_pows[10] == tuple(-a for a in C1) and order == 20,
      "lambda^20 = 1 so lambda IS a root of unity; every root of unity in "
      "Z[zeta5] satisfies x^10 = 1 (R4j + standard fact) but lambda^10 = "
      "-1 != 1 — CONCLUSION: no element of Z[zeta5] equals lambda; the "
      "park is forced, by torsion as well as by degree (R4h)")
q4 = [x for x in mu10 if z5_mul(z5_mul(x, x), z5_mul(x, x)) == ZT3]
ordmap = {}
for x in q4:
    p, k = x, 1
    while p != Z51:
        p = z5_mul(p, x); k += 1
    ordmap[x] = k
check("R4l_fourth_root_subtlety",
      sorted(ordmap.values()) == [5, 10] and
      {x for x in q4} == {ZT2, z5_neg(ZT2)},
      "x^4 = theta_tau DOES have Z5 solutions — exactly ±zeta^2, of orders "
      "5 and 10 — so the 4th-power content alone cannot pin lambda; what "
      "no Z5 element has is x^4 = theta WITH order 20, which is lambda's. "
      "The park protects a genuinely finer invariant than the twist")

# --- the denominator-5 coordinate measurement, re-solved [G:W5m] ---
closed = c20_mul_mine(emb5((2, -1, 1, -2)), D20) == tuple(5 * a for a in Z20)
basis = [c20_mul_mine(emb5(z), d) for d in (C1, D20)
         for z in (Z51, ZT, ZT2, ZT3)]
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
coords = [A[r][8] for r in range(8)]
dens = sorted({c.denominator for c in coords})
check("R4m_denominator_5", closed and dens == [1, 5],
      f"5*zeta20 = D*(2 - zeta + zeta^2 - 2 zeta^3) verified INTEGRALLY; "
      f"solving zeta20 over the basis zeta5^i D^j gives denominators {dens} "
      "— zeta20 is not in the order Z[zeta5][D]; the measured surprise "
      "(their first draft predicted 2) reproduces [G:W5m re-run]")
# B-bite (norm 16): flipped Phi20 fold must break zeta^10 = -1
PHI20_BAD = [1, 0, 1, 0, -1, 0, 1, 0, 1]
def c20_mul_bad(u, v):
    c = [0] * 15
    for i in range(8):
        for j in range(8):
            c[i + j] += u[i] * v[j]
    for d in range(14, 7, -1):
        lead = c[d]
        if lead:
            for k in range(9):
                c[d - 8 + k] -= lead * PHI20_BAD[k]
    return tuple(c[:8])
pb = C1
for _ in range(10):
    pb = c20_mul_bad(pb, Z20)
check("R4n_BITE_wrong_modulus", pb != tuple(-a for a in C1),
      "planted defect: a sign-flipped modulus loses zeta20^10 = -1 — the "
      "C20 layer of this racer can fail (norm 16 bite #4)")

# ======================================================================
# R5 — T5: THE WRONG-S CONTROL — FAILS EXACTLY WHERE THE FILE SAYS
# ======================================================================
print("=" * 72)
print("R5 — T5: Mwrong (Hadamard): the failure set, measured exactly")
print("=" * 72)

MWRONG = {(ONE, ONE): ZP1, (ONE, TAU): ZP1,
          (TAU, ONE): ZP1, (TAU, TAU): zp_neg(ZP1)}        # [V:226-230]
DSQW = (2, 0)                                              # [V:233]
def verlNumWrong(a, b, c):                                 # [V:237-240] no invPhi
    return zp_add(
        zp_mul(zp_mul(MWRONG[(a, ONE)], MWRONG[(b, ONE)]), MWRONG[(c, ONE)]),
        zp_mul(zp_mul(MWRONG[(a, TAU)], MWRONG[(b, TAU)]), MWRONG[(c, TAU)]))
fails = [(a, b, c) for (a, b, c) in cells
         if verlNumWrong(a, b, c) != zp_mul(DSQW, (fuseMult(a, b, c), 0))]
check("R5a_fail_set_exact",
      fails == [(TAU, TAU, TAU)],
      f"the wrong-S cleared identity fails on EXACTLY {{(tau,tau,tau)}} "
      f"(measured fail set: {[''.join(names[x] for x in f) for f in fails]}) "
      "— precisely the one cell wrong_S_fails_ttt names [V:246-248], and "
      "no other: the other 7 cells all pass, so the file's singular "
      "'FAILS at cell (tau,tau,tau)' is exact, not merely an example")
check("R5b_failing_values",
      verlNumWrong(TAU, TAU, TAU) == (0, 0) and
      zp_mul(DSQW, (fuseMult(TAU, TAU, TAU), 0)) == (2, 0),
      "at (t,t,t): verlNumWrong = <0,0> vs D'^2 * fuseMult = <2,0> — the "
      "docstring's exact numerals ('<0,0> != <2,0>'), and N'_tt^t = 0/2 = 0 "
      "stays integral while wrong, as the file says [V:242-245]")
check("R5c_correct_S_same_cell",
      verlNum(TAU, TAU, TAU) == zp_mul(DSQ, (1, 0)) and
      verlNum(TAU, TAU, TAU) == DSQ,
      "the CORRECT S passes that same cell: verlNum(t,t,t) = D^2 = <2,1> "
      "[V:251-253 correct_S_passes_ttt] — the contrast pair holds")
check("R5d_anti_vacuity",
      fuseMult(ONE, ONE, TAU) == 0 and fuseMult(TAU, TAU, TAU) == 1 and
      fuseMult(TAU, TAU, ONE) == 1 and
      verlNum(TAU, TAU, ONE) == DSQ and verlNum(TAU, TAU, TAU) == DSQ and
      verlNum(ONE, ONE, TAU) == (0, 0),
      "fuseMult_nonconstant [V:256-257] and all six conjuncts of "
      "verlinde_anti_vacuity [V:262-267]: N_tt^1 = N_tt^t = 1, N_11^t = 0, "
      "verlNum = D^2 where mult 1, = 0 where mult 0")
NZ2 = {(a, b, c): 1 if (a + b) % 2 == c else 0 for (a, b, c) in cells}
z2_match = all(verlNumWrong(a, b, c) == zp_mul(DSQW, (NZ2[(a, b, c)], 0))
               for (a, b, c) in cells)
diff = [k for k in cells if NZ2[k] != fuseMult(*k)]
check("R5e_wrong_S_is_Z2",
      z2_match and diff == [(TAU, TAU, TAU)],
      "coherence with the certificate's W4g: the Hadamard S "
      "Verlinde-derives EXACTLY the Z2 fusion table (all 8 cells), and Z2 "
      "differs from Fibonacci only at (t,t,t) — the file's control and the "
      "gift's Z2-discrimination control are the same fact, met in the middle")

# ======================================================================
# R6 — T6: THE CIRCLE CLOSES — S-MATRIX INTEGERS vs ROUND-1 fuse
# ======================================================================
print("=" * 72)
print("R6 — T6: 8 Verlinde integers vs Anyon.lean round-1 fuse/countA")
print("=" * 72)

# Anyon.lean's own machinery, transcribed FROM ANYON.LEAN's text [A:54-57,
# 6545-6551] (R0d proved the fuse block byte-identical to Verlinde's copy):
def countA_anyon(a, lst):                # [A:6545-6547], Nat-valued
    n = 0
    for x in lst:
        n += 1 if a == x else 0
    return n
def fuse_anyon(a, b):                    # [A:54-57]
    if a == ONE: return [b]
    if b == ONE: return [a]
    return [ONE, TAU]
routeB = {k: countA_anyon(k[2], fuse_anyon(k[0], k[1])) for k in cells}

# Route A(i): cleared quotient verlNum/D^2 (computed in R2h); Route A(ii):
# the UNCLEARED Verlinde sum, entirely over Q(sqrt5) Fractions:
#   N_abc = (1/(phi+2)) * [ Ma1 Mb1 Mc1 / 1 + Mat Mbt Mct / phi ]
PHIQ = (Fr(1, 2), Fr(1, 2))
q5 = {ZP1: (Fr(1), Fr(0)), ZPPHI: PHIQ}
def q5_inv(p):
    n = p[0] * p[0] - 5 * p[1] * p[1]
    return (p[0] / n, -p[1] / n)
q5_addf = lambda p, q: (p[0] + q[0], p[1] + q[1])
MQ = {k: q5_of_zp(v) for k, v in MSEL.items()}
routeA2, a2_int = {}, True
inv_phi_q = q5_inv(PHIQ); inv_rad = q5_inv(q5_addf(PHIQ, (Fr(2), Fr(0))))
for (a, b, c) in cells:
    s = q5_mul(q5_mul(MQ[(a, ONE)], MQ[(b, ONE)]), MQ[(c, ONE)])
    t = q5_mul(q5_mul(q5_mul(MQ[(a, TAU)], MQ[(b, TAU)]), MQ[(c, TAU)]),
               inv_phi_q)
    tot = q5_mul(q5_addf(s, t), inv_rad)
    a2_int = a2_int and tot[1] == 0 and tot[0].denominator == 1
    routeA2[(a, b, c)] = int(tot[0]) if tot[1] == 0 and \
        tot[0].denominator == 1 else None
routeA1 = {k: fuseMult(*k) for k in cells}   # = R2h's unique quotient
tab = ",".join(str(routeA2[k]) for k in cells)
check("R6a_three_routes_agree",
      a2_int and all(routeA1[k] == routeA2[k] == routeB[k] for k in cells),
      f"all 8 cells, three routes: (A1) cleared Z[phi] quotient "
      f"verlNum/D^2, (A2) uncleared field sum over Q(sqrt5) Fractions, "
      f"(B) Anyon.lean round-1 fuse/countA — table ({tab}) = "
      "(1,0,0,1,0,1,1,1); the S-matrix hands back the round-1 grammar, "
      "end to end through two codebases")
NFUS = {(i, j): routeB[(i, TAU, j)] for i in (ONE, TAU) for j in (ONE, TAU)}
check("R6b_Nfus_receipts",
      NFUS == {(ONE, ONE): 0, (ONE, TAU): 1, (TAU, ONE): 1, (TAU, TAU): 1},
      "Nfus i j = countA j (fuse i tau) = [[0,1],[1,1]] — Anyon.lean's "
      "receipt matrix [A:6551-6557] reproduced from the same machinery")
# the round-5 hinge: phi is Nfus's positive eigenvalue; Verlinde's S is
# built FROM phi; so check Nfus (1, phi)^T = phi (1, phi)^T in Zp exactly.
v = {ONE: ZP1, TAU: ZPPHI}
eig = all(zp_add(zp_mul((NFUS[(i, ONE)], 0), v[ONE]),
                 zp_mul((NFUS[(i, TAU)], 0), v[TAU]))
          == zp_mul(ZPPHI, v[i]) for i in (ONE, TAU))
check("R6c_perron_hinge", eig,
      "Nfus (1,phi)^T = phi (1,phi)^T exactly in Z[phi] — the round-5 "
      "Perron eigenvalue (quantum_dimension_tau, [A:6737]) is the phi the "
      "S-matrix row (dims_from_S) carries: grammar -> Nfus -> phi -> S -> "
      "Verlinde -> grammar, every arrow recomputed in this run")

# ======================================================================
print("=" * 72)
npass = sum(1 for _, ok in results if ok)
nfail = len(results) - npass
print(f"RESULT: {npass}/{len(results)} PASS" +
      (f", {nfail} FAIL" if nfail else ""))
sys.exit(0 if nfail == 0 else 1)
