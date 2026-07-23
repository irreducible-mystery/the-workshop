#!/usr/bin/env python3
"""r7s_v2_semantics.py -- ROUND-7 SEAT: Verlinde.lean semantic audit
(checks V2, V3, V4, V5, V9 of the seat charge).

METHOD.  Every constant used here is PARSED OUT OF Verlinde.lean's source
text (grep the fact, not the name): the Zp/Z5 multiplication formulas, the
Msel/Mwrong case tables, Dsq/sqrt5/invPhi/conj, the Z5 constants
pp/pm/phiPlus2/thetaTau, the ShatT/ShatTmirror entries, and the verlNum
term shape.  The arithmetic is then re-executed in three INDEPENDENT ways:

  route A  the file's own cleared route: integer pairs / 4-tuples with the
           parsed reduction formulas (what the Lean kernel decides);
  route B  the un-cleared route: exact Fraction arithmetic in the tower
           Q(sqrt5)(D), D^2 = phi+2 -- the certificate's W4 route,
           re-implemented from scratch (no code shared with
           r7_gift_verlinde.py; this is the first-contact cross-check);
  route C  complex floats, zeta5 = e^{2 pi i/5}, D = sqrt(phi+2)
           (non-load-bearing sanity for Z5; tolerance 1e-9).

The lambda/c layer is checked ON THE LABEL ONLY (route B/C arithmetic about
zeta20), never claimed as a file theorem -- the file parks it, and
r7s_v1_structure.sh S6 verifies no zeta20 is constructed.

Exit 0 iff every PASS.  Usage: python3 audit/r7s_v2_semantics.py
"""
import sys, os, re, cmath
from fractions import Fraction as Fr
from math import pi, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "Verlinde.lean")
text = open(SRC, encoding="utf-8").read()

results = []
def check(name, ok, detail=""):
    results.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ======================================================================
# PARSE the facts out of the source
# ======================================================================
def parse_pair(name):
    m = re.search(r"def %s\s*:\s*Zp\s*:=\s*(?:Zp\.add Zp\.phi )?⟨(-?\d+),\s*(-?\d+)⟩" % name, text)
    return (int(m.group(1)), int(m.group(2))) if m else None

def parse_z5(name):
    m = re.search(r"def %s\s*:\s*Z5\s*:=\s*⟨(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)⟩" % name, text)
    return tuple(int(m.group(k)) for k in (1, 2, 3, 4)) if m else None

# Zp core (the mul line is byte-checked vs Anyon.lean by transcription.sh)
assert "u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n" in text
zp_mul = lambda u, v: (u[0]*v[0] + u[1]*v[1], u[0]*v[1] + u[1]*v[0] + u[1]*v[1])
zp_add = lambda u, v: (u[0]+v[0], u[1]+v[1])
zp_neg = lambda u: (-u[0], -u[1])
ZP_ZERO, ZP_ONE, ZP_PHI = (0, 0), (1, 0), (0, 1)
# Zp.conj formula from source
assert "def conj (u : Zp) : Zp := ⟨u.m + u.n, -u.n⟩" in text
zp_conj = lambda u: (u[0]+u[1], -u[1])
ZP_INVPHI = parse_pair("invPhi") or (-1, 1)
assert "def invPhi : Zp := ⟨-1, 1⟩" in text
SQRT5 = parse_pair("sqrt5"); assert SQRT5 == (-1, 2), SQRT5
# Dsq := Zp.add Zp.phi ⟨2, 0⟩
m = re.search(r"def Dsq : Zp := Zp\.add Zp\.phi ⟨(-?\d+), (-?\d+)⟩", text)
DSQ = zp_add(ZP_PHI, (int(m.group(1)), int(m.group(2))))
check("P0_parse_Dsq", DSQ == (2, 1), f"Dsq parsed as phi+⟨2,0⟩ = {DSQ} = 2+phi")

# Msel case table parsed from source
mm = re.search(r"def Msel : Anyon → Anyon → Zp\n((?:  \| .*\n)+)", text)
MS = {}
for ln in mm.group(1).strip().split("\n"):
    g = re.match(r"\s*\| \.(\w+), \.(\w+) => (.*)", ln)
    val = {"Zp.one": ZP_ONE, "Zp.phi": ZP_PHI, "Zp.neg Zp.one": zp_neg(ZP_ONE)}[g.group(3).strip()]
    MS[(g.group(1), g.group(2))] = val
check("P1_parse_Msel", MS == {("one","one"):(1,0), ("one","tau"):(0,1),
                              ("tau","one"):(0,1), ("tau","tau"):(-1,0)},
      "M = [[1,phi],[phi,-1]] as Zp pairs, parsed from the case table")

mw = re.search(r"def Mwrong : Anyon → Anyon → Zp\n((?:  \| .*\n)+)", text)
MW = {}
for ln in mw.group(1).strip().split("\n"):
    g = re.match(r"\s*\| \.(\w+), \.(\w+) => (.*)", ln)
    val = {"Zp.one": ZP_ONE, "Zp.phi": ZP_PHI, "Zp.neg Zp.one": zp_neg(ZP_ONE)}[g.group(3).strip()]
    MW[(g.group(1), g.group(2))] = val
check("P2_parse_Mwrong", MW == {("one","one"):(1,0), ("one","tau"):(1,0),
                                ("tau","one"):(1,0), ("tau","tau"):(-1,0)},
      "Mwrong = Hadamard [[1,1],[1,-1]] parsed; DsqWrong ⟨2,0⟩ present: "
      + str("def DsqWrong : Zp := ⟨2, 0⟩" in text))

A = ["one", "tau"]

# fuse re-implemented from the (transcription-checked) source pattern
def fuse(a, b):
    if a == "one": return [b]
    if b == "one": return [a]
    return ["one", "tau"]
def fuseMult(a, b, c):           # the file: (fuse a b).countP (x = c)
    return sum(1 for x in fuse(a, b) if x == c)

# verlNum exactly as the file's term:  (Ma1*Mb1)*Mc1 + ((Mat*Mbt)*Mct)*invPhi
assert re.search(r"def verlNum \(a b c : Anyon\) : Zp :=\n  Zp\.add\n"
                 r"    \(Zp\.mul \(Zp\.mul \(Msel a \.one\) \(Msel b \.one\)\) \(Msel c \.one\)\)\n"
                 r"    \(Zp\.mul \(Zp\.mul \(Zp\.mul \(Msel a \.tau\) \(Msel b \.tau\)\) \(Msel c \.tau\)\) Zp\.invPhi\)", text), \
    "verlNum term shape drifted from what this audit checks"
def verlNum(a, b, c, M=MS):
    t1 = zp_mul(zp_mul(M[(a,"one")], M[(b,"one")]), M[(c,"one")])
    t2 = zp_mul(zp_mul(zp_mul(M[(a,"tau")], M[(b,"tau")]), M[(c,"tau")]), ZP_INVPHI)
    return zp_add(t1, t2)
def verlNumWrong(a, b, c):       # both weights 1, per the file
    t1 = zp_mul(zp_mul(MW[(a,"one")], MW[(b,"one")]), MW[(c,"one")])
    t2 = zp_mul(zp_mul(MW[(a,"tau")], MW[(b,"tau")]), MW[(c,"tau")])
    return zp_add(t1, t2)

# ======================================================================
# V2/V3 -- the Zp core, route A (the kernel's own arithmetic)
# ======================================================================
print("=" * 72)
print("Zp CORE -- route A: the file's cleared arithmetic, re-executed")
print("=" * 72)
check("A1_sqrt5_sq", zp_mul(SQRT5, SQRT5) == (5, 0), "(2phi-1)^2 = 5")
check("A2_Dsq_eq_sqrt5_phi", DSQ == zp_mul(SQRT5, ZP_PHI), "phi+2 = sqrt5*phi")
check("A3_norm_Dsq", zp_mul(DSQ, zp_conj(DSQ)) == (5, 0) and zp_conj(DSQ) == (3, -1),
      "N(D^2) = (phi+2)(3-phi) = 5; conj(Dsq) = ⟨3,-1⟩  => D^2 is a NON-UNIT (5 not invertible in Z)")
check("A4_invPhi_unit", zp_mul(ZP_PHI, ZP_INVPHI) == ZP_ONE,
      "phi*(phi-1) = 1: phi IS a unit -- the /phi in the Verlinde weight is legitimate")
check("A5_M_symm", all(MS[(i,j)] == MS[(j,i)] for i in A for j in A), "M symmetric")
Msq = {(i,j): zp_add(zp_mul(MS[(i,"one")], MS[("one",j)]), zp_mul(MS[(i,"tau")], MS[("tau",j)]))
       for i in A for j in A}
check("A6_M_sq", all(Msq[(i,j)] == (DSQ if i == j else ZP_ZERO) for i in A for j in A),
      "M^2 = D^2 I entrywise (the cleared S^2 = I)")
rd = {(i,j): zp_add(zp_mul(MS[(i,"one")], MS[(j,"one")]), zp_mul(MS[(i,"tau")], MS[(j,"tau")]))
      for i in A for j in A}
check("A7_rows_orthonormal", all(rd[(i,j)] == (DSQ if i == j else ZP_ZERO) for i in A for j in A),
      "row_i . row_j = D^2 delta_ij")
check("A8_dims_from_S", MS[("one","one")] == ZP_ONE and MS[("one","tau")] == ZP_PHI,
      "M_00 = 1, M_0tau = phi: S_0a/S_00 = (1, phi) -- the d_tau = phi READING "
      "(file cites quantum_dimension_tau, Anyon.lean:6737; a co-signature, definitional on M)")

# fuseMult table + the headline
NF = {(a,b,c): fuseMult(a,b,c) for a in A for b in A for c in A}
check("A9_fuseMult_from_fuse",
      [NF[(a,b,c)] for a in A for b in A for c in A] == [1,0,0,1,0,1,1,1],
      "8-cell multiplicity table COMPUTED from fuse (1,0,0,1,0,1,1,1) -- not asserted")
cells = {(a,b,c): (zp_mul(DSQ, (NF[(a,b,c)], 0)), verlNum(a,b,c)) for a in A for b in A for c in A}
check("A10_verlinde_cleared_8cells",
      all(l == r for l, r in cells.values()),
      "D^2 * fuseMult a b c = verlNum a b c holds in ALL 8 cells "
      + str({k: v[0] for k, v in cells.items()}))
check("A11_wrong_S_fails_ttt",
      verlNumWrong("tau","tau","tau") != zp_mul((2,0), (NF[("tau","tau","tau")], 0))
      and verlNumWrong("tau","tau","tau") == (0,0),
      "Hadamard S: verlNumWrong(t,t,t) = 0 != 2 = D'^2*fuseMult -- the negative control bites")
check("A12_anti_vacuity",
      NF[("tau","tau","one")] == 1 and NF[("tau","tau","tau")] == 1
      and NF[("one","one","tau")] == 0
      and verlNum("tau","tau","one") == DSQ and verlNum("tau","tau","tau") == DSQ
      and verlNum("one","one","tau") == ZP_ZERO,
      "N_tt^1 = N_tt^t = 1, N_11^t = 0; verlNum = D^2 / D^2 / 0 at those cells")

# ======================================================================
# V2 -- route B: the UN-cleared Verlinde in exact Q(sqrt5)(D)
# (independent re-implementation of the certificate's route; float-free)
# ======================================================================
print("=" * 72)
print("Zp CORE -- route B: exact 1/D arithmetic in Q(sqrt5)(D), from scratch")
print("=" * 72)
# Q(sqrt5) as (a, b) = a + b*sqrt5 over Fraction; then Q5(D) as (x, y) = x + y*D
q5m = lambda u, v: (u[0]*v[0] + 5*u[1]*v[1], u[0]*v[1] + u[1]*v[0])
q5a = lambda u, v: (u[0]+v[0], u[1]+v[1])
q5inv = lambda u: ((u[0]/(u[0]*u[0]-5*u[1]*u[1])), (-u[1]/(u[0]*u[0]-5*u[1]*u[1])))
PHI_Q = (Fr(1,2), Fr(1,2)); RAD = q5a(PHI_Q, (Fr(2), Fr(0)))       # phi+2
qdm = lambda u, v: (q5a(q5m(u[0], v[0]), q5m(RAD, q5m(u[1], v[1]))),
                    q5a(q5m(u[0], v[1]), q5m(u[1], v[0])))
qda = lambda u, v: (q5a(u[0], v[0]), q5a(u[1], v[1]))
def qdinv(u):
    n = q5a(q5m(u[0], u[0]), tuple(-x for x in q5m(RAD, q5m(u[1], u[1]))))
    ni = q5inv(n)
    return (q5m(u[0], ni), tuple(-x for x in q5m(u[1], ni)))
Z_Q = ((Fr(0), Fr(0)), (Fr(0), Fr(0)))
def emb(q5):  return (q5, (Fr(0), Fr(0)))
INVD = ((Fr(0), Fr(0)), q5inv(RAD))                                 # 1/D = D/(phi+2)
u5 = {("one","one"): (Fr(1), Fr(0)), ("one","tau"): PHI_Q,
      ("tau","one"): PHI_Q, ("tau","tau"): (Fr(-1), Fr(0))}
S = {k: qdm(INVD, emb(v)) for k, v in u5.items()}                   # true S = M/D
ok_int, okN, tbl = True, True, {}
for a in A:
    for b in A:
        for c in A:
            tot = Z_Q
            for x in A:
                t = qdm(qdm(qdm(S[(a,x)], S[(b,x)]), S[(c,x)]), qdinv(S[("one",x)]))
                tot = qda(tot, t)
            xpart, ypart = tot
            isZ = ypart == (Fr(0), Fr(0)) and xpart[1] == 0 and xpart[0].denominator == 1
            ok_int = ok_int and isZ
            tbl[(a,b,c)] = xpart[0]
            okN = okN and isZ and xpart[0] == NF[(a,b,c)]
check("B1_uncleared_lands_in_Z", ok_int,
      "sum_x S_ax S_bx S_cx / S_0x is an exact INTEGER in all 8 cells (1/D arithmetic, no floats)")
check("B2_uncleared_equals_fuse", okN,
      "and equals fuseMult everywhere: " + str([int(tbl[(a,b,c)]) for a in A for b in A for c in A]))
# the /phi-as-unit bridge: verlNum == D^2 * (uncleared N), certified by comparing
# the CLEARED tau-term against the un-cleared tau-term times D^2 termwise
okT = True
for a in A:
    for b in A:
        for c in A:
            t_unc = qdm(qdm(qdm(S[(a,"tau")], S[(b,"tau")]), S[(c,"tau")]), qdinv(S[("one","tau")]))
            D2 = emb(RAD)
            lhsq = qdm(D2, t_unc)                       # D^2 * (S S S / S_0tau)
            v = zp_mul(zp_mul(zp_mul(MS[(a,"tau")], MS[(b,"tau")]), MS[(c,"tau")]), ZP_INVPHI)
            # embed the Zp pair m+n*phi into Q5: (m + n/2, n/2)
            vq = (Fr(v[0]) + Fr(v[1], 2), Fr(v[1], 2))
            okT = okT and lhsq[1] == (Fr(0), Fr(0)) and lhsq[0] == vq
check("B3_invPhi_is_the_cleared_weight", okT,
      "termwise: D^2 * (S_at S_bt S_ct / S_0t) == (M_at M_bt M_ct) * invPhi in Q(sqrt5) "
      "-- the file's invPhi factor IS the cleared 1/S_0tau, phi treated as the unit it is")

# certificate agreement (W4d shape): sum_x Shat Shat Shat w_x = N*(phi+2)
W = {"one": (1, 0), "tau": ZP_INVPHI}
okC = True
for a in A:
    for b in A:
        for c in A:
            lhs = (0, 0)
            for x in A:
                lhs = zp_add(lhs, zp_mul(zp_mul(MS[(a,x)], MS[(b,x)]), zp_mul(MS[(c,x)], W[x])))
            okC = okC and lhs == zp_mul((NF[(a,b,c)], 0), DSQ) and lhs == verlNum(a,b,c)
check("B4_certificate_W4d_shape", okC,
      "the letter/certificate's cleared equation (weights w = (1, invPhi)) equals the file's "
      "verlNum in every cell -- first contact between the two routes AGREES")

# ======================================================================
# V4 -- the Z5 T-layer, route A (parsed constants, file arithmetic)
# ======================================================================
print("=" * 72)
print("Z5 T-LAYER -- route A: the file's Z[zeta5] arithmetic, re-executed")
print("=" * 72)
assert "c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4" in text   # transcription-checked line
def z5m(u, v):
    c0 = u[0]*v[0]; c1 = u[0]*v[1]+u[1]*v[0]; c2 = u[0]*v[2]+u[1]*v[1]+u[2]*v[0]
    c3 = u[0]*v[3]+u[1]*v[2]+u[2]*v[1]+u[3]*v[0]
    c4 = u[1]*v[3]+u[2]*v[2]+u[3]*v[1]; c5 = u[2]*v[3]+u[3]*v[2]; c6 = u[3]*v[3]
    return (c0-c4+c5, c1-c4+c6, c2-c4, c3-c4)
z5a = lambda u, v: tuple(a+b for a, b in zip(u, v))
z5n = lambda u: tuple(-a for a in u)
assert "def conj (u : Z5) : Z5 := ⟨u.a0 - u.a1, -u.a1, u.a3 - u.a1, u.a2 - u.a1⟩" in text
z5c = lambda u: (u[0]-u[1], -u[1], u[3]-u[1], u[2]-u[1])
O5, I5 = (0,0,0,0), (1,0,0,0)
Z, Z2, Z3, Z4 = (0,1,0,0), (0,0,1,0), (0,0,0,1), (-1,-1,-1,-1)
PHI5 = parse_z5("phi") or (0,0,-1,-1)
INVPHI5 = parse_z5("invPhi") or (-1,0,-1,-1)
PP  = parse_z5("pp");        PM = parse_z5("pm")
PH2 = parse_z5("phiPlus2")
check("C0_parse_Z5_constants", PP == (0,-1,0,1) and PM == (1,1,2,1) and PH2 == (2,0,-1,-1),
      f"pp={PP} pm={PM} phiPlus2={PH2} parsed from source (= certificate W5c/W5e/W5d constants)")

check("C1_receipts", z5m(Z3, Z) == Z4 and z5m(Z4, Z) == I5
      and z5a(z5a(I5, Z), Z4) == PHI5 and z5a(Z, Z4) == INVPHI5
      and z5m(PHI5, INVPHI5) == I5 and z5m(PHI5, PHI5) == z5a(PHI5, I5),
      "zeta reduction + phi receipts (z5_zeta4_eq .. z5_phi_sq) all recompute")
check("C2_conj_receipts", z5c(Z) == Z4 and z5c(Z2) == Z3 and z5c(Z3) == Z2
      and z5c(Z4) == Z and z5c(PHI5) == PHI5 and z5c(INVPHI5) == INVPHI5,
      "conj: zeta<->zeta4, zeta2<->zeta3, fixes phi and 1/phi")
TH = Z3   # thetaTau := Z5.zeta3
check("C3_ribbon_cosign", z5a(z5m(Z2, INVPHI5), z5n(Z)) == TH,
      "zeta^2*(1/phi) - zeta = zeta^3: thetaTau_ribbon recomputes (co-sign of Anyon.lean:414 "
      "ribbon_twist, whose constants r1=zeta^2, rt=-zeta, theta=zeta^3 were grepped in Anyon.lean)")
check("C4_pp_pm_defs", PP == z5a(Z3, z5n(Z)) and PM == z5a(Z2, z5n(Z4)) and PM == z5c(PP),
      "pp = zeta^3 - zeta, pm = zeta^2 - zeta^4 = conj(pp): the mirror IS complex conjugation")
check("C5_phiPlus2_is_D2", PH2 == z5a(PHI5, (2,0,0,0)) and PH2 == z5a(z5m(PHI5, PHI5), I5),
      "phi+2 = phi^2+1 = D^2 in Z5")

# ShatT parsed and cubed with the file's Mat2.mul (row-by-column over Z5)
assert "def ShatT : Mat2 := ⟨Z5.one, Z5.mul Z5.phi Z5.zeta3, Z5.phi, Z5.neg Z5.zeta3⟩" in text
assert "def ShatTmirror : Mat2 := ⟨Z5.one, Z5.mul Z5.phi Z5.zeta2, Z5.phi, Z5.neg Z5.zeta2⟩" in text
def mat_mul(Mx, Nx):
    a, b, c, d = Mx; e, f, g, h = Nx
    return (z5a(z5m(a, e), z5m(b, g)),
            z5a(z5m(a, f), z5m(b, h)),
            z5a(z5m(c, e), z5m(d, g)),
            z5a(z5m(c, f), z5m(d, h)))
ST  = (I5, z5m(PHI5, Z3), PHI5, z5n(Z3))
STm = (I5, z5m(PHI5, Z2), PHI5, z5n(Z2))
SC  = z5m(PH2, PP); SCm = z5m(PH2, PM)
cube  = mat_mul(mat_mul(ST, ST), ST)
cubem = mat_mul(mat_mul(STm, STm), STm)
check("C6_modular_cube", cube == (SC, O5, O5, SC),
      f"(ShatT)^3 = (phi+2)*pp * I exactly; scalar = {SC}")
check("C7_modular_cube_mirror", cubem == (SCm, O5, O5, SCm),
      f"(ShatT')^3 = (phi+2)*pm * I exactly; scalar = {SCm}")
check("C8_pp_pm_eq_D2", z5m(PP, PM) == PH2,
      "pp*pm = phi+2 = D^2 (the cleared |lambda|=1)")
check("C9_pp_pow4", z5m(z5m(PP,PP), z5m(PP,PP)) == z5m(TH, z5m(PH2, PH2)),
      "pp^4 = theta_tau*(phi+2)^2 (the cleared lambda^4 = theta_tau)")
check("C10_pm_pow4", z5m(z5m(PM,PM), z5m(PM,PM)) == z5m(Z2, z5m(PH2, PH2)),
      "pm^4 = zeta^2*(phi+2)^2 = conj-law mirror")
# Part 4: the balancing identities
d5 = {"one": I5, "tau": PHI5}; th5 = {"one": I5, "tau": TH}
sh5 = {("one","one"): I5, ("one","tau"): PHI5, ("tau","one"): PHI5, ("tau","tau"): z5n(I5)}
def rhs_bal(a, b):
    tot = O5
    for c in A:
        n = NF[(a,b,c)]
        if n:
            tot = z5a(tot, z5m(z5m((n,0,0,0), d5[c]), th5[c]))
    return tot
ok11 = z5m(z5m(sh5[("one","one")], th5["one"]), th5["one"]) == rhs_bal("one","one")
ok1t = z5m(z5m(sh5[("one","tau")], th5["one"]), th5["tau"]) == rhs_bal("one","tau")
oktt = z5m(z5m(sh5[("tau","tau")], th5["tau"]), th5["tau"]) == rhs_bal("tau","tau")
lhs_tt = z5m(z5m(z5n(I5), TH), TH)
check("C11_balancing_identities", ok11 and ok1t and oktt and lhs_tt == z5n(Z),
      "Shat_ab*theta_a*theta_b = sum_c N_ab^c d_c theta_c at (1,1),(1,t),(t,t); "
      "(t,t): -zeta^6 = -zeta = 1 + phi*zeta^3 -- imaginary parts cancel AS A RING IDENTITY")
check("C12_negative_controls", PP != PM and SC != SCm and TH != I5
      and z5m(z5m(z5m(z5m(Z3,Z3),Z3),Z3),Z3) == I5
      and PP != O5 and PH2 != O5 and SC != O5 and SC != PH2,
      "pp != pm; (phi+2)pp != (phi+2)pm; theta != 1 but theta^5 = 1; "
      "pp, phi+2, (phi+2)pp all nonzero; scalar carries pp")

# ======================================================================
# V4 -- route C: complex floats, and the PARKED lambda label arithmetic
# ======================================================================
print("=" * 72)
print("Z5/T -- route C: complex embedding zeta5 = e^{2 pi i/5} (sanity, 1e-9)")
print("=" * 72)
z5f = lambda u: sum(u[k] * cmath.exp(2j*pi*k/5) for k in range(4))
tol = 1e-9
phi_f = (1 + sqrt(5)) / 2
D_f = sqrt(phi_f + 2)
ok = (abs(z5f(PHI5) - phi_f) < tol and abs(z5f(PP) - (cmath.exp(6j*pi/5) - cmath.exp(2j*pi/5))) < tol
      and abs(z5f(PH2) - (phi_f + 2)) < tol and abs(z5f(TH) - cmath.exp(-4j*pi/5)) < tol)
check("D1_embedding_sanity", ok, "phi, pp, phi+2, theta_tau all embed to the right complex numbers")
Sf = [[1/D_f, phi_f/D_f], [phi_f/D_f, -1/D_f]]
Tf = [[1, 0], [0, cmath.exp(-4j*pi/5)]]
mmf = lambda X, Y: [[sum(X[i][k]*Y[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
ST3f = mmf(mmf(mmf(Sf, Tf), mmf(Sf, Tf)), mmf(Sf, Tf))
lam_f = cmath.exp(-7j*pi/10)                     # zeta20^13
dev = max(abs(ST3f[i][j] - lam_f*(1 if i == j else 0)) for i in range(2) for j in range(2))
check("D2_ST3_float", dev < tol,
      f"(S T)^3 = e^(-7 pi i/10) I to {dev:.1e}: the UN-cleared modular relation behind modular_cube")
check("D3_cleared_matches_uncleared",
      abs(z5f(SC) - lam_f * D_f**3) < 1e-8,
      "(phi+2)*pp == lambda*D^3 numerically: the file's cleared scalar is exactly D^3 * "
      "the uncleared scalar -- clearing bookkeeping verified")
# the PARKED LABEL, checked as arithmetic on the label (NOT a file theorem):
z20 = cmath.exp(1j*pi/10)
check("D4_lambda_label", abs(z20**13 * D_f - z5f(PP)) < tol and abs(z20**7 * D_f - z5f(PM)) < tol
      and abs(z20**13 - cmath.exp(2j*pi*Fr(-14,5)/8)) < tol,
      "LABEL ARITHMETIC (parked; no zeta20 in the file): zeta20^13*D = p+, zeta20^7*D = p-, "
      "and zeta20^13 = e^{2 pi i c/8} with c = -14/5 -- the c label is consistent")
check("D5_mirror_distinguished", abs(z20**13 - z20**7) > 0.5 and PP != PM,
      "zeta20^13 != zeta20^7 as numbers, and the file's CLEARED form distinguishes them: "
      "pp vs pm = conj pp (pm_eq_conj_pp), modular_cube vs modular_cube_mirror, "
      "cube_chirality_differs -- chirality is carried integrally")
check("D6_lambda4_content", abs(z20**52 - z5f(TH)) < tol,
      "lambda^4 = zeta20^52 = zeta5^3 = theta_tau: pp_pow4_eq pins exactly this, cleared")

# ======================================================================
# V9 -- HOSTILE MISREADING battery on verlinde_cleared
# ======================================================================
print("=" * 72)
print("V9 -- hostile misreading: can the cleared form be vacuous / wrong-S-true?")
print("=" * 72)
zero_cells = [(a,b,c) for a in A for b in A for c in A
              if NF[(a,b,c)] == 0 and verlNum(a,b,c) == ZP_ZERO]
nonz_cells = [(a,b,c) for a in A for b in A for c in A if verlNum(a,b,c) != ZP_ZERO]
check("H1_not_globally_vacuous", len(zero_cells) == 3 and len(nonz_cells) == 5,
      "3 cells reduce to 0 = 0 (multiplicity-0 cells), 5 cells assert the NONZERO identity "
      "D^2*1 = D^2; verlinde_anti_vacuity names both kinds -- the nest is not 0=0")
# uniqueness: over the domain Z[phi], D^2*k = verlNum pins k uniquely
ok_uni = True
for a in A:
    for b in A:
        for c in A:
            sols = [k for k in range(-3, 4) if zp_mul(DSQ, (k, 0)) == verlNum(a,b,c)]
            ok_uni = ok_uni and sols == [NF[(a,b,c)]]
check("H2_multiplicity_pinned", ok_uni,
      "for every cell, k in [-3..3] solving D^2*k = verlNum is UNIQUE and equals fuseMult "
      "(the integral-domain argument, checked concretely)")
# wrong-S: full failure profile of the Hadamard control under ITS OWN cleared form
fails = [(a,b,c) for a in A for b in A for c in A
         if verlNumWrong(a,b,c) != zp_mul((2,0), (NF[(a,b,c)], 0))]
check("H3_wrong_S_profile", ("tau","tau","tau") in fails and len(fails) == 1,
      f"Hadamard S fails its cleared identity at exactly {fails}: the single cell where "
      "Fibonacci differs from the Z2 table -- wrong_S_fails_ttt names the right cell, and "
      "correct_S_passes_ttt is its live contrast")
# wrong-fuse: plant the Z2 fusion table against the TRUE S
NZ2 = {(a,b,c): (1 if (A.index(a)+A.index(b)) % 2 == A.index(c) else 0)
       for a in A for b in A for c in A}
fails2 = [(a,b,c) for a in A for b in A for c in A
          if zp_mul(DSQ, (NZ2[(a,b,c)], 0)) != verlNum(a,b,c)]
check("H4_wrong_fuse_fails", fails2 == [("tau","tau","tau")],
      "planting the Z2/semion fusion table against the true S fails at exactly (t,t,t): "
      "the statement discriminates on the fuse side too")
# Galois-twin observation (REPORT, not a defect): conj everything, identity survives
MSc = {k: zp_conj(v) for k, v in MS.items()}
DSQc = zp_conj(DSQ); INVPHIc = zp_conj(ZP_INVPHI)
def verlNum_c(a, b, c):
    t1 = zp_mul(zp_mul(MSc[(a,"one")], MSc[(b,"one")]), MSc[(c,"one")])
    t2 = zp_mul(zp_mul(zp_mul(MSc[(a,"tau")], MSc[(b,"tau")]), MSc[(c,"tau")]), INVPHIc)
    return zp_add(t1, t2)
twin = all(zp_mul(DSQc, (NF[(a,b,c)],0)) == verlNum_c(a,b,c) for a in A for b in A for c in A)
check("H5_galois_twin_report", twin,
      "REPORT (expected, not a defect): the Galois-conjugate S (phi -> 1-phi, the Yang-Lee twin) "
      "ALSO satisfies the cleared Verlinde with the SAME fuse -- correct, since both Fibonacci "
      "categories share the fusion ring; the file claims S |- fuse, not uniqueness of S, and its "
      "norm-15 block says exactly that")
# scalar-shape attack: could verlNum be D^2 * (something independent of fuse)?
check("H6_rhs_nonconstant", len({verlNum(a,b,c) for a in A for b in A for c in A}) > 1
      and len({tuple(v) for v in [verlNum("tau","tau","one"), verlNum("one","one","one")]}) == 1,
      "verlNum takes multiple values across cells (not one scalar), matching multiplicities "
      "cell by cell -- the 8-cell nest is tied to fuse totals, not to a constant")

print("=" * 72)
npass = sum(results); nfail = len(results) - npass
print(f"RESULT: {npass}/{len(results)} PASS" + (f", {nfail} FAIL" if nfail else ""))
sys.exit(0 if nfail == 0 else 1)
