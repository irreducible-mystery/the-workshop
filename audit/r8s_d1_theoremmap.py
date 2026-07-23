#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d1_theoremmap.py -- terminal audit, check D1: the theorem-map.
#
# Spot-verifies 22 load-bearing citations from the capstone PROOFS.md
# theorem-map (and the charge's named ten): the theorem EXISTS, in the RIGHT
# file, and the STATEMENT supports the ledger's characterization (pinned by a
# statement-fragment that must appear within the declaration's first lines).
# Also re-derives the per-file theorem counts with the census rule
# (^theorem <name> ... with a ':' on the line) and checks them against the
# VIEW:transcript block and the headline 1,150 = 21+85+714+41+214+75.
#
# Standalone.  Run from anywhere:  python3 audit/r8s_d1_theoremmap.py
# Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()

fail = 0
def chk(ok, label, detail=""):
    global fail
    print(("  ok    " if ok else "  FAIL  ") + label + ((" -- " + detail) if detail else ""))
    if not ok: fail = 1

# (theorem, file, fragment-that-pins-the-characterization, what the ledger says)
CITES = [
 # the charge's named ten
 ("hexagon_exactly_two_sharp", "Anyon.lean", "KK.beq KK.rt rt' = false",
  "dichotomy + distinctness + both realized, in one statement (F2 repair)"),
 ("pentagon_iff", "Anyon.lean", "↔", "pentagon equivalent to the three relations (sufficiency+necessity)"),
 ("quantum_dimension_tau", "Anyon.lean", "Zp.pos lam = true → lam = Zp.phi",
  "unique positive eigenvalue of the fusion matrix is phi"),
 ("HY_swap_not_null", "Rigidity.lean", "qform HY swapDir = ⟨34,52⟩",
  "swap direction not null; value 34+52*phi > 0"),
 ("verlinde_cleared", "Verlinde.lean", "∀ a b c, Zp.mul Dsq (fuseZp a b c) = verlNum a b c",
  "D^2 * N = verlNum for all eight cells"),
 ("coker_two_classes", "MagicSquare.lean", "x = fromZ2 false ∨ x = fromZ2 true",
  "exactly two cokernel classes"),
 ("satCount_is_odd", "MagicSquare.lean", "satCount v % 2 = 1", "parity ceiling: satCount always odd"),
 ("converse_false", "Exchangeable.lean", "num p = num q ∧ counts p ≠ counts q",
  "converse of exchangeability honestly false at length 6"),
 ("tier3a_tier3b_same_anyon", "Anyon.lean", "FratK x y = KK.mul (KK.mul (lam x) (Fsymm x y)) (lamInv y)",
  "gauge equivalence: one anyon, two presentations"),
 ("hexagonCheck_conj", "Anyon.lean", "hexagonCheck kRng Fsymm (KK.conj r1) (KK.conj rt)",
  "naturality of the hexagon under Galois conjugation"),
 # twelve more chosen load-bearing ones
 ("eckmann_hilton", "Interchange.lean", "(∀ a b, n a b = m a b)",
  "shared-unit interchange ops are equal/comm/assoc"),
 ("units_agree", "Interchange.lean", "en = em", "the shared unit is forced, not assumed"),
 ("no_global_section", "MagicSquare.lean", "¬ GlobalSection v", "no global section"),
 ("image_iff_even", "MagicSquare.lean", "inImage u0 u1 u2 u3 u4 u5 = !(phiBits",
  "im(M) = ker phi exactly (even-weight covectors)"),
 ("imageCount_eq_32", "MagicSquare.lean", "imageCount = 32", "rank M = 5 computed (|im| = 2^5)"),
 ("b_not_in_image", "MagicSquare.lean", "inImage false false false false false true = false",
  "rank [M|b] = 6 (twist covector outside the image)"),
 ("toZ2_hom", "MagicSquare.lean", "toZ2 (Quotient.mk cokerSetoid (vxor u w))",
  "coker -> Z2 respects the group law"),
 ("pentagon_forces_golden", "Anyon.lean", "KK.add (KK.mul p p) p = KK.one",
  "pentagon forces q*r=p, p^2+p=1, s=-p"),
 ("yang_baxter", "Anyon.lean", "matMul kRng (matMul kRng B1 B2) B1", "B1B2B1 = B2B1B2 exactly"),
 ("HY_kernel_is_line", "Rigidity.lean", "w 2 = Zp.mul Zp.phi (w 1)",
  "null space is the line w1*(0,1,phi,0)"),
 ("norm_Dsq", "Verlinde.lean", "Zp.mul Dsq (Zp.conj Dsq) = ⟨5, 0⟩", "N(D^2) = 5, clearing forced"),
 ("rt_norm_one", "Anyon.lean", "KK.mul KK.rt (KK.conj KK.rt) = KK.one",
  "|r|=1 algebraic half: rt * conj(rt) = 1"),
]

print("== D1: theorem-map spot-verification (22 citations) ==")
srcs = {f: rd(f) for f in ["Interchange.lean","MagicSquare.lean","Anyon.lean",
                           "Exchangeable.lean","Rigidity.lean","Verlinde.lean"]}
for name, fn, frag, what in CITES:
    src = srcs[fn]
    m = re.search(r"^theorem %s\b" % re.escape(name), src, re.M)
    if not m:
        chk(False, "%s in %s" % (name, fn), "declaration not found"); continue
    window = src[m.start(): m.start() + 2200]
    chk(frag in window, "%s (%s)" % (name, fn),
        what if frag in window else "statement fragment missing: %r" % frag)
    # right-file uniqueness: not declared in any other of the six
    others = [g for g, s in srcs.items()
              if g != fn and re.search(r"^theorem %s\b" % re.escape(name), s, re.M)]
    if others: chk(False, "%s uniqueness" % name, "also in " + ",".join(others))

print("== D1: census-rule counts reproduce the view ==")
expected = {"Interchange.lean":21, "MagicSquare.lean":85, "Anyon.lean":714,
            "Exchangeable.lean":41, "Rigidity.lean":214, "Verlinde.lean":75}
tot = 0
for fn, want in expected.items():
    n = sum(1 for L in srcs[fn].splitlines()
            if re.match(r"^theorem [A-Za-z_0-9']+", L) and ":" in L)
    tot += n
    chk(n == want, "count %s" % fn, "counted %d, view says %d" % (n, want))
chk(tot == 1150, "TOTAL", "counted %d, headline says 1,150" % tot)
p = rd("PROOFS.md")
chk("**1,150 theorems**" in p and "**503 axiom-free**" in p,
    "headline states 1,150 / 503 (503 is the view's number; kernel-side, hash-stamped)")

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
