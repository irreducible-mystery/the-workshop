#!/usr/bin/env python3
"""r8s_k3_recompute.py -- ROUND-8 TERMINAL AUDIT, K3 (the coker seat).

Recompute the whole S6.5 story from scratch, binding to the Lean source:
  * transcribe M from `inCtx` in MagicSquare.lean (contexts r0 r1 r2 c0 c1 c2
    x cells row-major) and CHECK the source text of inCtx/inImage matches;
  * im(M) from all 2^9 = 512 assignments; |im M| = 32;
  * im(M) = ker(phi) for phi = the all-ones functional (even weight, y.v = 0);
  * b = (0,0,0,0,0,1) not in im(M); rank M = 5; rank [M|b] = 6 by elimination;
  * the quotient GF(2)^6 / im(M): exactly 2 classes, sizes 32+32=64, classes =
    fibres of phi (toZ2 well-defined), toZ2/fromZ2 mutually inverse, hom law;
  * emulate the Lean decls inImage / phiBits / image_iff_even / imageCount /
    b_not_in_image bit-for-bit over all 64 targets x 512 assignments;
  * left kernel = {0, all-ones} (S6 cross-check); no-global-section tie.
Standalone; stdlib only. Exit 0 = PASS, 1 = FAIL."""
import itertools, re, sys

LEAN = "/home/claude/workshop/lean/MagicSquare.lean"
fails = []
def check(label, ok):
    print(("  OK   " if ok else "  FAIL ") + label)
    if not ok: fails.append(label)

src = open(LEAN, encoding="utf-8").read()

# --- 0. bind to the source: inCtx and inImage as shipped ---------------------
check("source: inCtx rows are `.r0, i, _ => i == 0` .. `.c2, _, j => j == 2`",
      all(re.search(rf"\|\s*\.r{k},\s*i,\s*_\s*=>\s*i\s*==\s*{k}", src) for k in range(3)) and
      all(re.search(rf"\|\s*\.c{k},\s*_,\s*j\s*=>\s*j\s*==\s*{k}", src) for k in range(3)))
inimage_eqs = ("((a ⊻ b ⊻ c) == u0) && ((d ⊻ e ⊻ f) == u1) && ((g ⊻ h ⊻ i) == u2) &&\n"
               "    ((a ⊻ d ⊻ g) == u3) && ((b ⊻ e ⊻ h) == u4) && ((c ⊻ f ⊻ i) == u5)")
check("source: inImage's six parity equations are exactly rows/cols row-major", inimage_eqs in src)
inimage_block = re.search(r"def inImage .*?(?=\n/--|\ntheorem)", src, re.S)
check("source: inImage searches 9 free bits via anyB (scoped to its definition)",
      bool(inimage_block) and inimage_block.group(0).count("anyB fun") == 9)
check("source: phiV sums all six coordinates",
      "u .r0 ⊻ u .r1 ⊻ u .r2 ⊻ u .c0 ⊻ u .c1 ⊻ u .c2" in src)
check("source: bVec = mkY false false false false false true",
      "def bVec : Ctx → Bool := mkY false false false false false true" in src)

# --- 1. M transcribed from inCtx; the floor's M must be the same object ------
# contexts 0..5 = r0 r1 r2 c0 c1 c2 ; cells 0..8 row-major (i,j) -> 3i+j
M = [[0]*9 for _ in range(6)]
for i in range(3):
    for j in range(3):
        M[i][3*i+j] = 1        # row context i        (inCtx .r_i)
        M[3+j][3*i+j] = 1      # column context j     (inCtx .c_j)
b = (0,0,0,0,0,1)

def mul(Mm, v):  # GF(2) matrix * vector
    return tuple(sum(Mm[k][c]*v[c] for c in range(9)) % 2 for k in range(6))

# --- 2. the image from all 512 assignments -----------------------------------
image = set()
sols_b = 0
for v in itertools.product((0,1), repeat=9):
    u = mul(M, v)
    image.add(u)
    if u == b: sols_b += 1
check("|im M| = 32 (2^5)  [rank M = 5, computed]", len(image) == 32)
even = {u for u in itertools.product((0,1), repeat=6) if sum(u) % 2 == 0}
check("im M = ker(all-ones functional): exactly the 32 even-weight covectors (y.v = 0)",
      image == even)
check("b = (0,0,0,0,0,1) not in im M  [rank [M|b] = 6 side]", b not in image)
check("no global section <=> b outside im M: Mv = b has 0 of 512 solutions", sols_b == 0)

# --- 3. ranks by GF(2) elimination (the floor's computation, redone) ---------
def gf2_rank(rows):
    rows = [list(r) for r in rows]; r = 0; ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                rows[i] = [(x ^ y) for x, y in zip(rows[i], rows[r])]
        r += 1
    return r
check("gaussian rank M = 5", gf2_rank(M) == 5)
check("gaussian rank [M|b] = 6", gf2_rank([row + [bb] for row, bb in zip(M, b)]) == 6)
check("rank consistency: |im M| = 2^rank", len(image) == 2 ** gf2_rank(M))

# --- 4. the quotient GF(2)^6 / im(M) ----------------------------------------
V = list(itertools.product((0,1), repeat=6))
def vadd(u, w): return tuple(a ^ bb for a, bb in zip(u, w))
def rel(u, w): return vadd(u, w) in image          # cokerRel
def phi(u): return sum(u) % 2                      # phiV / the all-ones functional
# equivalence sanity (refl/symm/trans on all pairs/triples via the fibre law)
check("cokerRel u w <=> phi u = phi w, all 64x64 pairs (cokerRel_iff)",
      all(rel(u, w) == (phi(u) == phi(w)) for u in V for w in V))
classes = {}
for u in V: classes.setdefault(frozenset(w for w in V if rel(u, w)), []).append(u)
check("quotient has exactly 2 classes (coker_two_classes)", len(classes) == 2)
sizes = sorted(len(next(iter(c))) and len(c) for c in classes)
check("class sizes 32 + 32 = 64 (the tie)", sorted(len(c) for c in classes) == [32, 32]
      and sum(len(c) for c in classes) == 64)
check("classes are the two fibres of phi (toZ2 well-defined on classes)",
      all(len({phi(u) for u in members}) == 1 for members in classes.values()))
zero, ones_b = (0,)*6, b
check("[0] != [b]: the two classes are distinct (coker_classes_distinct / class_of_b_nonzero)",
      not rel(zero, ones_b))
# the iso: toZ2 = phi on representatives; fromZ2 0 -> [0], 1 -> [b]
def fromZ2(bit): return ones_b if bit else zero
check("toZ2 (fromZ2 bit) = bit, both bits (toZ2_fromZ2)",
      all(phi(fromZ2(t)) == t for t in (0, 1)))
check("fromZ2 (toZ2 u) ~ u for every covector (fromZ2_toZ2)",
      all(rel(fromZ2(phi(u)), u) for u in V))
check("hom law phi(u+w) = phi(u) xor phi(w), all 64x64 (toZ2_hom / phiV_vxor)",
      all(phi(vadd(u, w)) == (phi(u) ^ phi(w)) for u in V for w in V))
check("anti-vacuity: weight-2 covector (1,1,0,0,0,0) collapses to [0] (coker_identifies)",
      rel((1,1,0,0,0,0), zero))
check("negative control: e_r0 = (1,0,0,0,0,0) is NOT in [0] (coker_separates)",
      not rel((1,0,0,0,0,0), zero))

# --- 5. bit-level emulation of the Lean declarations -------------------------
def lean_inImage(u0,u1,u2,u3,u4,u5):
    # anyB over a..i of the six shipped equations (row-major a b c / d e f / g h i)
    return any(((a^bb^c)==u0) and ((d^e^f)==u1) and ((g^h^i)==u2) and
               ((a^d^g)==u3) and ((bb^e^h)==u4) and ((c^f^i)==u5)
               for a,bb,c,d,e,f,g,h,i in itertools.product((0,1), repeat=9))
def lean_phiBits(u0,u1,u2,u3,u4,u5): return u0^u1^u2^u3^u4^u5
check("emulated inImage(u) agrees with membership in im(M-from-inCtx), all 64 targets",
      all(lean_inImage(*u) == (u in image) for u in V))
check("image_iff_even: inImage u = not(phiBits u), all 64 targets x 512 assignments",
      all(lean_inImage(*u) == (not lean_phiBits(*u)) for u in V))
check("imageCount = 32 (imageCount_eq_32)", sum(1 for u in V if lean_inImage(*u)) == 32)
check("inImage(0,0,0,0,0,1) = false (b_not_in_image)", lean_inImage(0,0,0,0,0,1) == False)
check("phiBits additive in 12 bits (phiBits_xor), all 4096 pairs",
      all((lean_phiBits(*u) ^ lean_phiBits(*w)) ==
          lean_phiBits(*(a^bb for a,bb in zip(u,w))) for u in V for w in V))

# --- 6. S6 cross-check: the left kernel, and the dual pairing ----------------
lk = [y for y in V if all(sum(y[k]*M[k][c] for k in range(6)) % 2 == 0 for c in range(9))]
check("left kernel of M = {0, all-ones}, |ker| = 2 (kerCount_eq_two / ker_iff)",
      sorted(lk) == sorted([zero, (1,)*6]))
check("y = all-ones: y.M = 0 and y.b = 1 (cocycle_annihilates / twist_is_odd)",
      (1,)*6 in lk and sum(a*bb for a, bb in zip((1,)*6, b)) % 2 == 1)
check("duality tie: dim ker = 1 = dim coker; 2 classes = 2^1", len(lk) == 2 == len(classes))

print()
if fails:
    print(f"r8s_k3_recompute: FAIL ({len(fails)} failed)"); sys.exit(1)
print("r8s_k3_recompute: PASS  -- |im M| = 32, im M = ker phi (even weight), "
      "b outside, rank 5/6, coker = Z2 with [b] the nonzero class")
sys.exit(0)
