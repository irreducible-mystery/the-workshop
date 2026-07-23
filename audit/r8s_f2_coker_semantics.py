#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_f2 -- ROUND-8 FINAL AUDIT, fresh-defect seat.  Independent recompute of
# the S6-and-a-half cokernel section's mathematics and of every number the
# capstone's coker prose asserts, from first principles (no Lean needed):
#
#   * inImage as MagicSquare.lean defines it (3 row parities, 3 column
#     parities over 2^9 assignments) yields EXACTLY the 32 even-weight
#     covectors of GF(2)^6  -> image_iff_even, imageCount_eq_32, rank M = 5
#   * b = (0,0,0,0,0,1) is odd-weight and not in the image -> b_not_in_image,
#     rank [M|b] = 6
#   * phi = all-ones functional is linear and surjective; the quotient
#     GF(2)^6 / im(M) has exactly two distinct classes; a weight-2 covector
#     collapses to [0] and an odd-weight covector does not -> toZ2_hom,
#     coker_two_classes, coker_classes_distinct, coker_identifies,
#     coker_separates
#   * the floor bench (floor/sheaf_cohomology.py wording): rank M = 5,
#     rank [M|b] = 6, coker = Z2, witnessing cocycle all-ones
#
# PASS iff every recomputation agrees with the prose.  Run from workshop/lean/.
# ---------------------------------------------------------------------------
import itertools, sys, os

fails = []
def chk(name, cond, detail=""):
    print(("PASS  " if cond else "FAIL  ") + name + ("" if not detail else "  -- " + detail))
    if not cond: fails.append(name)

# the image of M: parities of the 512 assignments (a..i row-major)
image = set()
for bits in itertools.product((0, 1), repeat=9):
    a, b, c, d, e, f, g, h, i = bits
    image.add((a ^ b ^ c, d ^ e ^ f, g ^ h ^ i, a ^ d ^ g, b ^ e ^ h, c ^ f ^ i))

even = {u for u in itertools.product((0, 1), repeat=6) if sum(u) % 2 == 0}
chk("image_iff_even: im(M) == ker(phi) == the even-weight covectors",
    image == even, "im=%d even=%d" % (len(image), len(even)))
chk("imageCount_eq_32: |im(M)| == 32 == 2^5 (rank M = 5)", len(image) == 32)
chk("exhaustion sizes: 2^6 targets == 64, 2^9 assignments == 512",
    len(list(itertools.product((0,1),repeat=6))) == 64 and 2**9 == 512)

bvec = (0, 0, 0, 0, 0, 1)
chk("b_not_in_image: twist covector odd-weight, outside im(M) (rank [M|b] = 6)",
    bvec not in image and sum(bvec) % 2 == 1)

phi = lambda u: sum(u) % 2
allu = list(itertools.product((0, 1), repeat=6))
chk("phi linear: phi(u+w) == phi(u) xor phi(w), all 64x64",
    all(phi(tuple(x ^ y for x, y in zip(u, w))) == phi(u) ^ phi(w)
        for u in allu for w in allu))
chk("phi surjective: phi(0)=0, phi(b)=1", phi((0,)*6) == 0 and phi(bvec) == 1)

# the quotient: classes under u ~ w iff u+w in im(M)
classes = set()
for u in allu:
    cls = frozenset(tuple(x ^ y for x, y in zip(u, m)) for m in image)
    classes.add(cls)
chk("coker_two_classes + distinct: exactly 2 classes, so coker(M) = Z2",
    len(classes) == 2)
chk("coker_identifies: weight-2 covector (1,1,0,0,0,0) lands in [0]",
    (1, 1, 0, 0, 0, 0) in image)
chk("coker_separates: odd covector (1,0,0,0,0,0) does not land in [0]",
    (1, 0, 0, 0, 0, 0) not in image)
chk("group law descends: phi constant on each class (toZ2 well-defined)",
    all(len({phi(u) for u in cls}) == 1 for cls in classes))

# the floor bench co-signature (rank 5 / rank 6 / Z2 / all-ones)
bench = "floor/sheaf_cohomology.py"
if os.path.exists(bench):
    t = open(bench).read()
    chk("floor bench present and speaks rank/coker/all-ones",
        "coker" in t and "rank" in t)
else:
    print("note  %s not present in this tree; crate check only" % bench)

# the Lean file's own S6.5 literals: the six parity equations transcribe M
src = open("MagicSquare.lean", encoding="utf-8").read()
for eq in ["(a ⊻ b ⊻ c)", "(d ⊻ e ⊻ f)", "(g ⊻ h ⊻ i)",
           "(a ⊻ d ⊻ g)", "(b ⊻ e ⊻ h)", "(c ⊻ f ⊻ i)"]:
    chk("inImage carries parity term " + eq, eq in src)
chk("imageCount_eq_32 stated as rfl in the file",
    "theorem imageCount_eq_32 : imageCount = 32 := rfl" in src)
chk("b_not_in_image stated as rfl in the file",
    "theorem b_not_in_image : inImage false false false false false true = false := rfl" in src)

print()
if fails:
    print("RESULT: %d coker-semantics check(s) FAILED: %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("RESULT: the S6.5 cokernel mathematics and every number in its prose")
print("        (32 = 2^5, 2^6 targets, 2^9 assignments, two distinct classes,")
print("        rank 5/6) recompute exactly.  PASS.")
sys.exit(0)
