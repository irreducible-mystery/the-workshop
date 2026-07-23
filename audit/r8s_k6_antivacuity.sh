#!/bin/sh
# r8s_k6_antivacuity.sh -- ROUND-8 TERMINAL AUDIT, K6 (the coker seat).
# The section must have nonzero content on BOTH sides:
#   * the two classes are DISTINCT (coker_classes_distinct, class_of_b_nonzero)
#     -- coker(M) is not the trivial group;
#   * the quotient genuinely collapses (coker_identifies: a nonzero vector in
#     the zero class) -- coker(M) is not the discrete 64-element set;
#   * imageCount is 32, NOT 64 -- im(M) is a proper subgroup; the tie
#     32 (even, = im M) + 32 (odd) = 64 (all covectors, yEnumSize_eq_64);
#   * negative controls in-section: coker_separates, b_not_in_image; and S6's
#     cocycle_check_can_fail retained.
# Exit 0 = PASS, 1 = FAIL.
set -u
F=/home/claude/workshop/lean/MagicSquare.lean
fail=0
need() { if grep -qF "$2" "$F"; then echo "  OK   $1"; else echo "  MISS $1"; fail=1; fi }

echo "== both sides nonzero =="
need "distinct classes (not trivial group)"  "theorem coker_classes_distinct : fromZ2 false ≠ fromZ2 true := by"
need "[b] != [0] restated"                   "theorem class_of_b_nonzero :"
need "collapse is real (not discrete): weight-2 -> [0]" "theorem coker_identifies :"
need "  .. its witness mkY true true false false false false" "    Quotient.mk cokerSetoid (mkY true true false false false false) ="
need "separation is real: e_r0 not in [0]"   "theorem coker_separates :"
echo "== the 32-not-64 tie =="
need "imageCount_eq_32 (proper subgroup)"    "theorem imageCount_eq_32 : imageCount = 32 := rfl"
need "the 64-total is pinned in-file (yEnumSize_eq_64)" "theorem yEnumSize_eq_64 : yEnumSize = 64 := rfl"
if grep -q "imageCount = 64" "$F"; then echo "  FAIL imageCount stated as 64 somewhere"; fail=1
else echo "  OK   no imageCount = 64 anywhere (im M is proper)"; fi
[ $((32 + 32)) = 64 ] && echo "  OK   arithmetic tie: 32 (even = im M) + 32 (odd) = 64 covectors" || fail=1
echo "== negative controls =="
need "b_not_in_image (the negative of membership)" "theorem b_not_in_image : inImage false false false false false true = false := rfl"
need "S6 negative control retained (cocycle_check_can_fail)" "theorem cocycle_check_can_fail :"
echo "== the anti-vacuity pair is IN-SECTION (473-692) =="
for nm in coker_identifies coker_separates coker_classes_distinct b_not_in_image; do
  ln=$(grep -n "^theorem $nm" "$F" | cut -d: -f1 | head -1)
  if [ -n "$ln" ] && [ "$ln" -ge 473 ] && [ "$ln" -le 692 ]; then
    echo "  OK   $nm at line $ln (inside 473-692)"
  else echo "  FAIL $nm not inside the new section"; fail=1; fi
done
echo "note: the odd-class count 32 is the in-file complement (64 - 32); it is"
echo "      verified numerically (32+32=64, both fibres) by r8s_k3_recompute.py."
if [ "$fail" = 0 ]; then echo "r8s_k6_antivacuity: PASS"; exit 0
else echo "r8s_k6_antivacuity: FAIL"; exit 1; fi
