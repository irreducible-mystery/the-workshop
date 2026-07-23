#!/bin/sh
# r8s_k7_floor.sh -- ROUND-8 TERMINAL AUDIT, K7 (the coker seat).
# The last-theorem symmetry: the ledger says the last stone "closes on a bench
# the floor had computed (floor/sheaf_cohomology.py: rank 5/6, the all-ones
# cocycle)".  RUN the floor bench, capture its numbers, and verify each names
# the same object as a Lean statement in MagicSquare.lean S6.5/S2/S6.
# Exit 0 = PASS, 1 = FAIL.
set -u
L=/home/claude/workshop/lean
BENCH=/home/claude/workshop/sheaf_cohomology.py
CRATE=/tmp/r8crate/floor/sheaf_cohomology.py
F="$L/MagicSquare.lean"
fail=0

echo "== the ledger sentence under test (PROOFS.md) =="
grep -n "closes on a bench the floor had computed" "$L/PROOFS.md" | sed 's/^/  /' || { echo "  FAIL: sentence missing"; fail=1; }
[ -f "$CRATE" ] && echo "  OK   crate pointer floor/sheaf_cohomology.py exists in the ferried crate" \
  || { echo "  FAIL: floor/sheaf_cohomology.py missing from crate"; fail=1; }
if [ -f "$CRATE" ] && cmp -s "$BENCH" "$CRATE"; then echo "  OK   crate copy byte-identical to the workshop floor bench"
else echo "  FAIL: crate floor bench differs from workshop copy"; fail=1; fi

echo "== running the floor bench =="
OUT=$(cd /home/claude/workshop && python3 sheaf_cohomology.py 2>&1); rc=$?
echo "$OUT" | sed 's/^/  | /'
[ "$rc" = 0 ] || { echo "  FAIL: bench exited $rc"; fail=1; }

echo "== the correspondence table (floor number <-> Lean statement) =="
row() { # row <floor-fragment> <lean-fragment> <label>
  if echo "$OUT" | grep -qF "$1"; then f=ok; else f=MISS; fi
  if grep -qF "$2" "$F"; then l=ok; else l=MISS; fi
  printf "  [floor %-4s | lean %-4s] %s\n" "$f" "$l" "$3"
  [ "$f" = ok ] && [ "$l" = ok ] || fail=1
}
row "rank M = 5"           "theorem imageCount_eq_32 : imageCount = 32 := rfl" \
    "rank M = 5   <->  imageCount_eq_32 (|im M| = 32 = 2^5, computed)"
row "rank [M|b] = 6"       "theorem b_not_in_image : inImage false false false false false true = false := rfl" \
    "rank [M|b] = 6  <->  b_not_in_image (b outside the rank-5 image)"
row "coker(M) ≅ Z_2"       "abbrev Coker := Quotient cokerSetoid" \
    "coker(M) = Z_2  <->  Coker + toZ2/fromZ2 (honest Quotient)"
row "class of b = the nonzero element" "theorem class_of_b_nonzero :" \
    "class of b nonzero  <->  class_of_b_nonzero"
row "witnessing cocycle y = (1,1,1,1,1,1): y·M = 0 and y·b = 1" \
    "theorem cocycle_annihilates (v : Assignment) :" \
    "y = all-ones, yM = 0  <->  cocycle_annihilates (and phiV = y-pairing)"
row "y·b = 1"              "theorem twist_is_odd :" \
    "y.b = 1  <->  twist_is_odd (and phiV_bVec : phiV bVec = true)"
row "UNSOLVABLE"           "theorem no_global_section (v : Assignment) : ¬ GlobalSection v := by" \
    "Mx = b unsolvable  <->  no_global_section (= b_not_in_image semantically)"
# the iso itself: two classes distinct, hom -- Lean side only (the floor states
# the group; the Lean file PROVES the iso)
for t in "theorem toZ2_hom" "theorem coker_two_classes" "theorem coker_classes_distinct"; do
  grep -qF "$t" "$F" && echo "  [lean ok  ]        iso content: $t" || { echo "  MISS $t"; fail=1; }
done
echo "== assertion parity =="
echo "$OUT" | grep -qF "rank M = 5, rank [M|b] = 6 -> UNSOLVABLE" \
  && echo "  OK   floor asserts 5 / 6 / UNSOLVABLE in one line (its own asserts ran: exit 0)" \
  || { echo "  FAIL: floor line missing"; fail=1; }
if [ "$fail" = 0 ]; then
  echo "r8s_k7_floor: PASS -- the bench numbers and the Lean statements name the same object"
  exit 0
else echo "r8s_k7_floor: FAIL"; exit 1; fi
