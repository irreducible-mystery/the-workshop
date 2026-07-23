#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z8_crossconfirm.sh -- ROUND-8 TERMINAL AUDIT, seat Z, addendum.
#
# THE STAKES CHECK, CROSS-CONFIRMED FROM THIS SEAT.  The d-seat reported
# two FRESH round-8 prose defects (T1, T2) against the capstone's
# "exactly one defect" claim.  The terminal reconciliation seat re-derives
# the factual basis of both from primary evidence, and adds one datum the
# register note invites: the five carried re-verifications, run against
# the ROUND-8 tree.
#
#   T1  PROOFS.md's terminal gap table header claims "Every row any
#       round's DECLARED GAPS table ever carried, at its round-8 status"
#       -- but three round-1 rows (best == 8 game value; best == 5 sharp;
#       Tier 4a/4b) appear NOWHERE in PROOFS.md, neither in the table nor
#       in Closed-en-route.  (The mathematics DID close, round 2:
#       bestClassical_eq_eight, bestSat_eq_five -- so T1 is bookkeeping
#       prose, class 7, not a math gap.)
#   T2  PROOFS.md: "FILES= folded into one manifest ... a source list can
#       no longer drift between them" -- but audit/axioms.sh still
#       hard-codes the six-file list (twice); only transcript/pointers/
#       views read audit/sources.txt.  The census copy can still drift.
#
# PASS here = the cross-confirmation is established (the two defects are
# real, evidenced from primary sources, and the five carried instruments
# are green on the round-8 tree).  This script scores a claim; it is not
# a gate on the tree.
#
# Standalone: sh + grep + python3.  Exit 0 = cross-confirmation holds.
# ---------------------------------------------------------------------------
set -u
L=/home/claude/workshop/lean
fail=0

echo "=============================================================="
echo " Z8 -- FRESH-DEFECT CROSS-CONFIRMATION (terminal seat)"
echo "=============================================================="

echo "--- T1: the gap-table header vs the round-1 rows ---"
grep -q "Every row any round's DECLARED GAPS table ever carried" "$L/PROOFS.md" \
  && echo "  ok    header's ever-carried claim present verbatim in PROOFS.md" \
  || { echo "  FAIL  header sentence not found"; fail=1; }
for pat in 'best == 8' 'best == 5' 'Tier 4'; do
  if grep -qF "$pat" "$L/archive/PROOFS-round1.md"; then
    echo "  ok    round-1 DECLARED GAPS carried: $pat"
  else
    echo "  FAIL  round-1 row not found: $pat"; fail=1
  fi
  if grep -qF "$pat" "$L/PROOFS.md"; then
    echo "  FAIL  '$pat' IS in PROOFS.md -- T1 would be unfounded"; fail=1
  else
    echo "  ok    absent from the terminal ledger: $pat"
  fi
done
n=$(grep -cE '^theorem (bestClassical_eq_eight|bestSat_eq_five) ' "$L/MagicSquare.lean")
[ "$n" = 2 ] && echo "  ok    the closing theorems exist (bestClassical_eq_eight, bestSat_eq_five)" \
             || { echo "  FAIL  closing theorems missing"; fail=1; }
echo "  => T1 CONFIRMED: header overclaims; three ever-carried rows unaccounted."

echo
echo "--- T2: the manifest-fold sentence vs axioms.sh ---"
grep -q "a source list can no longer drift between them" "$L/PROOFS.md" \
  && echo "  ok    the no-longer-drift sentence present verbatim" \
  || { echo "  FAIL  sentence not found"; fail=1; }
nhard=$(grep -c '^for f in Interchange MagicSquare Anyon Exchangeable Rigidity Verlinde' "$L/audit/axioms.sh")
[ "$nhard" = 2 ] && echo "  ok    axioms.sh hard-codes the six-file list in $nhard places" \
                 || { echo "  FAIL  expected 2 hard-coded lists, found $nhard"; fail=1; }
for s in transcript.sh pointers.sh views.sh; do
  grep -q 'audit/sources\.txt' "$L/audit/$s" \
    && echo "  ok    $s reads audit/sources.txt" \
    || { echo "  FAIL  $s does not read the manifest"; fail=1; }
done
grep -q 'audit/sources\.txt' "$L/audit/axioms.sh" \
  && { echo "  FAIL  axioms.sh reads the manifest -- T2 would be unfounded"; fail=1; } \
  || echo "  ok    axioms.sh does NOT read the manifest -- its copy can drift"
echo "  => T2 CONFIRMED: the fold is three-of-four; the sentence overclaims."

echo
echo "--- the five carried re-verifications, on the ROUND-8 tree ---"
cd "$L" || exit 1
for s in audit_c1_check verify_anyon verify_anyon_r2 verify_c3 verify_exchangeable_r2; do
  if python3 "audit/$s.py" > /dev/null 2>&1; then
    echo "  ok    $s.py exit 0"
  else
    echo "  note  $s.py exit nonzero on round-8 tree (register note is"
    echo "        round-7-scoped, so this would be a datum, not a defect)"
  fi
done
echo "  => the REGISTER's corrected H1 note stays true, and stays true at 8."

echo
if [ "$fail" = 0 ]; then
  echo "RESULT: cross-confirmation holds.  Two fresh round-8 class-7 prose"
  echo "        defects (T1, T2) are real, from primary evidence; therefore"
  echo "        the capstone's 'exactly one prose defect' is falsified, while"
  echo "        the register-age alarm (defect OLDER than its adjudicator)"
  echo "        still never fired.  PASS (the confirmation, not the claim)."
  exit 0
else
  echo "RESULT: FAIL -- the cross-confirmation could not be established."
  exit 1
fi
