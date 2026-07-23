#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_f3 -- ROUND-8 FINAL AUDIT, fresh-defect seat.  Every checkable receipt
# behind the capstone's NEW prose, verified against the artifacts aboard:
#
#   R1  headline counts: recount 21/85/714/41/214/75 -> 1150 by the house rule
#   R2  census arithmetic: 503 axiom-free, per-file sums, family sums, 0/0
#   R3  near-miss numbers: 1,053 and 1,128 are the archived TOTALs
#   R4  the five scored-prediction receipts exist in the archives verbatim
#   R5  H2's receipt: "all 199" + the bump narration are in the ROUND-6 LEDGER;
#       round-6 Rigidity S10 said "all 214"; the round-7 G3 bullet misbound
#   R6  H3's receipt: "Eight instruments ship" is in the round-7 ledger;
#       exactly the seven named shell instruments ride
#   R7  the round-7 gap table lacks the three restored rows; round 6 has them
#   R8  the ferried-both-directions claim: floor/, r3-r7 certificates, the two
#       gifts (crate universe)
#   R9  every theorem-map / coker-section pointer resolves (delegates to
#       audit/pointers.sh) and key map bindings exist as declarations
#
# PASS iff every receipt checks.  Usage: sh audit/r8s_f3_capstone_receipts.sh
# [CRATE=/tmp/r8crate]  (run from workshop/lean/)
# ---------------------------------------------------------------------------
set -u
CRATE="${CRATE:-/tmp/r8crate}"
fail=0
ok () { echo "PASS  $1"; }
bad () { echo "FAIL  $1"; fail=1; }

# --- R1: theorem counts by the house awk rule --------------------------------
tot=0; pf=""
for f in Interchange:21 MagicSquare:85 Anyon:714 Exchangeable:41 Rigidity:214 Verlinde:75; do
  n="${f#*:}"; f="${f%%:*}"
  got=$(awk "/^theorem [A-Za-z_0-9']+/ && /:/ {c++} END{print c+0}" "$f.lean")
  [ "$got" -eq "$n" ] && ok "R1-count-$f = $n" || bad "R1-count-$f got $got want $n"
  tot=$((tot + got))
done
[ "$tot" -eq 1150 ] && ok "R1-total = 1150" || bad "R1-total got $tot"

# --- R2: census arithmetic ---------------------------------------------------
AX=audit/axioms-round8.txt
s=$(awk '/^Interchange|^MagicSquare|^Anyon|^Exchangeable|^Rigidity|^Verlinde/ {af+=$3} END{print af}' "$AX")
[ "$s" = "503" ] && ok "R2-axiom-free sums to 503" || bad "R2-axiom-free sums to $s"
grep -qE "TOTAL +1150 +503 +647" "$AX" \
  && ok "R2-census TOTAL row 1150/503/647" || bad "R2-census TOTAL row"
grep -q "sorryAx           0" "$AX" && grep -q "Classical.choice  0" "$AX" \
  && ok "R2-hygiene 0 sorryAx / 0 Classical.choice" || bad "R2-hygiene zeros"
# family sums equal the per-file "rest" column
awk '/axiom sets actually occurring/{f=1;next} f&&NF>=3{r[$1]+=$NF}
     END{ if (r["MagicSquare"]==60 && r["Anyon"]==407 && r["Rigidity"]==155 && r["Verlinde"]==25) exit 0; exit 1 }' "$AX" \
  && ok "R2-family sums match rest column (60/407/155/25)" || bad "R2-family sums"

# --- R3: the near-miss numbers are the archived totals -----------------------
grep -q "TOTAL                1053" audit/transcript-round6.txt \
  && ok "R3-round-6 total 1,053 (shipped correct)" || bad "R3-1053"
grep -q "TOTAL                1128" audit/transcript-round7.txt \
  && ok "R3-round-7 total 1,128" || bad "R3-1128"

# --- R4: the five prediction receipts ----------------------------------------
grep -q 'The verb .*collapse to' archive/PROOFS-round5.md \
  && ok "R4-p1 receipt: the 'collapse to' verb (round-5 ledger)" || bad "R4-p1"
grep -q 'twelve minutes' ROUND6.md && grep -q '06:54:40Z vs 07:12Z' HANDOFF.md \
  && ok "R4-p2 receipt: F4 twelve-minutes vs 17m20s" || bad "R4-p2"
grep -q 'not reachable in' archive/PROOFS-round6.md \
  && ok "R4-p3 receipt: 'not reachable in Lean' generalization (round 6, early)" || bad "R4-p3"
grep -q 'for any' ROUND7.md && grep -q 'gauge_curve_deriv' archive/PROOFS-round7.md \
  && ok "R4-p4 receipt: gauge_curve_deriv 'for any scalar l' (round 7)" || bad "R4-p4"
grep -q 'nonzero on newer sources' ROUND8.md && grep -q 'all five exit 0' REGISTER.md \
  && ok "R4-p5 receipt: H1 exit-nonzero reason false of the five aboard" || bad "R4-p5"

# --- R5: H2's receipt, both sites in the round-6 LEDGER ----------------------
grep -q 'all 199' archive/PROOFS-round6.md \
  && ok "R5-'all 199' lives in the round-6 ledger" || bad "R5-199-site"
grep -q 'bumped it to 214' archive/PROOFS-round6.md \
  && ok "R5-the bump narration lives in the round-6 ledger" || bad "R5-bump-site"
grep -q 'all 214 of them' archive/src-round6/Rigidity.lean 2>/dev/null \
  && ok "R5-round-6 Rigidity S10 said 'all 214' (correct at ship)" \
  || echo "note  archive/src-round6 not in this universe; skipped"
grep -q 'Rigidity.lean line 561 "all 199"' archive/PROOFS-round7.md \
  && ok "R5-the round-7 G3 bullet misbound the sites to Rigidity.lean" || bad "R5-G3-bullet"
grep -qc '214' Rigidity.lean >/dev/null; c=$(grep -c '214' Rigidity.lean)
[ "$c" -eq 0 ] && ok "R5-current Rigidity carries no hard-coded count (G3 repair)" \
  || bad "R5-current Rigidity still hard-codes a count"

# --- R6: instruments ---------------------------------------------------------
grep -q 'Eight instruments ship' archive/PROOFS-round7.md \
  && ok "R6-round-7 ledger said 'Eight instruments ship' (the H3 overcount)" || bad "R6-overcount"
n=0
for s in axioms transcript ship views pointers transcription numerals; do
  [ -f "audit/$s.sh" ] && n=$((n + 1))
done
[ "$n" -eq 7 ] && ok "R6-exactly the seven named shell instruments ride" \
  || bad "R6-shell instruments found $n/7"

# --- R7: the three restored rows ---------------------------------------------
for pat in 'r| = 1' 'SS' 'pentOK'; do :; done
if grep -q 'coker' archive/PROOFS-round7.md; then
  awk '/## DECLARED GAPS/{f=1} f' archive/PROOFS-round7.md > /tmp/r8s_f3_r7gaps.$$
  ! grep -q 'r| = 1' /tmp/r8s_f3_r7gaps.$$ && ! grep -q 'SS.*swap' /tmp/r8s_f3_r7gaps.$$ \
    && ! grep -q 'pentOK' /tmp/r8s_f3_r7gaps.$$ \
    && ok "R7-round-7 table lacks Born/SS/pentOK (the drop is real)" \
    || bad "R7-round-7 table drop claim"
  rm -f /tmp/r8s_f3_r7gaps.$$
fi
grep -q 'SS.*swap-invariance' archive/PROOFS-round6.md && grep -q 'pentOK' archive/PROOFS-round6.md \
  && ok "R7-round-6 table carried SS and pentOK (restoration is faithful)" || bad "R7-round-6 rows"
grep -q 'PROVED (round 8)' PROOFS.md && grep -q 'dropped by round 7, restored' PROOFS.md \
  && ok "R7-terminal table restores and closes as claimed" || bad "R7-terminal rows"

# --- R8: ferried both directions (crate universe) ----------------------------
if [ -d "$CRATE" ]; then
  [ -f "$CRATE/floor/sheaf_cohomology.py" ] && [ -f "$CRATE/floor/README.md" ] \
    && [ -f "$CRATE/floor/WELD_REPORT.txt" ] && [ -f "$CRATE/floor/FINDINGS.md" ] \
    && ok "R8-floor rides whole (benches + README + WELD_REPORT + FINDINGS)" \
    || bad "R8-floor incomplete"
  [ -f "$CRATE/audit/r7_gift_verlinde.py" ] && [ -f "$CRATE/audit/r7_numeral_gift.py" ] \
    && ok "R8-both missed gifts ride" || bad "R8-gifts"
  for r in 3 4 5 6 7; do
    ls "$CRATE"/audit/r${r}*_* >/dev/null 2>&1 || { bad "R8-r${r} certificates missing"; continue; }
  done
  ok "R8-r3..r7 builder certificates ride under audit/"
else
  echo "note  crate universe $CRATE not present; R8 skipped"
fi

# --- R9: pointers (in the CRATE universe -- the ferry pointers name floor/
#     files, which ride in the crate; a tree without floor/ merged is layout,
#     not a defect) ----------------------------------------------------------
PU="."
[ ! -d floor ] && [ -d "$CRATE/floor" ] && PU="$CRATE"
if ( cd "$PU" && sh audit/pointers.sh >/dev/null 2>&1 ); then
  ok "R9-all capstone pointers resolve (audit/pointers.sh green in $PU)"
else
  bad "R9-pointers.sh nonzero in $PU"
fi
for t in image_iff_even imageCount_eq_32 b_not_in_image toZ2_hom coker_two_classes \
         coker_classes_distinct coker_identifies coker_separates phiV_vxor phiV_bVec; do
  grep -qE "^(theorem|def) $t" MagicSquare.lean \
    && ok "R9-coker name $t declared" || bad "R9-coker name $t"
done
grep -q 'Msel (cleared S), verlNum' "$CRATE/audit/r7s_verlinde_race.py" 2>/dev/null \
  && ok "R9-the race transcribed Msel/verlNum (capstone's Msel correction is faithful)" \
  || echo "note  race script not aboard this universe; Msel binding from tree only"

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: every checkable receipt behind the capstone's new prose"
  echo "        verifies against the artifacts aboard.  PASS."
else
  echo "RESULT: receipt check(s) failed.  FAIL."
fi
exit $fail
