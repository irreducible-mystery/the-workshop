#!/bin/sh
# r8s_k4_axioms.sh -- ROUND-8 TERMINAL AUDIT, K4 (the coker seat).
# Reconcile the ledger's axiom claims for S6.5 with audit/axioms-round8.txt,
# as far as AGGREGATION allows:
#   claim 1: the rank facts (image_iff_even etc.) are axiom-free;
#   claim 2: the quotient/iso family carries only [propext, Quot.sound];
#   claim 3: 0 sorryAx, 0 Classical.choice.
# Verifies: per-file rows, per-family sums, round-7 -> round-8 deltas, the
# census's source-hash binding, and the PROOFS.md VIEW block = the txt.
# FLAGS (does not fail on): per-theorem rows are NOT aboard, so claims 1-2 are
# aggregate-consistent but single-sided here (no Lean toolchain to re-census).
# Exit 0 = PASS, 1 = FAIL.
set -u
L=/home/claude/workshop/lean
A8="$L/audit/axioms-round8.txt"; A7="$L/audit/axioms-round7.txt"
fail=0
num() { grep -E "$2" "$1" | head -1 | grep -oE '[0-9]+' | tr '\n' ' '; }

# --- per-file row and family rows, round 8 -----------------------------------
set -- $(num "$A8" '^MagicSquare +[0-9]')
T8=$1; F8=$2; R8=$3
P5=$(grep -E 'MagicSquare +\[propext, Quot.sound\]' "$A8" | grep -oE '[0-9]+$')
PP=$(grep -E 'MagicSquare +\[propext\]' "$A8" | grep -oE '[0-9]+$')
echo "round-8 MagicSquare row      : theorems=$T8 axiom-free=$F8 rest=$R8"
echo "round-8 families             : [propext, Quot.sound]=$P5  [propext]=$PP"
[ "$T8" = 85 ] && [ "$F8" = 25 ] && [ "$R8" = 60 ] || { echo "FAIL: row != 85/25/60"; fail=1; }
[ $((F8 + PP + P5)) = "$T8" ] && echo "partition                    : 25 + 55 + 5 = 85  OK" \
  || { echo "FAIL: families do not partition the file"; fail=1; }
# --- deltas vs round 7 -------------------------------------------------------
set -- $(num "$A7" '^MagicSquare +[0-9]')
T7=$1; F7=$2
P57=$(grep -E 'MagicSquare +\[propext, Quot.sound\]' "$A7" | grep -oE '[0-9]+$')
PP7=$(grep -E 'MagicSquare +\[propext\]' "$A7" | grep -oE '[0-9]+$')
echo "round-7 -> round-8 deltas    : theorems +$((T8-T7)) axiom-free +$((F8-F7)) [propext] +$((PP-PP7)) [propext,Quot.sound] +$((P5-P57))"
[ $((T8-T7)) = 22 ] && [ $((F8-F7)) = 9 ] && [ $((PP-PP7)) = 10 ] && [ $((P5-P57)) = 3 ] \
  && [ $(( (F8-F7)+(PP-PP7)+(P5-P57) )) = 22 ] \
  && echo "delta partition              : 9 + 10 + 3 = 22 new theorems  OK" \
  || { echo "FAIL: deltas inconsistent"; fail=1; }
# --- totals and the two that matter ------------------------------------------
grep -qE '^TOTAL +1150 +503 +647' "$A8" && echo "totals                       : 1150 / 503 / 647  OK" \
  || { echo "FAIL: totals row"; fail=1; }
grep -qE 'sorryAx +0' "$A8" && grep -qE 'Classical.choice +0' "$A8" \
  && echo "sorryAx = 0, Classical.choice = 0  OK" || { echo "FAIL: hygiene pair"; fail=1; }
# --- the census binds to these exact sources ---------------------------------
ok=1
for f in Interchange MagicSquare Anyon Exchangeable Rigidity Verlinde; do
  h=$(sha256sum "$L/$f.lean" | cut -d' ' -f1)
  grep -q "$f.lean *$h" "$A8" || { echo "FAIL: census hash mismatch for $f.lean"; ok=0; fail=1; }
done
h=$(sha256sum "$L/lean-toolchain" | cut -d' ' -f1)
grep -q "lean-toolchain *$h" "$A8" || { echo "FAIL: lean-toolchain hash"; ok=0; fail=1; }
[ "$ok" = 1 ] && echo "source binding               : all 7 census hashes = sha256 of the tree files  OK"
# round-7 census must bind to the ARCHIVED MagicSquare (the diff basis)
h7=$(sha256sum "$L/archive/src-round7/MagicSquare.lean" | cut -d' ' -f1)
grep -q "MagicSquare.lean *$h7" "$A7" && echo "round-7 census binds archive/src-round7/MagicSquare.lean  OK" \
  || { echo "FAIL: round-7 census hash vs archived source"; fail=1; }
# --- PROOFS.md VIEW block == the shipped txt (table + families + hygiene) ----
if sed -n '/VIEW:axioms BEGIN/,/VIEW:axioms END/p' "$L/PROOFS.md" | grep -E '^\s*(Interchange|MagicSquare|Anyon|Exchangeable|Rigidity|Verlinde|TOTAL|sorryAx|Classical)' > /tmp/r8s_k4_view.txt \
   && grep -E '^\s*(Interchange|MagicSquare|Anyon|Exchangeable|Rigidity|Verlinde|TOTAL|sorryAx|Classical)' "$A8" | grep -vE '\.lean ' > /tmp/r8s_k4_txt.txt \
   && diff -w /tmp/r8s_k4_view.txt /tmp/r8s_k4_txt.txt >/dev/null; then
  echo "PROOFS.md axioms VIEW        : identical numbers to audit/axioms-round8.txt  OK"
else echo "FAIL: PROOFS.md VIEW drifts from axioms-round8.txt"; fail=1; fi
# --- the honest boundary, flagged (K4's single-sidedness clause) -------------
echo "FLAG (not a failure): the shipped census aggregates per FILE and FAMILY only;"
echo "  per-theorem rows live in the builder's /tmp raw.txt and did not ride.  So"
echo "  'the rank facts are axiom-free' and 'the iso family carries only"
echo "  [propext, Quot.sound]' are CONSISTENT with (+9 axiom-free, +10 [propext],"
echo "  +3 [propext, Quot.sound]) and with the proof terms as read, but are not"
echo "  per-theorem checkable from the crate; no Lean toolchain on this side."
if [ "$fail" = 0 ]; then echo "r8s_k4_axioms: PASS (with the single-sidedness flag above)"; exit 0
else echo "r8s_k4_axioms: FAIL"; exit 1; fi
