#!/bin/sh
# ---------------------------------------------------------------------------
# r5s_u2_views_bite.sh -- round-5 source audit, check U2: views.sh bites.
#
# The builder ran `views.sh check` live and reported PASS.  House norm 7 says
# a check that cannot fail is not a check -- so this script verifies the BITE
# itself, in a throwaway copy of the tree (the real PROOFS.md is never
# touched; its hash is compared before/after as proof):
#
#   run 1  pristine copy            -> must PASS, exit 0
#   run 2  ONE digit edited inside the transcript VIEW block (the round-4
#          defect class: the date)  -> must print DRIFTED, exit 1
#   run 3  ONE digit edited inside the axioms VIEW block (TOTAL 839->838)
#                                   -> must print DRIFTED, exit 1
#   run 4  the PROOFS.md E2 claim: round-4 outputs + a ledger with no view
#          blocks -> ABSENT on both views, MISMATCH 0/2 on all five sources,
#          exit 1
#
# Standalone.  PASS/FAIL lines; exit 1 if any FAIL.
# ---------------------------------------------------------------------------
set -u
LEAN=/home/claude/workshop/lean
S=$(mktemp -d /home/claude/.r5s_u2.XXXXXX)
trap 'rm -rf "$S"' EXIT
npass=0; nfail=0
ok()  { echo "PASS  $1"; npass=$((npass+1)); }
bad() { echo "FAIL  $1"; nfail=$((nfail+1)); }

BEFORE=$(sha256sum "$LEAN/PROOFS.md" | cut -c1-64)

echo "== the view-block delimiters actually shipping in PROOFS.md =="
grep -n '^<!-- VIEW:' "$LEAN/PROOFS.md" | sed 's/^/  | /'
NB=$(grep -c '^<!-- VIEW:[a-z]* BEGIN - rendered by audit/views.sh, do not edit by hand -->' "$LEAN/PROOFS.md")
NE=$(grep -c '^<!-- VIEW:[a-z]* END -->' "$LEAN/PROOFS.md")
[ "$NB" -eq 2 ] && [ "$NE" -eq 2 ] \
  && ok "exactly two view blocks (transcript, axioms), BEGIN/END balanced" \
  || bad "delimiter count off: $NB BEGIN / $NE END"

mktree() {
  D="$1"; mkdir -p "$D/audit"
  cp "$LEAN/PROOFS.md" "$D/"
  cp "$LEAN/audit/views.sh" "$D/audit/"
  cp "$LEAN/audit/transcript-round5.txt" "$LEAN/audit/axioms-round5.txt" "$D/audit/"
  cp "$LEAN/Anyon.lean" "$LEAN/MagicSquare.lean" "$LEAN/Interchange.lean" \
     "$LEAN/Exchangeable.lean" "$LEAN/lean-toolchain" "$D/"
}

echo ""
echo "== run 1: pristine copy =="
T1="$S/t1"; mktree "$T1"
( cd "$T1" && sh audit/views.sh check ) > "$S/out1" 2>&1; rc=$?
if [ "$rc" -eq 0 ] && grep -q 'ok       VIEW:transcript' "$S/out1" \
   && grep -q 'ok       VIEW:axioms' "$S/out1" \
   && [ "$(grep -c 'stamped in both outputs' "$S/out1")" -eq 5 ]; then
  ok "pristine: exit 0, both views ok, 5/5 sources stamped in both outputs (matches builder's live PASS)"
else bad "pristine run: exit=$rc (want 0) -- see $S/out1"; fi

echo ""
echo "== run 2: one digit edited inside VIEW:transcript (date 09:38:40 -> 09:38:41) =="
T2="$S/t2"; mktree "$T2"
python3 - "$T2/PROOFS.md" <<'EOPY'
import sys
p = sys.argv[1]; s = open(p).read()
b = s.index('<!-- VIEW:transcript BEGIN'); e = s.index('<!-- VIEW:transcript END')
blk = s[b:e]
assert blk.count('09:38:40') == 1
open(p, 'w').write(s[:b] + blk.replace('09:38:40', '09:38:41') + s[e:])
EOPY
( cd "$T2" && sh audit/views.sh check ) > "$S/out2" 2>&1; rc=$?
if [ "$rc" -eq 1 ] && grep -q 'DRIFTED  VIEW:transcript' "$S/out2"; then
  ok "BITE: one-digit date edit -> 'DRIFTED  VIEW:transcript', exit 1"
  grep 'DRIFTED' "$S/out2" | sed 's/^/  | /'
else bad "edit not caught: exit=$rc (want 1) -- see $S/out2"; fi
grep -q 'ok       VIEW:axioms' "$S/out2" \
  && ok "control: untouched axioms view still reports ok in the same run" \
  || bad "axioms view unexpectedly not ok"

echo ""
echo "== run 3: one digit edited inside VIEW:axioms (TOTAL 839 -> 838) =="
T3="$S/t3"; mktree "$T3"
python3 - "$T3/PROOFS.md" <<'EOPY'
import sys
p = sys.argv[1]; s = open(p).read()
b = s.index('<!-- VIEW:axioms BEGIN'); e = s.index('<!-- VIEW:axioms END')
blk = s[b:e]
assert blk.count('TOTAL                839') == 1
open(p, 'w').write(s[:b] + blk.replace('TOTAL                839', 'TOTAL                838') + s[e:])
EOPY
( cd "$T3" && sh audit/views.sh check ) > "$S/out3" 2>&1; rc=$?
if [ "$rc" -eq 1 ] && grep -q 'DRIFTED  VIEW:axioms' "$S/out3"; then
  ok "BITE: one-digit count edit -> 'DRIFTED  VIEW:axioms', exit 1"
else bad "count edit not caught: exit=$rc (want 1)"; fi

echo ""
echo "== run 4: the PROOFS.md E2 'verified to bite' scenario (round-4 outputs, no view blocks) =="
T4="$S/t4"; mktree "$T4"
cp "$LEAN/archive/PROOFS-round4.md" "$T4/PROOFS.md"
cp "$LEAN/audit/transcript-round4.txt" "$T4/audit/transcript-round5.txt"
cp "$LEAN/audit/axioms-round4.txt" "$T4/audit/axioms-round5.txt"
( cd "$T4" && sh audit/views.sh check ) > "$S/out4" 2>&1; rc=$?
NA=$(grep -c 'ABSENT   VIEW:' "$S/out4")
NM=$(grep -c 'MISMATCH .* 0/2' "$S/out4")
if [ "$rc" -eq 1 ] && [ "$NA" -eq 2 ] && [ "$NM" -eq 5 ]; then
  ok "ledger claim verified live: ABSENT on both views, 'stamped in 0/2 outputs' on all 5 sources, exit 1"
else bad "E2 scenario: exit=$rc ABSENT=$NA MISMATCH0/2=$NM (want 1/2/5)"; fi

echo ""
AFTER=$(sha256sum "$LEAN/PROOFS.md" | cut -c1-64)
[ "$BEFORE" = "$AFTER" ] \
  && ok "restore guarantee: real PROOFS.md untouched (sha256 $BEFORE unchanged)" \
  || bad "real PROOFS.md hash CHANGED -- investigate immediately"

echo ""
echo "r5s_u2: $npass PASS, $nfail FAIL"
[ "$nfail" -eq 0 ] && echo "RESULT: U2 PASS" || echo "RESULT: U2 FAIL"
[ "$nfail" -eq 0 ]
