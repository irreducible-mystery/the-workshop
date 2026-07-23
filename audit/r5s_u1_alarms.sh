#!/bin/sh
# ---------------------------------------------------------------------------
# r5s_u1_alarms.sh -- round-5 source audit, check U1.
#
#   (E3/E4)  audit/axioms.sh's filter comment now places the census false
#            positive at MagicSquare.lean:320 and credits the ANCHOR, not the
#            /:/ guard; the guard is credited only with the (reworded-away)
#            Anyon sec-6 site and marked inert.  Old wording must be gone.
#   (E5 i)   the census turns sorryAx / Classical.choice / INCOMPLETE into a
#            nonzero EXIT CODE.  Verified by running the real script against
#            a stub Lean kernel (the house method, HANDOFF.md addendum 2).
#   (E5 iii) transcript.sh fails when lean exits 0 but writes no .olean.
#            Counterfactual: the round-4 script (from the FROZEN crate)
#            PASSes the same run.
#   (E5 ii)  both instruments GENERATE five source-hash stamps (stamping code
#            located statically; stub runs prove the stamps are computed from
#            the tree being measured, not hand-pasted).
#
# Standalone.  PASS/FAIL lines; exit 1 if any FAIL.
# ---------------------------------------------------------------------------
set -u
LEAN=/home/claude/workshop/lean
FROZEN=/root/.claude/uploads/2f80c594-7369-5679-8dd4-4edf1999b180/6c1cf17e-workshopleanround4FROZEN.zip
S=$(mktemp -d /home/claude/.r5s_u1.XXXXXX)
trap 'rm -rf "$S"' EXIT
npass=0; nfail=0
ok()  { echo "PASS  $1"; npass=$((npass+1)); }
bad() { echo "FAIL  $1"; nfail=$((nfail+1)); }

A="$LEAN/audit/axioms.sh"
T="$LEAN/audit/transcript.sh"

echo "== U1-A: E3/E4 -- the shipped wording of the filter comment =="
grep -q 'MagicSquare.lean:320' "$A" && grep -q 'the plural fails the anchor before any guard is consulted' "$A" \
  && ok "comment places the false positive at MagicSquare.lean:320, credited to the ANCHOR" \
  || bad "corrected MagicSquare/anchor attribution missing from axioms.sh"
grep -q 'currently inert' "$A" && grep -q 'Anyon.lean section 6 carried' "$A" \
  && grep -q 'one until round 4 reworded it; the guard is what caught THAT site' "$A" \
  && ok "guard credited only with the old Anyon sec-6 site; marked 'currently inert -- kept'" \
  || bad "guard credit / inert note missing"
grep -q 'Round 4 ledger prose credited the guard with work the anchor does' "$A" \
  && ok "the round-4 miscredit is recorded in the instrument itself" \
  || bad "no record of the miscredit in axioms.sh"
grep -q 'one does, in Anyon.lean section 6' "$A" \
  && bad "OLD defective wording still present in round-5 axioms.sh" \
  || ok "old wording ('...begin with the word theorem... one does, in Anyon.lean section 6') is gone"
# provenance: the old wording really was the round-4 state (line-54 region)
python3 -c "
import zipfile,sys
old = zipfile.ZipFile('$FROZEN').read('audit/axioms.sh').decode()
lines = old.split(chr(10))
hit = [i+1 for i,l in enumerate(lines) if 'Anyon.lean section 6' in l]
sys.exit(0 if (hit and 52 <= hit[0] <= 56 and 'one does, in Anyon.lean section 6' in old) else 1)
" && ok "FROZEN round-4 axioms.sh carries the old wording in the line-54 region (E3 was real)" \
  || bad "could not confirm old wording in FROZEN round-4 axioms.sh"

echo ""
echo "== U1-A2: the facts behind the comment =="
L320=$(sed -n '320p' "$LEAN/MagicSquare.lean")
case "$L320" in
  "theorems below"*) ok "MagicSquare.lean:320 begins 'theorems below' (plural; fails the space-anchor)";;
  *) bad "MagicSquare.lean:320 is: $L320";;
esac
echo "$L320" | grep -q ':' && bad "line 320 carries a colon (guard would matter)" \
  || ok "line 320 carries no colon either (both filters would exclude it; anchor fires first)"
NG=$(awk "/^theorem [A-Za-z_0-9']+/ && !/:/" "$LEAN/Anyon.lean" "$LEAN/MagicSquare.lean" "$LEAN/Interchange.lean" "$LEAN/Exchangeable.lean" | wc -l)
[ "$NG" -eq 0 ] && ok "guard is inert on the round-5 sources: 0 anchor-matching colon-free lines" \
  || bad "guard NOT inert: $NG such lines exist"
NG4=$(awk "/^theorem [A-Za-z_0-9']+/ && !/:/" "$LEAN/archive/src-round4/"*.lean | wc -l)
[ "$NG4" -eq 0 ] && ok "round-4 sources also carry none (consistent with 'reworded away in round 4')" \
  || bad "round-4 sources carry $NG4 such lines"

echo ""
echo "== U1-B: E5(i) exit-code plumbing, static trace =="
grep -q 'bad = (sorryax > 0 || choice > 0 || err > 0)' "$A" \
  && grep -q 'print bad > statusfile' "$A" \
  && grep -q 'STATUS=\$(cat "\$WORK/status" 2>/dev/null || echo 1)' "$A" \
  && grep -q 'exit "\$STATUS"' "$A" \
  && ok "path traced: awk END computes bad from (sorryax|choice|err) -> statusfile -> STATUS -> exit; cat-failure defaults to 1" \
  || bad "exit-code plumbing not found as documented"

echo ""
echo "== U1-C: the bites, run live against a stub Lean kernel =="
TT="$S/tree"; mkdir -p "$TT/audit" "$S/home/.elan/bin"
cp "$A" "$T" "$TT/audit/"
python3 -c "
import zipfile
open('$TT/audit/transcript_r4.sh','wb').write(zipfile.ZipFile('$FROZEN').read('audit/transcript.sh'))
"
printf 'leanprover/lean4:v4.32.0\n' > "$TT/lean-toolchain"
for f in Interchange MagicSquare Anyon Exchangeable; do
  {
    echo "namespace W"
    echo "theorem t1_$f : 1 = 1 := rfl"
    echo "theorem t2_$f : 2 = 2 := rfl"
    echo "end W"
  } > "$TT/$f.lean"
done
STUB="$S/home/.elan/bin/lean"
cat > "$STUB" <<'EOSTUB'
#!/bin/sh
# stub Lean kernel -- behavior selected by STUBMODE (house method)
case "${1:-}" in --version) echo "Lean (stub 4.32.0)"; exit 0;; esac
if [ "${1:-}" = "-o" ]; then OLEAN="$2"; SRC="$3"; else OLEAN=""; SRC="${1:-}"; fi
case "${STUBMODE:-}" in
  census_clean)
    n=$(grep -c '#print axioms' "$SRC"); i=0
    while [ "$i" -lt "$n" ]; do echo "stub does not depend on any axioms"; i=$((i+1)); done ;;
  census_sorry)
    n=$(grep -c '#print axioms' "$SRC"); i=0
    while [ "$i" -lt "$n" ]; do echo "stub depends on axioms: [sorryAx]"; i=$((i+1)); done ;;
  census_choice)
    n=$(grep -c '#print axioms' "$SRC"); i=0
    while [ "$i" -lt "$n" ]; do echo "stub depends on axioms: [propext, Classical.choice, Quot.sound]"; i=$((i+1)); done ;;
  census_error)
    echo "stub does not depend on any axioms"
    echo "$SRC:1:0: error: unknown constant (stub)" ;;
  tr_noolean) exit 0 ;;
  tr_ok) [ -n "$OLEAN" ] && printf 'stub-olean-bytes' > "$OLEAN"; exit 0 ;;
esac
exit 0
EOSTUB
chmod +x "$STUB"

runit() { ( cd "$TT" && HOME="$S/home" STUBMODE="$1" sh "audit/$2" ) > "$S/out.$1.$2" 2>&1; echo $?; }

rc=$(runit census_sorry axioms.sh)
if [ "$rc" -eq 1 ] && grep -q '!! HYGIENE FAILURE' "$S/out.census_sorry.axioms.sh" \
   && grep -q 'RESULT: FAIL' "$S/out.census_sorry.axioms.sh"; then
  ok "E5(i) BITE: planted sorryAx -> census prints '!! HYGIENE FAILURE', 'RESULT: FAIL', exits 1"
else bad "E5(i): sorryAx run gave exit=$rc (want 1) or missing alarm text"; fi

rc=$(runit census_choice axioms.sh)
if [ "$rc" -eq 1 ] && grep -q '!! HYGIENE FAILURE' "$S/out.census_choice.axioms.sh"; then
  ok "E5(i) BITE: planted Classical.choice -> census prints '!! HYGIENE FAILURE' and exits 1"
else bad "E5(i): Classical.choice run gave exit=$rc (want 1)"; fi

rc=$(runit census_error axioms.sh)
if [ "$rc" -eq 1 ] && grep -q 'INCOMPLETE' "$S/out.census_error.axioms.sh"; then
  ok "E5(i) BITE: planted lean error -> census reports INCOMPLETE and exits 1"
else bad "E5(i): error run gave exit=$rc (want 1) or missing INCOMPLETE"; fi

rc=$(runit census_clean axioms.sh)
if [ "$rc" -eq 0 ] && grep -q 'RESULT: census complete, hygiene clean.  PASS.' "$S/out.census_clean.axioms.sh"; then
  ok "E5(i) control: clean tree -> census exits 0, RESULT PASS"
else bad "E5(i) control: clean run gave exit=$rc (want 0)"; fi

rc=$(runit tr_noolean transcript.sh)
if [ "$rc" -eq 1 ] && grep -q 'NO OLEAN PRODUCED' "$S/out.tr_noolean.transcript.sh" \
   && grep -q '!! exit 0 but NO .olean was produced' "$S/out.tr_noolean.transcript.sh"; then
  ok "E5(iii) BITE: lean exits 0, writes nothing -> transcript.sh FAILs (exit 1, loud)"
else bad "E5(iii): no-olean run gave exit=$rc (want 1) or missing alarm text"; fi

rc=$(runit tr_ok transcript.sh)
if [ "$rc" -eq 0 ] && grep -q 'RESULT: all files compiled silent (exit 0, zero bytes).  PASS.' "$S/out.tr_ok.transcript.sh"; then
  ok "E5(iii) control: olean produced silently -> transcript.sh PASSes (exit 0)"
else bad "E5(iii) control: gave exit=$rc (want 0)"; fi

rc=$(runit tr_noolean transcript_r4.sh)
if [ "$rc" -eq 0 ] && grep -q '(no olean produced)' "$S/out.tr_noolean.transcript_r4.sh" \
   && grep -q 'PASS' "$S/out.tr_noolean.transcript_r4.sh"; then
  ok "counterfactual: ROUND-4 transcript.sh calls the same no-olean run a clean PASS (HANDOFF claim verified)"
else bad "counterfactual: round-4 script gave exit=$rc (expected 0 = the old hole)"; fi

echo ""
echo "== U1-D: E5(ii) -- the stamps are GENERATED, not pasted =="
grep -n 'sha256sum "\$f.lean"' "$A" >/dev/null \
  && ok "stamping code found in axioms.sh (loop: printf + sha256sum \$f.lean, + lean-toolchain)" \
  || bad "no stamping code in axioms.sh"
grep -n 'sha256sum "\$f"' "$T" >/dev/null \
  && ok "stamping code found in transcript.sh (loop over FILES + lean-toolchain)" \
  || bad "no stamping code in transcript.sh"
missing=0
for f in Interchange MagicSquare Anyon Exchangeable; do
  h=$(sha256sum "$TT/$f.lean" | cut -c1-64)
  grep -q "$h" "$S/out.census_clean.axioms.sh" || missing=$((missing+1))
  grep -q "$h" "$S/out.tr_ok.transcript.sh"    || missing=$((missing+1))
done
htc=$(sha256sum "$TT/lean-toolchain" | cut -c1-64)
grep -q "$htc" "$S/out.census_clean.axioms.sh" || missing=$((missing+1))
grep -q "$htc" "$S/out.tr_ok.transcript.sh"    || missing=$((missing+1))
[ "$missing" -eq 0 ] \
  && ok "stub runs stamp the SANDBOX files' fresh hashes (5 per instrument) -- live generation proven" \
  || bad "$missing expected sandbox stamps missing from stub-run outputs"
sm=0
for f in Interchange.lean MagicSquare.lean Anyon.lean Exchangeable.lean lean-toolchain; do
  h=$(sha256sum "$LEAN/$f" | cut -c1-64)
  grep -q "$h" "$LEAN/audit/transcript-round5.txt" || sm=$((sm+1))
  grep -q "$h" "$LEAN/audit/axioms-round5.txt"     || sm=$((sm+1))
done
[ "$sm" -eq 0 ] && ok "shipped round-5 outputs stamp all 5 current-tree hashes (10/10 present)" \
  || bad "$sm tree-hash stamps missing from shipped outputs"

echo ""
echo "r5s_u1: $npass PASS, $nfail FAIL"
[ "$nfail" -eq 0 ] && echo "RESULT: U1 PASS" || echo "RESULT: U1 FAIL"
[ "$nfail" -eq 0 ]
