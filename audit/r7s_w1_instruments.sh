#!/bin/sh
# ---------------------------------------------------------------------------
# r7s_w1_instruments.sh -- ROUND-7 SEAT: instruments, live (charge C1/C2/C3).
#
# WHAT THIS CHECKS (every falsifier RUN, per norms 7/14; bites in /tmp copies):
#   I1  pointers.sh baseline PASS on a pristine tree copy
#   I2  quoted-names.txt: the G1 rule sits at the TOP of the phantoms section,
#       BEFORE the exemption lines; both discussed names stay exempt
#   I3  the G1 repair, live: a FRESH planted phantom -> pointers.sh exits 1
#       (and the DESIGNED miss: planting the exempt `totally_made_up_theorem_name`
#       does NOT fire -- the exemption is necessary; the falsifier must be fresh)
#   I4  the repaired ledger sentence points at the file (byte-grep)
#   I5  the round-8-prediction PREMISE, live: rewriting an exemption's REASON
#       to nonsense changes nothing -- membership is checked, reasons are not
#   I6  numerals.sh: shipped exemption list carries NONE of the G3/HANDOFF
#       review numbers (the reversal the pre-ship audit forced)
#   I7  numerals.sh baseline: flag set == the DECLARED-GAPS benign review set,
#       exactly, on all three scanned docs (quarantine posture: exit 1 + review
#       language, not a verdict)
#   I8  numerals.sh bite: a planted fresh count is flagged (delta measured)
#   I9  numerals.sh retro on the ROUND-6 ledger: the G3 counts flag (this is
#       the ledger's own "run on the round-6 ledger" sentence, executed)
#   I10 numerals.sh design boundary vs the gift: 2-digit numerals are OUTSIDE
#       the shipped regex (reported as a NOTE -- divergence from the gift's
#       >=2-digit rule and from the header's own "every multi-digit number")
#   I11 ship.sh enumerate-or-forbid: the REAL 43-entry round-7 crate manifest
#       reconciles as 38 REQUIRED + 5 labeled-ALLOWED (.py) + 0 unlisted; a
#       planted stowaway is caught by the same logic; no .bak anywhere
#   I12 views.sh: `render` writes its backup OUT OF TREE and is idempotent on
#       a clean tree; `check` PASSes live and FAILS on a corrupted VIEW byte
#
# WHAT IT DOES NOT CHECK: binding of Verlinde prose (r7s_v2), the ledger crops
# and register (r7s_w2), anything needing a Lean toolchain (none here).
# Usage:   sh audit/r7s_w1_instruments.sh        (from workshop/lean/)
# Exit 0 iff every PASS (NOTEs do not fail; they are review items, norm 16).
# ---------------------------------------------------------------------------
set -u
fail=0
res() { printf '%-4s  %-30s %s\n' "$1" "$2" "$3"
        if [ "$1" = "FAIL" ]; then fail=1; fi; return 0; }

echo "=============================================================="
echo " r7s_w1 -- INSTRUMENTS LIVE (C1 pointers/G1, C2 numerals, C3 crate)"
echo "=============================================================="
echo " sources read (sha256, first 12):"
for f in PROOFS.md audit/quoted-names.txt audit/numerals.sh audit/pointers.sh \
         audit/ship.sh audit/views.sh archive/PROOFS-round6.md; do
  printf '   %-28s %s\n' "$f" "$(sha256sum "$f" | cut -c1-12)"
done
echo

SBOX=/tmp/r7s_w1_sandbox_$$
mkdir -p "$SBOX"
tar -cf - --exclude='*.zip' --exclude='*.olean' . | (cd "$SBOX" && tar -xf -)

# --- I1: baseline resolver ---------------------------------------------------
( cd "$SBOX" && sh audit/pointers.sh ) > /tmp/r7s_w1_p0.txt 2>&1
if [ $? -eq 0 ]; then res PASS "I1-pointers-baseline" "clean tree copy: exit 0, $(grep -c 'pointers checked' /tmp/r7s_w1_p0.txt) docs"
else res FAIL "I1-pointers-baseline" "resolver fails on pristine copy -- see /tmp/r7s_w1_p0.txt"; fi

# --- I2: the rule at the top of the phantoms section -------------------------
QN=audit/quoted-names.txt
sec=$(grep -n -- '-- phantoms' "$QN" | head -1 | cut -d: -f1)
rule=$(grep -n 'must NOT double as an exemption' "$QN" | head -1 | cut -d: -f1)
n1=$(grep -n '^exactly_two_of_domain' "$QN" | head -1 | cut -d: -f1)
n2=$(grep -n '^totally_made_up_theorem_name' "$QN" | head -1 | cut -d: -f1)
if [ -n "$sec" ] && [ -n "$rule" ] && [ -n "$n1" ] && [ -n "$n2" ] \
   && [ "$sec" -lt "$rule" ] && [ "$rule" -lt "$n1" ] && [ "$n1" -lt "$n2" ]; then
  res PASS "I2-rule-at-top" "phantoms@$sec < rule@$rule < exactly_two_of_domain@$n1 < totally_made_up@$n2; both stay exempt"
else
  res FAIL "I2-rule-at-top" "section/rule/name order wrong (sec=$sec rule=$rule n1=$n1 n2=$n2)"
fi
grep -q 'a name that is ALSO the documented FALSIFIER' "$QN" \
  && res PASS "I2-rule-wording" "'a name that is ALSO the documented FALSIFIER must NOT double as an exemption'" \
  || res FAIL "I2-rule-wording" "the one-rule sentence is absent"

# --- I3: the offered falsifier, run ------------------------------------------
printf '\nA planted fresh phantom for the live test: `xq_fresh_phantom_probe_w1` is cited here.\n' >> "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/pointers.sh ) > /tmp/r7s_w1_p1.txt 2>&1
rc=$?
if [ $rc -ne 0 ] && grep -q 'UNRESOLVED.*xq_fresh_phantom_probe_w1' /tmp/r7s_w1_p1.txt; then
  res PASS "I3-fresh-phantom-bites" "planted fresh name -> UNRESOLVED, exit $rc (the G1 repair holds)"
else
  res FAIL "I3-fresh-phantom-bites" "fresh phantom did NOT fire (exit $rc)"
fi
# restore (printf added two lines), then the DESIGNED miss: exempt name stays quiet
sed -i '$d' "$SBOX/PROOFS.md"; sed -i '$d' "$SBOX/PROOFS.md"
printf '\nThe corrections discuss `totally_made_up_theorem_name` again here.\n' >> "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/pointers.sh ) > /tmp/r7s_w1_p2.txt 2>&1
if [ $? -eq 0 ]; then
  res PASS "I3-exempt-name-designed-miss" "the DISCUSSED name passes by design (exemption necessary; falsifier must be fresh)"
else
  res FAIL "I3-exempt-name-designed-miss" "exempt discussed name fired -- exemption list broken"
fi
( cd "$SBOX" && sed -i '$d' PROOFS.md; sed -i '$d' PROOFS.md )

# --- I4: the repaired sentence -----------------------------------------------
if grep -q 'see `audit/quoted-names.txt` for what is exempt and why' PROOFS.md; then
  res PASS "I4-ledger-points-at-file" "\"This correction says \\\"see audit/quoted-names.txt for what is exempt and why\\\" rather than enumerating the lists in prose\""
else
  res FAIL "I4-ledger-points-at-file" "repaired pointer sentence absent from PROOFS.md"
fi

# --- I5: the reason column is unchecked (prediction premise, live) -----------
sed -i 's|# F1: scratch name that never became a theorem;|# DELIBERATELY WRONG REASON planted by r7s_w1;|' "$SBOX/audit/quoted-names.txt"
( cd "$SBOX" && sh audit/pointers.sh ) > /tmp/r7s_w1_p3.txt 2>&1
if [ $? -eq 0 ]; then
  res PASS "I5-reason-column-unchecked" "reason rewritten to nonsense; resolver still exits 0 -- membership only (their round-8 prediction's premise, CONFIRMED live)"
else
  res FAIL "I5-reason-column-unchecked" "resolver reacted to a comment edit -- premise wrong"
fi
cp audit/quoted-names.txt "$SBOX/audit/quoted-names.txt"

# --- I6: shipped numeral exemptions carry no G3/HANDOFF review number --------
EX=$(sed -n "/<<'EXEMPT'/,/^EXEMPT$/p" audit/numerals.sh | grep -vE '^\s*#|EXEMPT|^\s*$' | tr -d ' ')
bad=""
for n in 199 2610 2766 126 104 561 535 191 320 200; do
  echo "$EX" | grep -qx "$n" && bad="$bad $n"
done
if [ -z "$bad" ]; then
  res PASS "I6-no-G3-exemptions" "static list = {$(echo $EX | tr '\n' ' ')}; none of 199/2610/2766/126/104/561/535/191/320/200 (reversal shipped)"
else
  res FAIL "I6-no-G3-exemptions" "review numbers found exempt:$bad"
fi
grep -q 'the pre-ship audit flagged that as a G1 recreation' audit/numerals.sh \
  && res PASS "I6-reversal-note" "the NOTE records the exemption reversal + the 2766 false-reason catch in the shipped script" \
  || res FAIL "I6-reversal-note" "reversal NOTE absent from numerals.sh"

# --- I7: baseline flag set == declared benign review set ---------------------
( cd "$SBOX" && sh audit/numerals.sh ) > /tmp/r7s_w1_n0.txt 2>&1
nrc=$?
got=$(awk '/^  REVIEW/{print $2}' /tmp/r7s_w1_n0.txt | sort -un | tr '\n' ' ')
want="104 126 191 199 200 320 535 561 2610 2766 "
if [ "$got" = "$want" ] && [ $nrc -eq 1 ]; then
  res PASS "I7-benign-set-exact" "flags = {$got} == DECLARED-GAPS review list; exit 1 (quarantined review list, not a gate)"
else
  res FAIL "I7-benign-set-exact" "got {$got} rc=$nrc, want {$want} rc=1"
fi
grep -q 'REVIEW ITEM (norm 16 quarantine), not a proof of error' /tmp/r7s_w1_n0.txt \
  && res PASS "I7-quarantine-language" "output states flags are review items, not verdicts" \
  || res FAIL "I7-quarantine-language" "quarantine language missing from live output"

# --- I8: fresh planted count bites -------------------------------------------
printf '\nThis copy gained exactly 4271 theorems overnight.\n' >> "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/numerals.sh ) > /tmp/r7s_w1_n1.txt 2>&1
if awk '/^  REVIEW/{print $2}' /tmp/r7s_w1_n1.txt | grep -qx 4271; then
  res PASS "I8-fresh-count-bites" "planted 4271 flagged (delta over baseline; falsifier live)"
else
  res FAIL "I8-fresh-count-bites" "planted 4271 NOT flagged"
fi
sed -i '$d' "$SBOX/PROOFS.md"; sed -i '$d' "$SBOX/PROOFS.md"

# --- I9: retro-run on the round-6 ledger (the ledger's own sentence, executed)
cp archive/PROOFS-round6.md "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/numerals.sh ) > /tmp/r7s_w1_n2.txt 2>&1
r6got=$(awk '/REVIEW.*PROOFS.md/{print $2}' /tmp/r7s_w1_n2.txt | sort -un | tr '\n' ' ')
miss=""
for n in 199 2610 126 104; do echo "$r6got" | tr ' ' '\n' | grep -qx "$n" || miss="$miss $n"; done
if [ -z "$miss" ]; then
  res PASS "I9-round6-retro" "round-6 ledger flags include the G3 counts {199 2610 126 104} among {$r6got} -- the shipped sentence is TRUE"
else
  res FAIL "I9-round6-retro" "missing expected round-6 flags:$miss (got {$r6got})"
fi
cp PROOFS.md "$SBOX/PROOFS.md"

# --- I10: design boundary vs the gift ---------------------------------------
printf '\nA two-digit probe: 73 pointers resolve in this sentence.\n' >> "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/numerals.sh ) > /tmp/r7s_w1_n3.txt 2>&1
if awk '/^  REVIEW/{print $2}' /tmp/r7s_w1_n3.txt | grep -qx 73; then
  res NOTE "I10-two-digit-scanned" "unexpected: 73 flagged (regex wider than read)"
else
  res NOTE "I10-two-digit-blind" "2-digit numerals are OUTSIDE the shipped regex [0-9][0-9,]+[0-9] (>=3 chars): planted '73 pointers' not flagged. Divergence from the gift (>=2 digits) and from the header's 'every multi-digit number'. Round-6's '72 pointers' G3 item is invisible to this build. REVIEW ITEM."
fi
sed -i '$d' "$SBOX/PROOFS.md"; sed -i '$d' "$SBOX/PROOFS.md"

# --- I11: ship.sh enumerate-or-forbid against the REAL crate manifest --------
REQ=$(awk '/^REQUIRED="/{f=1;next} f&&/^"/{f=0} f' audit/ship.sh | grep -v '^\s*$')
nreq=$(echo "$REQ" | grep -c .)
ALLOWED_PAT=$(grep "^ALLOWED_PAT=" audit/ship.sh | sed "s/^ALLOWED_PAT='//;s/'.*//")
MANIFEST='Anyon.lean
Exchangeable.lean
HANDOFF.md
Interchange.lean
MagicSquare.lean
PROOFS.md
REGISTER.md
ROUND2.md
ROUND3.md
ROUND4.md
ROUND5.md
ROUND6.md
ROUND7.md
Rigidity.lean
Verlinde.lean
archive/PROOFS-round1.md
archive/PROOFS-round2.md
archive/PROOFS-round3.md
archive/PROOFS-round4.md
archive/PROOFS-round5.md
archive/PROOFS-round6.md
audit/audit_c1_check.py
audit/axioms-round4.txt
audit/axioms-round5.txt
audit/axioms-round6.txt
audit/axioms-round7.txt
audit/axioms.sh
audit/numerals.sh
audit/pointers.sh
audit/quoted-names.txt
audit/ship.sh
audit/transcript-round4.txt
audit/transcript-round5.txt
audit/transcript-round6.txt
audit/transcript-round7.txt
audit/transcript.sh
audit/transcription.sh
audit/verify_anyon.py
audit/verify_anyon_r2.py
audit/verify_c3.py
audit/verify_exchangeable_r2.py
audit/views.sh
lean-toolchain'
# (manifest above transcribed from the arrived workshop-lean-round7.zip,
#  sha256 5822df2e2656e01c3f4054321fb7c82508a174a3a4f0572e5f03a304c1d6bba6;
#  cross-checked live below when that zip is present on this machine)
nman=$(printf '%s\n' "$MANIFEST" | grep -c .)
nallow=0; nstow=0; stows=""
for e in $MANIFEST; do
  if printf '%s\n' $REQ | grep -qxF "$e"; then :
  elif printf '%s' "$e" | grep -qE "$ALLOWED_PAT"; then nallow=$((nallow+1))
  else nstow=$((nstow+1)); stows="$stows $e"; fi
done
if [ "$nman" -eq 43 ] && [ "$nreq" -eq 38 ] && [ "$nallow" -eq 5 ] && [ "$nstow" -eq 0 ]; then
  res PASS "I11-enumerate-or-forbid" "43 manifest = 38 REQUIRED + 5 ALLOWED($ALLOWED_PAT) + 0 unlisted"
else
  res FAIL "I11-enumerate-or-forbid" "manifest=$nman req=$nreq allowed=$nallow stowaways=$nstow:$stows"
fi
# the same logic must CATCH a stowaway
caught=0
for e in PROOFS.md.bak audit/notes.txt; do
  if printf '%s\n' $REQ | grep -qxF "$e"; then :
  elif printf '%s' "$e" | grep -qE "$ALLOWED_PAT"; then :
  else caught=$((caught+1)); fi
done
[ "$caught" -eq 2 ] && res PASS "I11-stowaway-bite" "planted PROOFS.md.bak + audit/notes.txt -> both refused by the same rule" \
                    || res FAIL "I11-stowaway-bite" "planted stowaways slipped ($caught/2 caught)"
Z=/root/.claude/uploads/2f80c594-7369-5679-8dd4-4edf1999b180/3fe2366a-workshopleanround7.zip
if [ -f "$Z" ]; then
  if [ "$(unzip -Z1 "$Z" | sort)" = "$(printf '%s\n' "$MANIFEST" | sort)" ]; then
    res PASS "I11-manifest-is-real" "embedded manifest == live listing of the arrived crate ($(sha256sum "$Z" | cut -c1-12)...)"
  else
    res FAIL "I11-manifest-is-real" "embedded manifest drifted from the arrived crate"
  fi
else
  res NOTE "I11-manifest-is-real" "arrived crate zip not on this machine; embedded manifest used as recorded"
fi
nbak=$(find . -name '*.bak' -type f | grep -c . || true)
[ "$nbak" -eq 0 ] && res PASS "I11-no-bak-in-tree" "find . -name '*.bak' -> none" \
                  || res FAIL "I11-no-bak-in-tree" "$nbak .bak file(s) in tree"

# --- I12: views.sh -- out-of-tree backup, idempotent render, drift bite ------
( cd "$SBOX" && sh audit/views.sh check ) > /tmp/r7s_w1_v0.txt 2>&1
[ $? -eq 0 ] && res PASS "I12-views-check-live" "VIEW blocks match instruments; all six source stamps match tree" \
             || res FAIL "I12-views-check-live" "views.sh check fails on pristine copy"
h0=$(sha256sum "$SBOX/PROOFS.md" | cut -c1-64)
( cd "$SBOX" && sh audit/views.sh render ) > /tmp/r7s_w1_v1.txt 2>&1
h1=$(sha256sum "$SBOX/PROOFS.md" | cut -c1-64)
inbak=$(find "$SBOX" -name '*.bak*' -type f | grep -c . || true)
outbak=$(grep -o 'backed up out-of-tree at /tmp/[^ ]*' /tmp/r7s_w1_v1.txt | sed 's/.*at //')
if [ "$h0" = "$h1" ] && [ "$inbak" -eq 0 ] && [ -n "$outbak" ] && [ -f "$outbak" ]; then
  res PASS "I12-render-out-of-tree" "render idempotent on clean tree; backup at $outbak, ZERO .bak in tree (stowaway eliminated at source)"
else
  res FAIL "I12-render-out-of-tree" "h0=h1:$([ "$h0" = "$h1" ] && echo yes || echo no) inbak=$inbak outbak=$outbak"
fi
sed -i 's/olean=2766400 bytes/olean=2766401 bytes/' "$SBOX/PROOFS.md"
( cd "$SBOX" && sh audit/views.sh check ) > /tmp/r7s_w1_v2.txt 2>&1
if [ $? -ne 0 ] && grep -q 'DRIFTED' /tmp/r7s_w1_v2.txt; then
  res PASS "I12-drift-bite" "one corrupted byte in a VIEW -> DRIFTED, exit 1"
else
  res FAIL "I12-drift-bite" "corrupted VIEW not caught"
fi

rm -rf "$SBOX"
echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: r7s_w1 -- every check PASS (NOTEs are review items).  PASS."
else
  echo "RESULT: r7s_w1 -- at least one FAIL above."
fi
exit $fail
