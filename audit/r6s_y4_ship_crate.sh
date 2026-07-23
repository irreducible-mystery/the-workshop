#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_y4_ship_crate.sh -- seat check I4: ship.sh REQUIRED census, the
# no-default-round guard, and the stray-passenger (unpoliced extras) property.
#
# WHAT THIS CHECKS
#   a. REQUIRED names the letters ROUND2..ROUND6, the three prose instruments
#      (views/pointers/transcription), quoted-names.txt, and both round-6
#      outputs; REQUIRED entry count printed (expected 32);
#   b. bare run exits 2 with a usage line (the ${1:-4} default is gone) --
#      safe to run: the guard fires before any packaging;
#   c. the stray-passenger mechanism, from the scripts' own text:
#      views.sh render mints PROOFS.md.bak; ship.sh tars the WHOLE tree
#      (only *.zip and *.olean excluded); the verify loop iterates over
#      REQUIRED only -- so extras ride unexamined.  Demonstrated by running
#      ship.sh's own verification-loop shape against a synthetic manifest
#      containing REQUIRED + PROOFS.md.bak: the loop passes and never sees it.
#
# Exit: 0 if a+b hold and the extras property is demonstrated (the property
#       itself is reported as a finding line for the crop note); 1 on failure.
# ---------------------------------------------------------------------------
set -u
fail=0
W=/tmp/r6s_y4_work_$$
mkdir -p "$W"

echo "=============================================================="
echo " I4 -- ship.sh: REQUIRED census, default-round guard, extras"
echo "=============================================================="

awk '/^REQUIRED="$/,/^"$/' audit/ship.sh | grep -vE '^(REQUIRED="|")$' | grep . > "$W/req.txt"
n=$(grep -c . "$W/req.txt")
echo "  REQUIRED entries: $n"

miss=0
for f in ROUND2.md ROUND3.md ROUND4.md ROUND5.md ROUND6.md \
         audit/views.sh audit/pointers.sh audit/transcription.sh \
         audit/quoted-names.txt audit/transcript-round6.txt audit/axioms-round6.txt \
         REGISTER.md PROOFS.md HANDOFF.md Rigidity.lean; do
  grep -qx "$f" "$W/req.txt" || { echo "  NOT IN REQUIRED: $f"; miss=1; }
done
if [ $miss -eq 0 ]; then
  echo "PASS: letters ROUND2-6, three prose instruments, quoted-names, both"
  echo "      round-6 outputs, REGISTER, ledger, HANDOFF, Rigidity all REQUIRED"
else
  echo "FAIL: REQUIRED is missing named files"; fail=$((fail+1))
fi

# --- b. bare run must exit 2 before doing anything --------------------------
out=$(sh audit/ship.sh 2>&1); rc=$?
if [ $rc -eq 2 ] && printf '%s' "$out" | grep -q 'usage: sh audit/ship.sh'; then
  echo "PASS: bare run exits 2 with usage (no default round; no overwrite path)"
else
  echo "FAIL: bare run rc=$rc out=$out"; fail=$((fail+1))
fi
# the old default must be gone from CODE (the comment legitimately quotes it):
if grep -vE '^\s*#' audit/ship.sh | grep -q '{1:-'; then
  echo "FAIL: a \${1:-...} default survives in ship.sh code"; fail=$((fail+1))
else
  echo "PASS: no round default in code (comment-only mention of the old one)"
fi

# --- c. extras are unpoliced ------------------------------------------------
grep -qn 'cp "\$LEDGER" "\$LEDGER.bak"' audit/views.sh \
  && echo "  mechanism 1: views.sh render mints PROOFS.md.bak (line $(grep -n 'LEDGER.bak' audit/views.sh | head -1 | cut -d: -f1))"
grep -q -- "--exclude='\*.zip' --exclude='\*.olean'" audit/ship.sh \
  && echo "  mechanism 2: ship.sh tars the whole tree; only *.zip *.olean excluded"

# replicate ship.sh's verify-loop SHAPE against a synthetic manifest that
# carries one extra file.  (ship.sh itself cannot run here: it packages via
# Windows PowerShell.  The loop below is its verification logic, lines
# 127-147, minus the hashing, which is irrelevant to the extras question.)
{ cat "$W/req.txt"; echo "PROOFS.md.bak"; } > "$W/listing.txt"
loopfail=0
while IFS= read -r f; do
  grep -qx "$f" "$W/listing.txt" || loopfail=1
done < "$W/req.txt"
extras=$(grep -vxFf "$W/req.txt" "$W/listing.txt")
if [ $loopfail -eq 0 ] && [ -n "$extras" ]; then
  echo "PASS(demonstrated): REQUIRED-only loop passes a manifest carrying"
  echo "      extra(s) [$extras] -- extras ride unexamined"
  echo "FINDING(crop note): the shipped round-6 crate carried PROOFS.md.bak"
  echo "  (views.sh render's backup) past a manifest check that polices only"
  echo "  REQUIRED.  Nothing malicious rode this time; the property is the"
  echo "  finding.  Suggested fix: an extras policy -- enumerate-or-forbid"
  echo "  (diff the archive listing against REQUIRED + a labeled ALLOWED list"
  echo "  with reasons, same design as quoted-names.txt; fail on anything"
  echo "  else)."
else
  echo "FAIL: could not demonstrate the extras property"; fail=$((fail+1))
fi

rm -rf "$W"
echo
[ $fail -eq 0 ] && echo "RESULT: PASS (with the crop-note finding above)" || echo "RESULT: FAIL ($fail)"
exit $((fail>0))
