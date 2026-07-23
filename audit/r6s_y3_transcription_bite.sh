#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_y3_transcription_bite.sh -- seat check I3: transcription.sh live +
# a one-token drift planted in a COPY (never the real tree).
#
# WHAT THIS CHECKS
#   a. live run: six copied definitions byte-identical (fuse memA isOne
#      sumOver Fs pentagonValid), three declared exceptions REPORTED
#      (Fg pentResid pentOK), and pentResid's two halves each identical to
#      pentagonCheck's beq arguments;
#   b. (copy) the builder's own documented bite: swap `fuse a y` -> `fuse y a`
#      inside the copied Fs in Rigidity.lean -- transcription.sh must report
#      DRIFTED and exit 1.
#
# Exit: 0 all PASS, 1 otherwise.
# ---------------------------------------------------------------------------
set -u
ROOT=$(pwd)
fail=0
W=/tmp/r6s_y3_work_$$
mkdir -p "$W"

echo "=============================================================="
echo " I3 -- transcription.sh: live + planted one-token drift"
echo "=============================================================="

# --- a. live ----------------------------------------------------------------
sh audit/transcription.sh > "$W/live.txt" 2>&1
rc=$?
ident=$(grep -c '^  identical' "$W/live.txt")
decl=$(grep -c '^  declared' "$W/live.txt")
if [ $rc -eq 0 ] && [ "$ident" -eq 8 ] && [ "$decl" -eq 3 ]; then
  echo "PASS: live run exit 0; 6 defs + 2 pentResid halves identical (8 lines),"
  echo "      3 exceptions declared-and-reported (Fg pentResid pentOK)"
else
  echo "FAIL: live run exit=$rc identical-lines=$ident declared-lines=$decl"
  sed 's/^/    /' "$W/live.txt"; fail=$((fail+1))
fi

# --- b. planted drift in a COPY --------------------------------------------
C="$W/copy_drift"; rm -rf "$C"; mkdir -p "$C"
(cd "$ROOT" && tar -cf - --exclude='*.zip' .) | (cd "$C" && tar -xf -)
# the builder's documented two-character bite, applied to the COPY's Rigidity
# Fs only (first occurrence of the guard clause in that file is inside Fs).
sed -i '0,/memA d (fuse a y)/s//memA d (fuse y a)/' "$C/Rigidity.lean"
if cmp -s "$C/Rigidity.lean" "$ROOT/Rigidity.lean"; then
  echo "FAIL: drift plant did not change the copy"; fail=$((fail+1))
else
  (cd "$C" && sh audit/transcription.sh) > "$W/drift.txt" 2>&1
  rc=$?
  if [ $rc -eq 1 ] && grep -q 'DRIFTED     Fs' "$W/drift.txt"; then
    echo "PASS: one-token drift in copied Fs -> 'DRIFTED  Fs', exit 1 (bites)"
    grep 'DRIFTED' "$W/drift.txt" | sed 's/^/    /'
  else
    echo "FAIL: planted drift not caught (exit $rc)"
    sed 's/^/    /' "$W/drift.txt" | head -20; fail=$((fail+1))
  fi
fi

rm -rf "$W"
echo
[ $fail -eq 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL ($fail)"
exit $((fail>0))
