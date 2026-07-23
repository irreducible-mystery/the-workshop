#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z7_gates_crate.sh -- ROUND-8 TERMINAL AUDIT, seat Z, check R7.
#
# THE FOUR GATES, RUN IN THE CRATE UNIVERSE.  The crate at /tmp/r8crate is
# the artifact that ferries; norm 12 says verify the artifact, not the
# tree.  All four prose gates must pass THERE, where floor/ rides and the
# pointer universe is the crate's own:
#
#   pointers.sh       -- every prose pointer resolves (expected: all 123)
#   views.sh check    -- VIEW blocks match instruments; stamps match tree
#   transcription.sh  -- Rigidity/Verlinde copies byte-match Anyon
#   numerals.sh       -- GATE (graduated round 8): every bare-asserted
#                        numeral sourced or labeled; quoted-vs-asserted
#
# Each gate's RESULT line is recorded verbatim.  Exit 0 = all four PASS.
#
# Standalone: sh + the crate itself.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
set -u
C=/tmp/r8crate
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
fail=0

echo "=============================================================="
echo " R7 -- THE FOUR GATES IN THE CRATE UNIVERSE ($C)"
echo "=============================================================="
cd "$C" || { echo "FAIL: no crate"; exit 1; }

run_gate() {  # $1 = label, $2... = command
  label=$1; shift
  echo
  echo "--- gate: $label ---"
  "$@" > "$W/out.txt" 2>&1
  rc=$?
  # record the RESULT line(s) verbatim, plus the summary counts
  grep -E '^RESULT|pointers checked|bare-asserted,|^  ok |^  identical|quoted numerals' \
      "$W/out.txt" | sed 's/^/  | /'
  echo "  exit code: $rc"
  if [ "$rc" -ne 0 ]; then
    echo "  GATE FAILED -- full output:"
    sed 's/^/  ! /' "$W/out.txt"
    fail=1
  fi
  cp "$W/out.txt" "$W/$label.txt"
}

run_gate pointers      sh audit/pointers.sh
run_gate views         sh audit/views.sh check
run_gate transcription sh audit/transcription.sh
run_gate numerals      sh audit/numerals.sh

echo
echo "--- the recorded PASS lines, one per gate ---"
p1=$(grep '^RESULT' "$W/pointers.txt")
p2b=$(sed -n '/^RESULT/,$p' "$W/views.txt" | tr '\n' ' ')
p3=$(grep -m1 '^RESULT' "$W/transcription.txt")
p4=$(grep -m1 '^RESULT' "$W/numerals.txt")
echo "  pointers      : $p1"
echo "  views         : $p2b"
echo "  transcription : $p3"
echo "  numerals      : $p4"

# the charge's expected reading: 123 pointers, all resolving
if echo "$p1" | grep -q "all 123 pointers resolve.  PASS."; then
  echo "  pointer count : 123, as claimed"
else
  echo "  FAIL: pointers did not report 'all 123 pointers resolve'"
  fail=1
fi
echo "$p3" | grep -q "PASS" || fail=1
echo "$p4" | grep -q "PASS" || fail=1
grep -q "PASS" "$W/views.txt" || fail=1

echo
if [ "$fail" = 0 ]; then
  echo "RESULT: all four gates PASS in the crate universe -- 123 pointers"
  echo "        resolve, views match their instruments and stamps, every"
  echo "        copied definition byte-matches, every bare-asserted numeral"
  echo "        is sourced or labeled.  PASS."
  exit 0
else
  echo "RESULT: FAIL -- at least one gate did not pass in the crate."
  exit 1
fi
