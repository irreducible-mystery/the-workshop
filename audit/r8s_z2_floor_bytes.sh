#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z2_floor_bytes.sh -- ROUND-8 TERMINAL AUDIT, seat Z, check R2.
#
# FLOOR BYTE-IDENTITY, full sweep (not spot): every one of the 33 entries
# under /tmp/r8crate/floor/ must be byte-identical to its counterpart in
# /home/claude/workshop/ -- the builder benches ferried home must be the
# benches, exactly.  Also two-sided: every workshop bench (*.py) and the
# three floor documents must appear in floor/, so nothing was dropped.
#
# Standalone: sh + cmp.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
set -u
C=/tmp/r8crate/floor
WS=/home/claude/workshop
fail=0
n=0; ok=0

echo "=============================================================="
echo " R2 -- FLOOR BYTE-IDENTITY: floor/* vs $WS/*"
echo "=============================================================="
[ -d "$C" ] || { echo "FAIL: no $C"; exit 1; }

# direction 1: every floor/ entry matches the workshop original
for f in "$C"/*; do
  b=$(basename "$f")
  n=$((n + 1))
  if [ ! -f "$WS/$b" ]; then
    printf '  NO-ORIGINAL  %-28s (not in workshop)\n' "$b"; fail=1
  elif cmp -s "$f" "$WS/$b"; then
    printf '  identical    %s\n' "$b"; ok=$((ok + 1))
  else
    printf '  DIVERGED     %-28s (crate differs from workshop)\n' "$b"; fail=1
  fi
done
echo
echo "  floor entries swept : $n   byte-identical: $ok   (claim: all 33)"
[ "$n" = 33 ] || { echo "  FAIL: expected exactly 33 floor entries"; fail=1; }

# direction 2: nothing in the workshop floor was left ashore
echo
missing=0
for f in "$WS"/*.py "$WS/FINDINGS.md" "$WS/README.md" "$WS/WELD_REPORT.txt"; do
  b=$(basename "$f")
  [ -f "$C/$b" ] || { printf '  LEFT-ASHORE  %s (in workshop, not in floor/)\n' "$b"; missing=1; }
done
[ "$missing" = 0 ] && echo "  reverse sweep       : every workshop bench + 3 documents aboard"
[ "$missing" = 0 ] || fail=1

echo
if [ "$fail" = 0 ] && [ "$ok" = 33 ]; then
  echo "RESULT: all 33 floor entries byte-identical to the workshop, both"
  echo "        directions complete.  PASS."
  exit 0
else
  echo "RESULT: FAIL -- divergence or omission above."
  exit 1
fi
