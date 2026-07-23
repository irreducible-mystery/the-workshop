#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z3_builder_bytes.sh -- ROUND-8 TERMINAL AUDIT, seat Z, check R3.
#
# BUILDER-INSTRUMENT BYTE-IDENTITY, full sweep: the 46 builder scripts
# aboard the crate (audit/r[0-9]* -- the r3-r7 certificates, gifts, and
# shell re-verifications, 29 .py + 17 .sh) must each be byte-identical to
# the original in /home/claude/workshop/lean/audit/.  For completeness the
# sweep also covers the other 24 audit/ entries aboard (the prover's 7
# gates, 12 .txt outputs/manifests, and the 5 carried verify/audit_c1
# .py), so the WHOLE audit/ wing of the crate is reconciled -- 70 of 70.
#
# Standalone: sh + cmp.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
set -u
C=/tmp/r8crate/audit
T=/home/claude/workshop/lean/audit
fail=0
nb=0; okb=0     # builder subset (r[0-9]*)
nt=0; okt=0     # the other 24

echo "=============================================================="
echo " R3 -- BUILDER-INSTRUMENT BYTE-IDENTITY: crate audit/ vs tree"
echo "=============================================================="
[ -d "$C" ] || { echo "FAIL: no $C"; exit 1; }

echo "--- the 46 builder instruments (audit/r[0-9]*) ---"
for f in "$C"/r[0-9]*; do
  b=$(basename "$f")
  nb=$((nb + 1))
  if [ ! -f "$T/$b" ]; then
    printf '  NO-TREE      %s\n' "$b"; fail=1
  elif cmp -s "$f" "$T/$b"; then
    printf '  identical    %s\n' "$b"; okb=$((okb + 1))
  else
    printf '  DIVERGED     %s\n' "$b"; fail=1
  fi
done
echo "  builder swept: $nb   identical: $okb   (claim: all 46)"
[ "$nb" = 46 ] || { echo "  FAIL: expected 46 builder scripts aboard"; fail=1; }

echo
echo "--- the other 24 audit/ entries (gates, outputs, carried .py) ---"
for f in "$C"/*; do
  b=$(basename "$f")
  case "$b" in r[0-9]*) continue ;; esac
  nt=$((nt + 1))
  if [ ! -f "$T/$b" ]; then
    printf '  NO-TREE      %s\n' "$b"; fail=1
  elif cmp -s "$f" "$T/$b"; then
    printf '  identical    %s\n' "$b"; okt=$((okt + 1))
  else
    printf '  DIVERGED     %s\n' "$b"; fail=1
  fi
done
echo "  others swept : $nt   identical: $okt   (expect all 24)"
[ "$nt" = 24 ] || { echo "  FAIL: expected 24 non-r entries"; fail=1; }

echo
if [ "$fail" = 0 ] && [ "$okb" = 46 ] && [ "$okt" = 24 ]; then
  echo "RESULT: all 46 builder instruments aboard byte-identical to the tree;"
  echo "        the full 70-entry audit/ wing reconciles exactly.  PASS."
  exit 0
else
  echo "RESULT: FAIL -- divergence above."
  exit 1
fi
