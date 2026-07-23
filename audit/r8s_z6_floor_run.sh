#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z6_floor_run.sh -- ROUND-8 TERMINAL AUDIT, seat Z, check R6.
#
# RUN THE FLOOR AT CLOSE.  The 29 benches are the ground the tower stands
# on; the terminal audit re-runs every one of them via run_all.py.
#
# The run happens in a SCRATCH COPY of /home/claude/workshop, because
# run_all.py rewrites WELD_REPORT.txt in its working directory and the
# shipped WELD_REPORT.txt is part of the byte-verified record (R2) --
# verify the artifact, do not overwrite it.  The benches executed are
# byte-identical to both the workshop and the crate's floor/ (r8s_z2).
#
# PASS = run_all.py exits 0, all 29 benches [PASS], zero [FAIL], and the
# coker floor bench (sheaf_cohomology) prints rank M = 5, rank [M|b] = 6,
# coker(M) = Z_2 -- the ground under the round-8 headline.
#
# Standalone: sh + python3 (numpy for the benches).  Exit 0 = PASS.
# ---------------------------------------------------------------------------
set -u
WS=/home/claude/workshop
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT

echo "=============================================================="
echo " R6 -- THE FLOOR, RE-RUN AT CLOSE (all 29 benches, scratch copy)"
echo "=============================================================="
cp "$WS"/*.py "$W"/ || { echo "FAIL: could not stage benches"; exit 1; }
N=$(ls "$W"/*.py | wc -l | tr -d ' ')
echo " staged: $N python files (29 benches + run_all.py) -> $W"

cd "$W" || exit 1
python3 run_all.py > "$W/weld_out.txt" 2>&1
rc=$?

npass=$(grep -c '\[PASS\]' "$W/weld_out.txt")
nfail=$(grep -c '\[FAIL\]' "$W/weld_out.txt")
echo
echo " run_all.py exit      : $rc      (want 0)"
echo " benches [PASS]       : $npass   (want 29)"
echo " benches [FAIL]       : $nfail    (want 0)"

echo
echo "--- every bench, as reported (title -> verdict) ---"
awk '
  /\[PASS\]|\[FAIL\]/ {
    v = ($0 ~ /\[PASS\]/) ? "[PASS]" : "[FAIL]"
    printf "  %-6s %s\n", v, substr(title, 1, 66); next
  }
  /^Bench|^FLATLAND/ { title = $0 }
' "$W/weld_out.txt"

echo
echo "--- the six representative benches, named in the charge ---"
for b in sheaf_cohomology grammar_stone3 grammar_hexagon modular_data \
         grammar_stone5 symmetric_statistics; do
  case "$b" in
    sheaf_cohomology)     pat="COHOMOLOGY: the obstruction priced" ;;
    grammar_stone3)       pat="the associator: Mac Lane's pentagon solved" ;;
    grammar_hexagon)      pat="the anyon braided: chirality, Yang-Baxter" ;;
    modular_data)         pat="S, T, Verlinde: the circle closes" ;;
    grammar_stone5)       pat="rigidity: why invariants cannot drift" ;;
    symmetric_statistics) pat="symmetric statistics built constructively" ;;
  esac
  if grep -qF "$pat" "$W/weld_out.txt"; then
    # the verdict is the [PASS]/[FAIL] line that follows the banner
    verdict=$(grep -A9999 -F "$pat" "$W/weld_out.txt" | grep -m1 -oE '\[(PASS|FAIL)\]')
    printf '  %-22s ran, verdict %s\n' "$b" "$verdict"
    [ "$verdict" = "[PASS]" ] || rc=1
  else
    printf '  %-22s DID NOT RUN\n' "$b"; rc=1
  fi
done

echo
echo "--- the coker ground: sheaf_cohomology's own printed facts ---"
if grep -q "rank M = 5, rank \[M|b\] = 6" "$W/weld_out.txt"; then
  grep "rank M = 5" "$W/weld_out.txt" | sed 's/^/  /'
else
  echo "  FAIL: bench did not print rank M = 5, rank [M|b] = 6"; rc=1
fi
grep -m1 "coker(M)" "$W/weld_out.txt" | sed 's/^/  /'
grep -q "Z_2" "$W/weld_out.txt" || { echo "  FAIL: no Z_2 line"; rc=1; }

echo
echo " shipped WELD_REPORT.txt untouched: $(ls -la "$WS/WELD_REPORT.txt" | awk '{print $5" bytes"}')"
echo
if [ "$rc" = 0 ] && [ "$npass" = 29 ] && [ "$nfail" = 0 ]; then
  echo "RESULT: the floor is green at close -- 29/29 benches PASS, and the"
  echo "        coker bench still computes rank 5/6, coker(M) = Z_2, the"
  echo "        ground under the round-8 headline.  PASS."
  exit 0
else
  echo "RESULT: FAIL -- the floor is not green (see above)."
  exit 1
fi
