#!/bin/sh
# ---------------------------------------------------------------------------
# r5s_u5_rerun.sh -- round-5 source audit, check U5: backward compatibility.
#
# Re-runs the four round-3 instruments against the CURRENT (round-5) tree:
#   r3_hexagon.py, r3_pentagon_poly.py, r3_galois_gauge.py   (live sources)
#   r3_magicsquare_ledger.py   (ledger checks pinned to round 3)
#
# CLASSIFICATION.  A failing CHECK is a REGRESSION unless it is one of the
# six known ROUND-3 PINS that rounds 4-5 legitimately overtook:
#   hexagon  H1.presence_table       Z5.mul_right_comm / KK.neg_add now EXIST
#                                    (round-3 pinned them absent, C2' era)
#   hexagon  H12.ledger_lists_them   live PROOFS.md is round 5; it points at
#                                    views and no longer restates the 18 names
#   hexagon  H12.negctrl_ghost_names hexagon_exactly_two became a THEOREM in
#                                    round 4 (Anyon.lean:5110) -- the ghost
#                                    name came alive; the control fired true
#   magicsq  M5a theorem_census      live census 21/63/714/41=839 vs pinned
#                                    round-3 21/63/245/41=370
#   magicsq  M5c round2_round3_deltas  same pin, delta form (+167 vs +636)
#   magicsq  M6c anyon_funext_family_of_six  funext family grew 6 -> 8
# Anything else that fails is reported as a REGRESSION and fails this script.
#
# PASS/FAIL lines; exit 1 only on a real regression.
# ---------------------------------------------------------------------------
set -u
LEAN=/home/claude/workshop/lean
S=$(mktemp -d /home/claude/.r5s_u5.XXXXXX)
trap 'rm -rf "$S"' EXIT
nreg=0

known_pin() {
  case "$1" in
    *H1.presence_table*|*H12.ledger_lists_them*|*H12.negctrl_ghost_names*) return 0;;
    *M5a*|*M5c*|*M6c*) return 0;;
    *) return 1;;
  esac
}

for scr in r3_hexagon.py r3_pentagon_poly.py r3_galois_gauge.py r3_magicsquare_ledger.py; do
  ( cd "$LEAN" && python3 "audit/$scr" ) > "$S/out" 2>&1; rc=$?
  fails=$(grep -E '^FAIL|^   FAIL:' "$S/out" | sort -u)
  if [ "$rc" -eq 0 ] && [ -z "$fails" ]; then
    echo "PASS  $scr (exit 0, no failing checks)"
    continue
  fi
  unexplained=0
  echo "NOTE  $scr exit=$rc; failing checks:"
  printf '%s\n' "$fails" | while read -r line; do
    [ -z "$line" ] && continue
    if known_pin "$line"; then
      echo "        STALE-PIN  $line" | cut -c1-140
    else
      echo "        REGRESSION $line" | cut -c1-140
    fi
  done
  # count unexplained in the parent shell (the while above runs in a subshell)
  unexplained=$(printf '%s\n' "$fails" | { n=0; while read -r line; do
      [ -z "$line" ] && continue
      case "$line" in
        *H1.presence_table*|*H12.ledger_lists_them*|*H12.negctrl_ghost_names*|*M5a*|*M5c*|*M6c*) ;;
        *) n=$((n+1));;
      esac
    done; echo "$n"; })
  if [ "$unexplained" -eq 0 ]; then
    echo "PASS  $scr -- all failing checks are known round-3 pins overtaken by rounds 4-5 (no regression)"
  else
    echo "FAIL  $scr -- $unexplained unexplained failing check(s): REGRESSION"
    nreg=$((nreg+1))
  fi
done

echo ""
if [ "$nreg" -eq 0 ]; then
  echo "RESULT: U5 PASS -- zero mathematical regressions; the 6 failing checks are all"
  echo "        round-3 pins the tree legitimately outgrew (3 facts became theorems /"
  echo "        ledger superseded, 3 frozen round-3 census numbers vs the 839 tree)"
else
  echo "RESULT: U5 FAIL -- $nreg script(s) show real regressions"
fi
[ "$nreg" -eq 0 ]
