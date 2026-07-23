#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_y1_register.sh -- seat check I1: REGISTER.md census and completeness.
#
# WHAT THIS CHECKS
#   1. every artifact-class row in REGISTER.md's table names BOTH an
#      adjudicator (col 4) and a boundary / "what it does NOT cover" (col 5);
#   2. the class count, mechanically (rows numbered in col 1);
#   3. the three load-bearing declarations are present verbatim:
#      class-7 frontier, class-10 semantic boundary, row-9 self-reference;
#   4. cross-check: what PROOFS.md says the register contains vs what it does.
#
# WHAT IT DOES NOT CHECK: whether any row's adjudicator claim is TRUE about
#   its coverage (the register's own declared boundary, and class 7 itself).
#
# Usage: sh audit/r6s_y1_register.sh     (from workshop/lean/)
# Exit:  0 all PASS, 1 otherwise.
# ---------------------------------------------------------------------------
set -u
REG=REGISTER.md
LED=PROOFS.md
fail=0

echo "=============================================================="
echo " I1 -- REGISTER.md: rows, adjudicators, boundaries"
echo "=============================================================="
[ -f "$REG" ] || { echo "FAIL: no $REG"; exit 1; }

# --- 1+2: row census.  A class row is '| <n> | ... |' with numeric col 1.
rows=$(grep -cE '^\| [0-9]+ \|' "$REG")
echo "  class rows found: $rows"

bad=0
grep -E '^\| [0-9]+ \|' "$REG" | while IFS= read -r line; do :; done
# parse cols with awk (| separated; cols: 2=#,3=class,4=born,5=adjudicator,6=boundary)
grep -E '^\| [0-9]+ \|' "$REG" | awk -F'|' '
{
  n=$2; adj=$5; bnd=$6
  gsub(/^[ *]+|[ *]+$/,"",n); gsub(/^[ ]+|[ ]+$/,"",adj); gsub(/^[ ]+|[ ]+$/,"",bnd)
  a = (length(adj)>=8) ? "yes" : "MISSING"
  b = (length(bnd)>=8) ? "yes" : "MISSING"
  printf "  row %-2s adjudicator:%-8s boundary:%s\n", n, a, b
  if (a=="MISSING" || b=="MISSING") bad=1
}
END { exit bad }'
[ $? -ne 0 ] && { echo "FAIL: a row is missing an adjudicator or a boundary"; fail=1; } \
             || echo "PASS: every class row names both an adjudicator and a boundary"

# row-8 nuance, reported not failed: its boundary is a declared null.
grep -E '^\| 8 \|' "$REG" | grep -q "nothing known" \
  && echo "  NOTE: row 8 boundary is the declared null 'nothing known' (honest, but a null)"

# --- 3: the three declarations, greped as facts not names -------------------
if grep -q "Class 7 is the live one, and it is named here rather than discovered" "$REG"; then
  echo "PASS: class-7 frontier declaration present"
else echo "FAIL: class-7 frontier declaration missing"; fail=1; fi

if grep -q "cannot check that .pentOK. and .pentagonCheck. .agree., because that" "$REG"; then
  echo "PASS: class-10 semantic boundary (pentOK/pentagonCheck agreement) present"
else echo "FAIL: class-10 semantic boundary missing"; fail=1; fi

if grep -q "self-referential in a way that cannot be fully cashed out" "$REG"; then
  echo "PASS: row-9 self-reference declared"
else echo "FAIL: row-9 self-reference missing"; fail=1; fi

if grep -q "Nothing checks whether a row" "$REG"; then
  echo "PASS: register's own honesty boundary declared (no row-truth check)"
else echo "FAIL: register's own honesty boundary missing"; fail=1; fi

# --- 4: ledger prose vs register fact ---------------------------------------
claim=$(grep -oE "(nine|ten|eleven|[0-9]+) artifact classes" "$LED" | head -1)
echo "  ledger says: '$claim'; register table has: $rows classes"
case "$claim" in
  *nine*)  want=9 ;;
  *ten*)   want=10 ;;
  *eleven*) want=11 ;;
  *) want=$(printf '%s' "$claim" | grep -oE '[0-9]+') ;;
esac
if [ "${want:-0}" = "$rows" ]; then
  echo "PASS: ledger's class count matches the register"
else
  echo "FAIL: ledger's class count ($claim) != register rows ($rows) -- stale count in prose, F5 species"
  fail=$((fail + 1))
fi

echo
[ $fail -eq 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL ($fail finding(s) above)"
exit $fail
