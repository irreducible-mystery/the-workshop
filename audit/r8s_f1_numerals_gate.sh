#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_f1 — ROUND-8 FINAL AUDIT, fresh-defect seat.  The graduated numerals.sh:
# does its quoted-vs-asserted logic actually distinguish, and does its header
# describe its own scanner truthfully (two-digit sight, inline-code stripping)?
#
# Five live trials on a scratch copy of the shipped tree:
#   T1 clean tree                          -> must exit 0 (gate green at ship)
#   T2 planted bare 3-digit number (847)   -> must exit 1 (gate bites)
#   T3 same number inside "..." (quoted)   -> must exit 0 (quotation passes)
#   T4 planted bare 2-digit number (73)    -> must exit 1 (two-digit sight)
#   T5 planted `identifier_999` in code    -> must exit 0 (inline-code stripped)
#
# PASS iff all five trials land as required.  Norm 16's two directions both
# exercised: fails on a plant, passes on the clean tree.
# Usage: sh audit/r8s_f1_numerals_gate.sh   (from workshop/lean/)
# ---------------------------------------------------------------------------
set -u
SRC="$(pwd)"
W=/tmp/r8s_f1_$$
mkdir -p "$W/audit"
cp "$SRC"/PROOFS.md "$SRC"/HANDOFF.md "$SRC"/REGISTER.md "$W/" || exit 2
cp "$SRC"/*.lean "$W/" 2>/dev/null
cp "$SRC"/audit/numerals.sh "$W/audit/"
for o in transcript-round4 transcript-round5 transcript-round6 transcript-round7 \
         transcript-round8 axioms-round4 axioms-round5 axioms-round6 \
         axioms-round7 axioms-round8; do
  cp "$SRC/audit/$o.txt" "$W/audit/" 2>/dev/null
done
fail=0
res () { # $1 name  $2 want  $3 got
  if [ "$3" -eq "$2" ]; then echo "PASS  $1 (exit $3, wanted $2)"
  else echo "FAIL  $1 (exit $3, wanted $2)"; fail=1; fi
}
cd "$W" || exit 2
cp PROOFS.md PROOFS.orig

sh audit/numerals.sh >/dev/null 2>&1; res "T1-clean-tree-green" 0 $?

sed 's/^The first result is the mathematics\./The first result is the mathematics, and the count is 847./' \
  PROOFS.orig > PROOFS.md
sh audit/numerals.sh >/dev/null 2>&1; res "T2-bare-3digit-bites" 1 $?

sed 's/^The first result is the mathematics\./The first result is the mathematics, and the retired count was "847"./' \
  PROOFS.orig > PROOFS.md
sh audit/numerals.sh >/dev/null 2>&1; res "T3-quoted-passes" 0 $?

sed 's/^The first result is the mathematics\./The first result is the mathematics, and the count is 73./' \
  PROOFS.orig > PROOFS.md
sh audit/numerals.sh >/dev/null 2>&1; res "T4-bare-2digit-bites" 1 $?

sed 's/^The first result is the mathematics\./The first result is the mathematics, see `lemma_theorem_999` there./' \
  PROOFS.orig > PROOFS.md
sh audit/numerals.sh >/dev/null 2>&1; res "T5-inline-code-stripped" 0 $?

cd /; rm -rf "$W"
if [ "$fail" -eq 0 ]; then
  echo "RESULT: the graduated gate distinguishes quoted from asserted, sees"
  echo "        two-digit numbers, and strips inline code — its header is true"
  echo "        of its own scanner.  PASS."
else
  echo "RESULT: the gate does not behave as its header claims.  FAIL."
fi
exit $fail
