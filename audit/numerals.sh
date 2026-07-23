#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  The numeral check.  GRADUATED, round 8.
#
# ADJUDICATOR DECLARATION (norm 15, this artifact's own entry):
#   WHAT THIS CHECKS: every BARE-ASSERTED multi-digit number in the ledger prose
#     matches a number in an instrument output (a rendered value) or a LABELED
#     exemption (structural / mathematical / standing).  A bare number that
#     matches neither FAILS the gate.
#   WHAT IT DOES NOT CHECK: single digits; numbers inside code (fenced ``` or
#     inline `backtick`) or VIEW blocks; numbers inside "double quotes" (those
#     are QUOTATIONS -- discussing a value, not asserting it -- and are allowed,
#     the numeral analogue of quoted-names.txt); and whether a sourced number is
#     the RIGHT one (a number can match an output and still be miscited -- that
#     is class 7, the audit loop's).
#
# GRADUATION (round 8).  Through round 7 this shipped QUARANTINED (norm 16): a
# static exemption list could not tell a quotation of a retired number from a
# live claim of it, so it flagged both and its output was a review list, not a
# gate.  Two hardenings graduate it:
#   (1) QUOTED vs ASSERTED.  A number inside "..." is a quotation and is passed;
#       only bare-asserted numbers must be sourced.  This is what lets the ledger
#       *name* a retired value (e.g. the round-6 headline it is correcting)
#       without the instrument mistaking the quotation for a fresh claim -- the
#       exact distinction whose absence forced the quarantine.  The G1 discipline
#       still holds: the live falsifier is a fresh bare-asserted number on no
#       list, and quoting history cannot defuse it.
#   (2) IT IS NO LONGER BLIND TO TWO-DIGIT NUMBERS.  The old regex needed three
#       characters, so "72" was invisible and ten two-digit exemptions were dead
#       entries the scanner could never consult.  It now sees every number of two
#       or more digits (commas stripped), and inline-code spans are removed first
#       so an identifier like `imageCount_eq_32` is not read as the number 32.
# So round 8 it is a GATE: exit 0 iff every bare-asserted numeral is sourced or
# labelled; exit 1 names the offenders.
#
# Usage:   sh audit/numerals.sh          (run from workshop/lean/)
# Exit:    0 if every bare-asserted prose numeral is sourced or exempt; 1 else.
# ---------------------------------------------------------------------------
set -u

DOCS="PROOFS.md HANDOFF.md REGISTER.md README.md VERIFY.md"
OUTPUTS="audit/transcript-round8.txt audit/axioms-round8.txt \
         audit/transcript-round7.txt audit/axioms-round7.txt \
         audit/transcript-round6.txt audit/axioms-round6.txt \
         audit/transcript-round5.txt audit/axioms-round5.txt \
         audit/transcript-round4.txt audit/axioms-round4.txt"
WORK=/tmp/wsl_numerals_$$
mkdir -p "$WORK"

echo "=============================================================="
echo " NUMERAL CHECK (graduated) -- bare-asserted numbers vs outputs"
echo "=============================================================="
echo " checks:   bare-asserted multi-digit numbers vs instrument outputs"
echo " allows:   quotations (inside \"...\"), code, VIEW blocks, single digits"
echo " GATE:     exit 1 on any bare-asserted numeral that is not sourced"
echo "=============================================================="

# every number that appears in any instrument output (rendered, trusted)
: > "$WORK/known.txt"
for o in $OUTPUTS; do
  [ -f "$o" ] && grep -oE '[0-9]+' "$o" >> "$WORK/known.txt"
done
# trust source line-counts computed on the fly (a ledger may quote a per-file
# line count without a stored output)
for f in *.lean; do wc -l < "$f"; done >> "$WORK/known.txt"
sort -u "$WORK/known.txt" -o "$WORK/known.txt"

# LABELED EXEMPTIONS (norm: exemptions are reviewable, and each has a reason).
cat > "$WORK/exempt.txt" <<'EXEMPT'
# -- structural: the year, the toolchain version fragments --
2026
432
32
# -- rounds are single-digit through 8; classes and norms are two-digit --
10
11
12
13
14
15
16
# -- mathematical constants stated as math, not as counts --
512
64
50
39
41
# -- coker(M) over GF(2)^6: |GF(2)^6| = 64, |im(M)| = 2^5 = 32, coker = Z_2 --
# (64 and 32 already above; the group order 2 is single-digit)
# -- the satCount histogram {1: 96, 3: 320, 5: 96} (bench data, MagicSquare) --
96
320
# -- the Hessian row/thousands cases the builder named (round 6) --
212
138
220
150
# -- standing historical figures, labelled: round-2 deliverable count (191),
#    the "200-line scratch" size (200), the descriptive 60-200 s compile range
#    (60); measured once, quoted since --
191
200
60
EXEMPT

grep -vE '^\s*#' "$WORK/exempt.txt" | grep -vE '^\s*$' | tr -d ' ' \
  | sort -u > "$WORK/exemptclean.txt"

fail=0
total=0
flagged=0
quoted_total=0
for d in $DOCS; do
  [ -f "$d" ] || continue
  # Strip fenced code and VIEW blocks (line level).  Then, per surviving line,
  # remove inline-code spans `...` (identifiers, literals) and quoted spans
  # "..." (quotations, allowed).  What remains is BARE-ASSERTED prose.
  awk '
    /^```/              { code = !code; next }
    /<!-- VIEW:.*BEGIN/ { view = 1; next }
    /<!-- VIEW:.*END/   { view = 0; next }
    !code && !view {
      line = $0
      gsub(/`[^`]*`/, " ", line)   # inline code -> gone
      gsub(/"[^"]*"/, " ", line)   # quotations  -> gone (allowed)
      print line
    }
  ' "$d" > "$WORK/bare_$d.txt"
  # count quoted numbers for the advisory line (transparency)
  qn=$(awk '
    /^```/              { code = !code; next }
    /<!-- VIEW:.*BEGIN/ { view = 1; next }
    /<!-- VIEW:.*END/   { view = 0; next }
    !code && !view {
      line = $0
      while (match(line, /"[^"]*"/)) {
        print substr(line, RSTART, RLENGTH); line = substr(line, RSTART+RLENGTH)
      }
    }
  ' "$d" | tr -d ',' | grep -oE '[0-9]{2,}' | wc -l | tr -d ' ')
  quoted_total=$((quoted_total + qn))
  # bare-asserted numbers, commas stripped (1,053 -> 1053), two or more digits
  n=0; bad=0
  for num in $(tr -d ',' < "$WORK/bare_$d.txt" | grep -oE '[0-9]{2,}' | sort -u); do
    n=$((n + 1))
    if grep -qxF "$num" "$WORK/known.txt" \
       || grep -qxF "$num" "$WORK/exemptclean.txt"; then
      :
    else
      printf '  UNSOURCED %-10s in %s  (bare-asserted, matches no output/exemption)\n' "$num" "$d"
      bad=$((bad + 1)); flagged=$((flagged + 1)); fail=1
    fi
  done
  total=$((total + n))
  printf '  %-14s %3d bare-asserted, %d unsourced\n' "$d" "$n" "$bad"
done

echo
printf '  (%d quoted numerals passed as quotations, not asserted)\n' "$quoted_total"
if [ "$fail" -eq 0 ]; then
  echo "RESULT: every bare-asserted prose numeral is sourced or labelled.  PASS."
else
  echo "RESULT: $flagged bare-asserted numeral(s) unsourced.  FAIL (gate)."
  echo "        Each is a bare number matching no instrument output and no labeled"
  echo "        exemption.  Source it from an instrument, quote it (put it inside"
  echo "        \"...\" if it is a quotation of a value), or add a labeled exemption."
fi
rm -rf "$WORK"
exit $fail
