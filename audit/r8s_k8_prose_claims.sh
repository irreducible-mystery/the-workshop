#!/bin/sh
# r8s_k8_prose_claims.sh -- ROUND-8 TERMINAL AUDIT, the zero-defect adjudicator
# for the coker seat.  Tests the shipped PROSE about the new section against
# the shipped SOURCE.  This is the script that decides whether a FRESH round-8
# prose defect shipped.  Exit 0 = no defect; exit 1 = defect(s), named.
#
# Claim A (MagicSquare.lean:12-19, shipped unchanged from round 7):
#   "Core tactics only: `cases`, `rw`, `exact`, `intro`, `have`, `apply`,
#    `show`, `first`, `rfl`, the `<;>` combinator, five uses of `decide` and
#    exactly two of `omega`."
#   Round 7: TRUE (5 decide, 2 omega, list complete).  Round 8 added S6.5.
# Claim B (PROOFS.md, THE HEADLINE): image_iff_even "is **axiom-free** -- a
#   `decide` over the 2^6 targets against 2^9 assignments".
set -u
L=/home/claude/workshop/lean
F="$L/MagicSquare.lean"
OLD="$L/archive/src-round7/MagicSquare.lean"
defects=0

count_tactic() { # count_tactic <file> <regex-token>  (block+line comments stripped)
python3 - "$1" "$2" <<'PY'
import re, sys
txt = open(sys.argv[1], encoding='utf-8').read()
out, i, depth, n = [], 0, 0, len(txt)
while i < n:
    if txt.startswith('/-', i): depth += 1; i += 2; continue
    if depth and txt.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: out.append('\n' if txt[i] == '\n' else ' '); i += 1; continue
    if txt.startswith('--', i):
        j = txt.find('\n', i); i = n if j < 0 else j; continue
    out.append(txt[i]); i += 1
print(len(re.findall(sys.argv[2], ''.join(out))))
PY
}

echo "== CLAIM A: the file-header tactic manifest (MagicSquare.lean:12-19) =="
sed -n '12,19p' "$F" | sed 's/^/  | /'
D7=$(count_tactic "$OLD" '\bdecide\b'); O7=$(count_tactic "$OLD" '\bomega\b')
D8=$(count_tactic "$F"   '\bdecide\b'); O8=$(count_tactic "$F"   '\bomega\b')
U8=$(count_tactic "$F"   '\bunfold\b'); I8=$(count_tactic "$F"   '\binduction\b')
echo "  measured (comment-stripped): round-7 decide=$D7 omega=$O7 ; round-8 decide=$D8 omega=$O8 unfold=$U8 induction=$I8"
echo "  new decide sites:"
grep -n "cases a <;> cases b <;> decide\|cases (phiV u ⊻ phiV w) <;> decide\|absurd this (by decide)" "$F" | sed 's/^/    /'
echo "  new unlisted tactics:"
grep -n "^  unfold \|  induction x using Quotient.inductionOn" "$F" | sed 's/^/    /'
if [ "$D7" = 5 ] && [ "$O7" = 2 ]; then
  echo "  round-7 header was TRUE of the round-7 file (5 decide, 2 omega)."
else echo "  NOTE: round-7 baseline unexpected (decide=$D7 omega=$O7)"; fi
if [ "$D8" != 5 ]; then
  echo "  DEFECT A1: header says 'five uses of \`decide\`'; the round-8 file has $D8."
  echo "     The three S6.5 decides (xor_false_iff, cokerRel_iff, coker_separates)"
  echo "     were added without updating the manifest."
  defects=$((defects + 1))
fi
if [ "$U8" != 0 ] || [ "$I8" != 0 ]; then
  echo "  DEFECT A2: header's 'Core tactics only: ...' list omits tactics the new"
  echo "     section uses: unfold (x$U8, cokerRel_iff) and induction (x$I8,"
  echo "     fromZ2_toZ2 via Quotient.inductionOn)."
  defects=$((defects + 1))
fi
[ "$O8" = 2 ] && echo "  (the 'exactly two of \`omega\`' half is still true: $O8.)"
echo "  precedent: this exact header went stale once before and was corrected as"
echo "  C3' (HANDOFF.md: 'stale round-1 tactic-list headers in ... MagicSquare.lean:12');"
echo "  the header's own parenthetical records that episode ('the line had gone stale')."

echo ""
echo "== CLAIM B: PROOFS.md calls image_iff_even 'a \`decide\`' =="
grep -n "a \`decide\` over the 2⁶ targets" "$L/PROOFS.md" | sed 's/^/  | /'
PROOF_LINE=$(sed -n '525,527p' "$F")
echo "  the shipped proof of image_iff_even:"
sed -n '525,527p' "$F" | sed 's/^/  | /'
if echo "$PROOF_LINE" | grep -q "decide"; then
  echo "  proof uses the decide tactic: claim wording accurate."
else
  echo "  DEFECT B1 (minor): the 2^6 x 2^9 exhaustion IS present, but it is"
  echo "     'cases u0 <;> ... <;> cases u5 <;> rfl' -- 64 branches closed by rfl"
  echo "     (kernel evaluation of the 512-leaf anyB search), NOT the \`decide\`"
  echo "     tactic the ledger names.  The word was carried forward from ROUND8.md's"
  echo "     pre-implementation estimate ('is a decide over at most 64x512 cases')."
  echo "     Quantities and the axiom-free claim are right; the mechanism-name is not."
  defects=$((defects + 1))
fi

echo ""
if [ "$defects" = 0 ]; then
  echo "r8s_k8_prose_claims: PASS -- no fresh round-8 prose defect in the coker seat"
  exit 0
else
  echo "r8s_k8_prose_claims: FAIL -- $defects fresh round-8 prose defect(s) confirmed"
  echo "  (A1/A2: one stale hygiene manifest, two symptoms; B1: mechanism mislabel.)"
  exit 1
fi
