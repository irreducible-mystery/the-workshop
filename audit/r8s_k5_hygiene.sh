#!/bin/sh
# r8s_k5_hygiene.sh -- ROUND-8 TERMINAL AUDIT, K5 (the coker seat).
# Hygiene of the NEW section (MagicSquare.lean lines 473-692):
#   * no sorry / native_decide / set_option / import / axiom / maxHeartbeats;
#   * omega discipline: ZERO omega in the new section (the file's two omegas
#     are the pre-existing S7/S8 ones, byte-identical to round 7);
#   * the 64 x 512 exhaustion is present: image_iff_even = 6 nested cases
#     (2^6 = 64 branches) each closed by rfl over inImage's 9-bit anyB search
#     (2^9 = 512) -- NOTE it is `cases ... <;> rfl`, not the decide tactic;
#   * the section's decide uses: exactly 3, each on a closed decidable goal
#     after its variables are split;
#   * zero imports preserved file-wide.
# Exit 0 = PASS, 1 = FAIL.  (Prose-claim adjudication lives in r8s_k8.)
set -u
L=/home/claude/workshop/lean
F="$L/MagicSquare.lean"
OLD="$L/archive/src-round7/MagicSquare.lean"
fail=0
sec() { sed -n '473,692p' "$F"; }

echo "== forbidden tokens in the new section (473-692) =="
for tok in "sorry" "native_decide" "set_option" "import " "^axiom" "maxHeartbeats" "maxRecDepth" "partial def" "omega" "simp"; do
  n=$(sec | grep -c "$tok")
  printf "  %-14s %s\n" "$tok" "$n"
  [ "$n" = 0 ] || { echo "  FAIL: '$tok' appears in the new section"; fail=1; }
done

echo "== file-wide zero-imports and axiom-freedom of the source =="
n=$(grep -cE '^import|^axiom' "$F"); echo "  ^import|^axiom lines: $n"
[ "$n" = 0 ] || fail=1

echo "== the 64 x 512 exhaustion (image_iff_even) =="
if grep -qF "  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;> cases u4 <;> cases u5 <;> rfl" "$F" \
   && [ "$(sec | grep -o 'anyB fun' | wc -l)" = 9 ]; then
  echo "  OK: 6 nested cases (64 branches) x rfl-evaluation of the 9-bit anyB"
  echo "      search (512 assignments) -- the 64x512 exhaustion is present."
  echo "  NOTE: the closing tactic is rfl, NOT decide (see r8s_k8 on the ledger's wording)."
else echo "  FAIL: exhaustion shape not found"; fail=1; fi

echo "== decide uses inside the new section =="
sec | grep -n "decide" | sed 's/^/    /'
n=$(sec | grep -c "decide")
echo "  count: $n (want 3: xor_false_iff after cases a,b; cokerRel_iff after cases on"
echo "  the xor; coker_separates on a closed concrete goal)"
[ "$n" = 3 ] || fail=1
sec | grep -qF "cases a <;> cases b <;> decide" || fail=1
sec | grep -qF "cases (phiV u ⊻ phiV w) <;> decide" || fail=1
sec | grep -qF "exact absurd this (by decide)" || fail=1

echo "== omega: file has exactly the two pre-existing uses, unchanged =="
grep -n "^  omega$" "$F" | sed 's/^/    /'
n=$(grep -c "^  omega$" "$F")
[ "$n" = 2 ] || { echo "  FAIL: omega count $n != 2"; fail=1; }
# both must be byte-identical inherited lines (context check: 3 lines around each
# omega in round 8 appear verbatim in round 7)
for ln in $(grep -n "^  omega$" "$F" | cut -d: -f1); do
  ctx=$(sed -n "$((ln-2)),$((ln))p" "$F")
  if printf '%s\n' "$ctx" | { ok=1; while IFS= read -r cl; do grep -qF -- "$cl" "$OLD" || ok=0; done; [ $ok = 1 ]; }
  then echo "  OK: omega at line $ln inherits round-7 context (not a round-8 addition)"
  else echo "  FAIL: omega at line $ln context not found in round-7 source"; fail=1; fi
done
echo "  omega discipline: 0 omega in the new section => no conjunctive-goal risk added."

if [ "$fail" = 0 ]; then echo "r8s_k5_hygiene: PASS"; exit 0
else echo "r8s_k5_hygiene: FAIL"; exit 1; fi
