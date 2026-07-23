#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_f4 -- ROUND-8 FINAL AUDIT, fresh-defect seat.  The hostile class-7 assay:
# each check PASSES if the capstone's fresh prose is supported by the artifacts
# aboard, and FAILS where a fresh shipped mischaracterization is present.  On
# the shipped tree this script is the experiment's needle: exit 0 = no fresh
# defect in the assayed set; exit 1 = at least one, named.
#
#   D1  TERMINAL-TABLE TOTALITY.  The header claims "Every row any round's
#       DECLARED GAPS table ever carried, at its round-8 status."  Round 1's
#       table carried `best == 8`, `best == 5`, and `Tier 4a / 4b`; each must
#       appear in the terminal table or its Closed-en-route line.
#   D2  COKER AGREEMENT DATE.  The capstone says "left open by agreement in
#       round 2" / "rounds 2-7"; the round-4, round-5 and round-6 ledgers all
#       pin the agreement "(round 3, Q3)" and the agreement text itself is
#       ROUND3.md's Q3 answer.  The capstone must not re-date it.
#   D3  H1-REPAIR APPOSITIVE.  REGISTER's repair must not re-bind "the
#       population the transplanted reason was actually true of" away from
#       r3-r5 (its own preceding sentence, ROUND8.md, and the capstone all
#       name r3-r5).
#   D4  MANIFEST-FOLD REACH.  "a source list can no longer drift between
#       them": instruments that still carry their own hard-coded six-file
#       list are counted; the folded ones must actually read the manifest.
#
# Usage: sh audit/r8s_f4_fresh_defects.sh   (from workshop/lean/)
# ---------------------------------------------------------------------------
set -u
fail=0
ok  () { echo "PASS  $1"; }
bad () { echo "FAIL  $1"; fail=1; }
note() { echo "note  $1"; }

# --- D1: terminal-table totality ---------------------------------------------
# the terminal section runs from its header to the next '## ' heading
awk '/## THE TERMINAL GAP TABLE/{f=1} f && /## THE INSTRUMENTS/{exit} f' PROOFS.md \
  > /tmp/r8s_f4_term.$$
grep -q 'Every row any round.s DECLARED GAPS table ever carried' /tmp/r8s_f4_term.$$ \
  && ok "D1-header makes the totality claim (so it is checkable)" \
  || bad "D1-header text not found"
for row in 'best == 8' 'best == 5' 'Tier 4'; do
  if grep -qF "$row" archive/PROOFS-round1.md; then
    if grep -qF "$row" /tmp/r8s_f4_term.$$; then
      ok "D1-round-1 row '$row' accounted in the terminal section"
    else
      bad "D1-round-1 row '$row' carried by round 1's DECLARED GAPS, absent from the terminal table AND its Closed-en-route line"
    fi
  else
    note "round-1 row '$row' not found in archive; skipped"
  fi
done
note "D1-context: all three missing rows are CLOSED/ABSORBED elsewhere (best==8"
note "   and best==5 are no_perfect_script/satCount_le_five in the map's S2 line;"
note "   Tier 4a became Exchangeable.lean, the map's S4).  The defect is the"
note "   totality SENTENCE, not hidden mathematics."
rm -f /tmp/r8s_f4_term.$$

# --- D2: the coker agreement date --------------------------------------------
r3=$(grep -c 'agreement (round 3, Q3)\|agreement (Q3, round 3)' \
     archive/PROOFS-round4.md archive/PROOFS-round5.md archive/PROOFS-round6.md \
     | awk -F: '{s+=$2} END{print s}')
[ "$r3" -ge 3 ] && ok "D2-archived dating: three ledgers pin the agreement '(round 3, Q3)'" \
  || note "archived '(round 3, Q3)' found $r3 times"
grep -q 'Left kernel exact + duality cited is enough' ROUND3.md \
  && ok "D2-the agreement text itself is ROUND3.md's Q3 answer" \
  || bad "D2-agreement text not found in ROUND3.md"
if grep -q 'by agreement in round 2' PROOFS.md; then
  bad "D2-capstone dates the agreement 'in round 2' against the archived '(round 3, Q3)' (headline; the table row says 'rounds 2-7').  The proposal is round 2 (ledger Q3); the AGREEMENT is round 3."
else
  ok "D2-capstone does not re-date the agreement"
fi

# --- D3: the H1-repair appositive --------------------------------------------
if grep -q 'r3–r5 instrument population' REGISTER.md; then
  ok "D3-REGISTER names r3-r5 as the population the reason was true of"
else
  bad "D3-REGISTER lost the r3-r5 population sentence"
fi
if tr '\n' ' ' < REGISTER.md | grep -q 'r3–r7 instruments — the population the transplanted *reason was actually true of'; then
  note "D3-the closing appositive re-binds 'the population...' to r3-r7; the definite description names r3-r5 five lines up.  Existential 'some' keeps the superset reading true -- imprecise, not false.  (recorded, not failed)"
else
  ok "D3-no conflicting appositive"
fi

# --- D4: manifest-fold reach -------------------------------------------------
folded=0
for s in transcript pointers views; do
  grep -q 'audit/sources.txt' "audit/$s.sh" && folded=$((folded + 1))
done
[ "$folded" -eq 3 ] && ok "D4-transcript/pointers/views read the shared manifest" \
  || bad "D4-only $folded/3 folded instruments read the manifest"
resid=0
grep -q 'for f in Interchange MagicSquare Anyon Exchangeable Rigidity Verlinde' audit/axioms.sh \
  && { resid=$((resid + 1)); note "D4-axioms.sh still hard-codes its own six-name list"; }
grep -q '^Verlinde.lean$' audit/ship.sh \
  && { resid=$((resid + 1)); note "D4-ship.sh REQUIRED still hard-codes the six .lean names"; }
# no ACTUAL drift today: every hard-coded copy must agree with the manifest
drift=0
for m in Interchange MagicSquare Anyon Exchangeable Rigidity Verlinde; do
  grep -q "^$m.lean$" audit/sources.txt || drift=1
done
awk -F'in | ' '/for f in Interchange/{print}' audit/axioms.sh | grep -q Verlinde || drift=1
[ "$drift" -eq 0 ] && ok "D4-no actual drift today between manifest and residual copies ($resid residual hard-coded lists remain; 'can no longer drift' holds only for the folded set)" \
  || bad "D4-a residual copy already disagrees with the manifest"

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: no fresh shipped defect in the assayed set.  PASS."
else
  echo "RESULT: fresh shipped defect(s) present -- see FAIL lines.  FAIL."
  echo "        (This exit is the experiment's needle, not a broken script.)"
fi
exit $fail
