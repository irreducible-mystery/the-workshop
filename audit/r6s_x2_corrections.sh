#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_x2_corrections.sh -- round-6 seat check, task X2.
# Reconciles the round-6 ledger's CORRECTIONS section (F1-F5 + small notes)
# against the shipped tree.  Standalone; run from workshop/lean/.
# Every verdict is a PASS/FAIL line; exit 1 if any FAIL.
# ---------------------------------------------------------------------------
set -u
fail=0
say() { printf '%s\n' "$*"; }
chk() { # chk <label> <0-for-pass> <detail>
  if [ "$2" -eq 0 ]; then say "PASS  $1 -- $3"; else say "FAIL  $1 -- $3"; fail=1; fi
}

say "== X2: F1 -- the phantom exactly_two_of_domain =="
# F1a: HANDOFF carries the scratch-file account.
grep -q "development scaffolding that dissolved on merge" HANDOFF.md \
  && grep -q "audit/pointers.sh.* now catches this class" HANDOFF.md
chk "F1a-handoff-account" $? "HANDOFF records scratch-name account + pointers.sh adjudication"
# F1b: HANDOFF no longer cites the phantom BY NAME (the repair is nameless there).
n=$(grep -c "exactly_two_of_domain" HANDOFF.md || true)
[ "$n" -eq 0 ]; chk "F1b-handoff-name-gone" $? "occurrences of the name in HANDOFF.md = $n (want 0)"
# F1c: the ledger says the name is 'deliberately on neither list'.  Fact-check
# against audit/quoted-names.txt, which pointers.sh consumes as an exemption file.
if grep -v '^#' audit/quoted-names.txt | grep -q "^exactly_two_of_domain"; then
  say "FAIL  F1c-ledger-neither-list -- PROOFS.md:68 says 'deliberately on neither list', but audit/quoted-names.txt line $(grep -n '^exactly_two_of_domain' audit/quoted-names.txt | cut -d: -f1) EXEMPTS the name (phantoms section); pointers.sh can never flag it again, even as a live citation"
  fail=1
else
  say "PASS  F1c-ledger-neither-list -- name not exempted anywhere"
fi
# F1d: run the two falsifiers in a scratch copy of the tree.
W=$(mktemp -d)
cp -r . "$W/lean" 2>/dev/null
( cd "$W/lean" || exit 3
  printf '\nSee `totally_made_up_theorem_name_2` for details.\n' >> PROOFS.md
  sh audit/pointers.sh >/dev/null 2>&1 )
chk "F1d-planted-phantom-bites" $([ $? -eq 1 ] && echo 0 || echo 1) \
  "planting a fresh phantom in PROOFS.md makes pointers.sh exit 1 (ledger's own falsifier)"
rm -rf "$W"; W=$(mktemp -d); cp -r . "$W/lean" 2>/dev/null
( cd "$W/lean" || exit 3
  printf '\nThe assembly applies `exactly_two_of_domain` directly.\n' >> HANDOFF.md
  sh audit/pointers.sh >/dev/null 2>&1 )
r=$?
rm -rf "$W"
if [ "$r" -eq 0 ]; then
  say "FAIL  F1e-exemption-swallows-reliance -- a planted LIVE citation of exactly_two_of_domain passes pointers.sh (exit 0): the quoted-names exemption neutralizes the instrument for exactly the finding it was built on"
  fail=1
else
  say "PASS  F1e-exemption-swallows-reliance -- a live citation is caught"
fi

say ""
say "== X2: F2 -- pentagon_exactly_two_sharp, four conjuncts =="
blk=$(awk '/^theorem pentagon_exactly_two_sharp/,/alt_root_satisfies_pentagon⟩/' Anyon.lean)
c1=$(printf '%s' "$blk" | grep -c "pentagonCheck kRng (Fg KK.invPhi KK.b KK.b")
c2=$(printf '%s' "$blk" | grep -c "pentagonCheck kRng (Fg pAlt KK.one pAlt")
c3=$(printf '%s' "$blk" | grep -c "KK.beq KK.invPhi (KK.neg (KK.emb Z5.phi)) = false")
c4=$(printf '%s' "$blk" | grep -c "pentagon_exactly_two_worlds, rfl")
c5=$(printf '%s' "$blk" | grep -c "golden_satisfies_pentagon, alt_root_satisfies_pentagon")
[ "$c1" -ge 1 ] && [ "$c2" -ge 1 ] && [ "$c3" -ge 1 ] && [ "$c4" -ge 1 ] && [ "$c5" -ge 1 ]
chk "F2-statement-and-proof" $? "dichotomy+distinctness+both realizations in statement; proof term = <pentagon_exactly_two_worlds, rfl, golden_satisfies_pentagon, alt_root_satisfies_pentagon>"
grep -q "Builder's source\s*audit, F2" Anyon.lean || grep -q "audit, F2" Anyon.lean
chk "F2-docstring-records" $? "the docstring records the round-6 repair and the reversed-sides pattern"

say ""
say "== X2: F3 -- three stale K-domain sentences, dated updates =="
n=$(grep -c "ROUND-6 UPDATE" Anyon.lean)
[ "$n" -eq 3 ]; chk "F3-three-sites" $? "ROUND-6 UPDATE markers in Anyon.lean = $n (want 3)"
# every present-tense stale assertion sits within 25 lines of a dated update
bad=0
for ln in $(grep -n "nowhere proved in this file\|is NOT proved here" Anyon.lean | cut -d: -f1); do
  lo=$((ln>25 ? ln-25 : 1)); hi=$((ln+25))
  sed -n "${lo},${hi}p" Anyon.lean | grep -q "ROUND-6 UPDATE" || bad=$((bad+1))
done
[ "$bad" -eq 0 ]; chk "F3-all-annotated" $? "stale-tense sites without a nearby ROUND-6 UPDATE: $bad (want 0)"
say "      quote (Anyon.lean:615): '⚠ ROUND-6 UPDATE, because this paragraph went stale.  §12 *does* now prove it ...'"

say ""
say "== X2: F4 -- twelve-minutes prose =="
grep -q "twelve minutes\" -- the 12 lifted" audit/views.sh && grep -qi "seventeen minutes twenty" audit/views.sh
chk "F4-views.sh" $? "views.sh header states 17m20s; 'twelve minutes' survives only as quoted history"
grep -q "The delta is 17m20s" HANDOFF.md && grep -q 'said "twelve minutes", the 12' HANDOFF.md
chk "F4-handoff" $? "HANDOFF Ledger-as-view section states 17m20s; 'twelve minutes' only as quoted history"
# no OTHER live 'twelve minutes' anywhere in the crate docs
n=$(grep -l "twelve minutes" PROOFS.md REGISTER.md 2>/dev/null | wc -l)
[ "$n" -eq 0 ]; chk "F4-no-other-sites" $? "no further 'twelve minutes' sites in PROOFS.md/REGISTER.md"

say ""
say "== X2: F5 -- axioms.sh header =="
grep -q "DO NOT HARD-CODE THE COUNT HERE" audit/axioms.sh \
  && grep -q "statements avoid the Fin-indexed layer" audit/axioms.sh \
  && grep -q "archive/PROOFS-round3.md" audit/axioms.sh
chk "F5-explains-why" $? "comment explains WHY some MagicSquare theorems are axiom-free, forbids hard-coding, cites archive path for C1'"
# 'exactly 14' may appear only as quoted history
if grep -q 'said$' /dev/null 2>/dev/null; then :; fi
n=$(grep -c '"exactly 14"' audit/axioms.sh); m=$(grep -c 'exactly 14' audit/axioms.sh)
[ "$n" -eq "$m" ]; chk "F5-14-only-history" $? "every 'exactly 14' occurrence is inside quotes-as-history ($n of $m)"

say ""
say "== X2: the small notes =="
# a LIVE ${1:-...} default would sit on a non-comment line; the surviving
# occurrence is quoted history inside the comment block.
if grep -v '^#' audit/ship.sh | grep -q '{1:-'; then
  say "FAIL  ship-default -- a live \${1:-...} default survives outside comments"; fail=1
else
  sh audit/ship.sh >/dev/null 2>&1; r=$?
  [ "$r" -eq 2 ]; chk "ship-default" $? "no live default (comment-only history); bare run exits $r (want 2) with a usage line"
fi
ok=0
for f in ROUND2.md ROUND3.md ROUND4.md ROUND5.md ROUND6.md; do
  grep -q "^$f\$" audit/ship.sh && [ -f "$f" ] || ok=1
done
chk "letters-in-crate" $ok "ROUND2..ROUND6 letters in ship.sh REQUIRED and present in tree"
grep -q "Condensed excerpt" archive/PROOFS-round5.md
chk "drifted-demo-label" $? "round-5 ledger DRIFTED demo block now labelled a condensed excerpt"
# r3 instruments: ledger says 'the REGISTER records that they are pinned to the
# round they were written for'.  Fact-check REGISTER.md.
if grep -qi "r3_\|pinned" REGISTER.md; then
  say "PASS  r3-pins-register -- REGISTER records the pin"
else
  say "FAIL  r3-pins-register -- PROOFS.md:162-163 claims 'the REGISTER records that they are pinned to the round they were written for'; REGISTER.md contains no such record (no 'r3', no 'pinned'); the r3_*.py files themselves are also unmodified (no in-file pin added)"
  fail=1
fi

say ""
[ "$fail" -eq 0 ] && say "RESULT: X2 corrections reconcile.  PASS." \
                  || say "RESULT: X2 found discrepancies.  FAIL (see lines above)."
exit $fail
