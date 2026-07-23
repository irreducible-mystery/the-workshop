#!/bin/sh
# ---------------------------------------------------------------------------
# r7s_w2_crop_register.sh -- ROUND-7 SEAT: corrections-vs-artifacts, REGISTER,
# census (charge C4/C5/C6/C8).  Companion to r7s_w1_instruments.sh (live bites).
#
# WHAT THIS CHECKS
#   R1  census three ways: transcript table, axioms table (incl. free+rest and
#       per-file axiom-family sums), and an independent recount from source
#       with the house rule  awk '/^theorem [A-Za-z_0-9']+/ && /:/'
#   R2  all six source hashes + toolchain stamped identically in BOTH round-7
#       outputs and matching the tree NOW (the recompile table itself is
#       single-sided -- no Lean here -- and is noted, not re-run)
#   R3  REGISTER: row 11 born r7 with numerals.sh named; row 9 gained the
#       numerals clause; the G4 note occupies EXACTLY the ledger-stated lines
#       35-42; live diff vs the round-6 crate REGISTER when that zip is present
#   R4  norms 15-strengthened and 16 present in HANDOFF with their key clauses
#   R5  G1/G2/G3/G4 crops: every round-6 sentence the round-7 corrections quote
#       exists at the claimed site in the archived round-6 artifacts
#       -- including the check that "all 199"@561 / bump@532-537 are in
#       PROOFS-round6.md and NOT in src-round6/Rigidity.lean (see R5f FAIL)
#   R6  G5 repairs in the shipped files (gauge_curve_deriv forall-l-li +
#       cross-term; sos_G 'never measured'; in-file self-counts gone)
#   R7  Verlinde prose spot-checks (names, proof shapes, receipts stripped)
#       + the axiom-free-core claim's receipt boundary (NOTE: single-sided)
#   R8  the five carried .py: RUN here -- the REGISTER note's reason clause
#       ("some now exit nonzero on newer sources") measured against them
#   R9  the round-8 prediction extracted verbatim + the observation that its
#       class already had a round-7 instance (finding B, the 2766 reason)
#   R10 the numeral gift raced on the round-6 ledger (expect the letter's 33)
#
# WHAT IT DOES NOT CHECK: Verlinde semantics (r7s_v2/race), live instrument
# bites (r7s_w1).  NOTEs are review items (norm 16), not failures.
# Usage:   sh audit/r7s_w2_crop_register.sh       (from workshop/lean/)
# ---------------------------------------------------------------------------
set -u
fail=0
res() { printf '%-4s  %-30s %s\n' "$1" "$2" "$3"
        if [ "$1" = "FAIL" ]; then fail=1; fi; return 0; }
R6L=archive/PROOFS-round6.md
R6R=archive/src-round6/Rigidity.lean

echo "=============================================================="
echo " r7s_w2 -- CROPS vs ARTIFACTS, REGISTER, CENSUS"
echo "=============================================================="
echo " sources read (sha256, first 12):"
for f in PROOFS.md REGISTER.md HANDOFF.md Rigidity.lean Verlinde.lean \
         audit/transcript-round7.txt audit/axioms-round7.txt "$R6L" "$R6R"; do
  printf '   %-34s %s\n' "$f" "$(sha256sum "$f" | cut -c1-12)"
done
echo

# --- R1: the census, three ways ---------------------------------------------
tsum=0; asum=0; gsum=0; ok1=1
for spec in "Interchange.lean 21" "MagicSquare.lean 63" "Anyon.lean 714" \
            "Exchangeable.lean 41" "Rigidity.lean 214" "Verlinde.lean 75"; do
  f=${spec% *}; want=${spec#* }
  t=$(awk -v F="$f" '$1==F && NF==2 && $2 ~ /^[0-9]+$/ {print $2}' audit/transcript-round7.txt)
  a=$(awk -v F="${f%%.lean}" '$1==F && NF==4 && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ {print $2}' audit/axioms-round7.txt)
  fr=$(awk -v F="${f%%.lean}" '$1==F && NF==4 && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ {print $3}' audit/axioms-round7.txt)
  rs=$(awk -v F="${f%%.lean}" '$1==F && NF==4 && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ {print $4}' audit/axioms-round7.txt)
  g=$(awk "/^theorem [A-Za-z_0-9']+/ && /:/ {c++} END{print c+0}" "$f")
  if [ "$t" = "$want" ] && [ "$a" = "$want" ] && [ "$g" = "$want" ] \
     && [ $((fr+rs)) -eq "$want" ]; then
    tsum=$((tsum+t)); asum=$((asum+a)); gsum=$((gsum+g))
  else
    ok1=0; res FAIL "R1-census-$f" "transcript=$t axioms=$a grep=$g want=$want free+rest=$((fr+rs))"
  fi
done
[ "$ok1" -eq 1 ] && res PASS "R1-census-three-ways" "21+63+714+41+214+75: transcript=$tsum axioms=$asum source-grep=$gsum, all = 1128; free+rest per file consistent"
tt=$(awk '$1=="TOTAL" {print $2}' audit/transcript-round7.txt)
at=$(awk '$1=="TOTAL" {print $2" "$3" "$4}' audit/axioms-round7.txt)
[ "$tt" = "1128" ] && [ "$at" = "1128 494 634" ] \
  && res PASS "R1-totals" "TOTAL rows: transcript 1128; axioms 1128 = 494 free + 634 rest" \
  || res FAIL "R1-totals" "transcript TOTAL=$tt axioms TOTAL=$at"
famok=1
for spec in "Rigidity 124+1+30=155" "Anyon 29+8+370=407" "MagicSquare 2+45=47" "Verlinde 25=25"; do
  fn=${spec% *}; expr=${spec#* }
  got=$(awk -v F="$fn" '$1==F && /\[/{s+=$NF} END{print s+0}' audit/axioms-round7.txt)
  rest=$(awk -v F="$fn" '$1==F && NF==4 && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ {print $4}' audit/axioms-round7.txt)
  [ "$got" = "$rest" ] || { famok=0; res FAIL "R1-families-$fn" "family sum $got != rest $rest"; }
done
[ "$famok" -eq 1 ] && res PASS "R1-axiom-families" "per-file family sums == rest column (155/407/47/25); Interchange+Exchangeable have no family rows (0 rest)"
grep -q '^  sorryAx           0' audit/axioms-round7.txt && grep -q '^  Classical.choice  0' audit/axioms-round7.txt \
  && res PASS "R1-two-that-matter" "sorryAx 0, Classical.choice 0 in the shipped census" \
  || res FAIL "R1-two-that-matter" "hygiene lines absent"

# --- R2: hashes both outputs + tree; recompile table single-sided ------------
hok=1
for f in Interchange.lean MagicSquare.lean Anyon.lean Exchangeable.lean Rigidity.lean Verlinde.lean lean-toolchain; do
  th=$(sha256sum "$f" | cut -c1-64)
  grep -q "$th" audit/transcript-round7.txt && grep -q "$th" audit/axioms-round7.txt \
    || { hok=0; res FAIL "R2-hash-$f" "tree hash not stamped in both outputs"; }
done
[ "$hok" -eq 1 ] && res PASS "R2-six-hashes" "all six sources + lean-toolchain: tree sha256 stamped in BOTH round-7 outputs"
res NOTE "R2-recompile-single-sided" "the per-file exit/ms/olean table (incl. Verlinde 7609 ms, olean a14dff81...) is the third body's from-crate run; NO Lean toolchain here, so it is recorded, hash-tied to these exact sources, and not re-run"

# --- R3: REGISTER row 11, row 9, the G4 note at its stated lines -------------
grep -q '^| 11 | \*\*Numeral prose\*\* | \*\*r7\*\* | `audit/numerals.sh`' REGISTER.md \
  && res PASS "R3-row11" "row 11 numeral prose, born r7, adjudicator numerals.sh, boundary names single digits/code/VIEW + flag-not-verdict" \
  || res FAIL "R3-row11" "row 11 absent or malformed"
grep -q '`audit/numerals.sh` checks its numbers' REGISTER.md \
  && res PASS "R3-row9-amended" "row 9 adjudicator now includes 'audit/numerals.sh checks its numbers'" \
  || res FAIL "R3-row9-amended" "row 9 numerals clause absent"
l35=$(sed -n '35p' REGISTER.md); l42=$(sed -n '42p' REGISTER.md)
l34=$(sed -n '34p' REGISTER.md); l43=$(sed -n '43p' REGISTER.md)
case "$l35" in "**A note on the builder's Python instruments**"*) a35=1;; *) a35=0;; esac
case "$l42" in *"finding G4)."*) a42=1;; *) a42=0;; esac
if [ "$a35" -eq 1 ] && [ "$a42" -eq 1 ] && [ -z "$l34" ] && [ -z "$l43" ]; then
  res PASS "R3-note-lines-35-42" "the G4 note occupies EXACTLY REGISTER.md lines 35-42, as the ledger states"
else
  res FAIL "R3-note-lines-35-42" "note boundaries wrong (35='$(echo "$l35" | cut -c1-30)...' 42='...$(echo "$l42" | tail -c 20)')"
fi
RZ6=/root/.claude/uploads/2f80c594-7369-5679-8dd4-4edf1999b180/b21c5ccc-workshopleanround6.zip
if [ -f "$RZ6" ]; then
  unzip -p "$RZ6" REGISTER.md > /tmp/r7s_w2_reg6.md 2>/dev/null
  nh=$(diff /tmp/r7s_w2_reg6.md REGISTER.md | grep -c '^[0-9]')
  grep -q 'pinned' /tmp/r7s_w2_reg6.md && p6=had || p6=none
  if [ "$nh" -eq 2 ] && [ "$p6" = "none" ]; then
    res PASS "R3-diff-vs-round6" "exactly 2 hunks: row 9 amended + (row 11 & note) inserted; round-6 REGISTER had NO pin text (G4 confirmed: claim had no referent)"
    res NOTE "R3-diff-sentence" "ledger's diff sentence says 'one new row ... plus the labeled note' -- accurate for additions, but the row-9 amendment is a third change it does not mention (row 9's own text discloses it). REVIEW ITEM, low."
  else
    res FAIL "R3-diff-vs-round6" "hunks=$nh round6-pin=$p6"
  fi
else
  res NOTE "R3-diff-vs-round6" "round-6 crate zip not on this machine; row/note checks above stand alone"
fi

# --- R4: norms 15 (strengthened) and 16 -------------------------------------
grep -q 'what did this round add that nothing checks?' HANDOFF.md \
  && grep -q 'whose answer ships as a REGISTER diff' HANDOFF.md \
  && res PASS "R4-norm15" "15: adjudicator named at birth + r7 strengthening: the checklist question at crate time, 'what did this round add that nothing checks?', answer ships as a REGISTER diff -- fire, not merely catch" \
  || res FAIL "R4-norm15" "norm 15 strengthening clauses absent"
grep -q 'first output is \*\*quarantined\*\*' HANDOFF.md \
  && grep -q 'both failed on a planted defect and passed on a clean tree' HANDOFF.md \
  && res PASS "R4-norm16" "16: a new instrument's first output is quarantined -- claims to verify, not results to report, until it has both failed on a planted defect and passed on a clean tree" \
  || res FAIL "R4-norm16" "norm 16 clauses absent"

# --- R5: the crops, quoted sentence by quoted sentence ------------------------
sed -n '68p' "$R6L" | grep -q 'deliberately on \*\*neither\*\* list' \
  && res PASS "R5a-G1-quote" "r6 ledger line 68: '\`exactly_two_of_domain\` is deliberately on **neither** list' -- the denied exemption, byte-verified" \
  || res FAIL "R5a-G1-quote" "G1 quoted sentence not at r6 ledger line 68"
sed -n '169p' "$R6L" | grep -q '2,610 lines, 199 theorems' \
  && res PASS "R5b-G3-headline" "r6 ledger line 169: '2,610 lines, 199 theorems' (shipped Rigidity was 2766/214)" \
  || res FAIL "R5b-G3-headline" "headline crop site missing"
sed -n '283p' "$R6L" | grep -q 'nine artifact classes' \
  && res PASS "R5c-G3-nine" "r6 ledger line 283: 'nine artifact classes' against a ten-row REGISTER (r6 line 15 says 'class 10')" \
  || res FAIL "R5c-G3-nine" "'nine artifact classes' site missing"
sed -n '174p' "$R6L" | grep -q '~104 s' \
  && sed -n '72p' "$R6L" | grep -q '72 pointers' \
  && sed -n '631p' "$R6L" | grep -q '126 lines' \
  && res PASS "R5d-G3-rest" "~104s @174, '72 pointers' @72, '126 lines' @631 (inside the r6 Q4 prediction paragraph)" \
  || res FAIL "R5d-G3-rest" "one of ~104/72/126 crop sites missing"
sed -n '619p' "$R6L" | grep -q 'overruns the default heartbeat budget' \
  && grep -q 'germ_G' "$R6L" \
  && res PASS "R5e-G2-premise" "r6 Q3's premise ('transcribed because the E-valued germ overruns the default heartbeat budget', line 619) coexists with the same document's germ_G closure records" \
  || res FAIL "R5e-G2-premise" "G2 premise site missing"
p561=$(sed -n '561p' "$R6L" | grep -c 'all 199' || true)
p532=$(sed -n '532p' "$R6L" | grep -c 'gone stale \*by two\*' || true)
r561=$(sed -n '561p' "$R6R" | grep -c 'all 199' || true)
if [ "$p561" -eq 1 ] && [ "$p532" -eq 1 ] && [ "$r561" -eq 0 ]; then
  if grep -q 'Rigidity.lean line 561 "all 199"' PROOFS.md; then
    res FAIL "R5f-G3-misattribution" "the 'all 199'@561 + bump narration@532-537 live in PROOFS-round6.md, NOT Rigidity.lean (r6 Rigidity:561 is proof code; its Sec-10 said 'all 214 of them'@2755). The shipped G3 bullet 'Rigidity.lean line 561' points at the wrong FILE -- a fresh class-7 specimen inside the correction that reports the numeral crop. The builder's letter said 'line 561' with the LEDGER as antecedent."
  else
    res PASS "R5f-G3-attribution" "G3 bullet attributes 561/535 correctly"
  fi
else
  res FAIL "R5f-G3-sites" "expected r6-ledger 'all 199'@561 ($p561), bump@532 ($p532), r6-Rigidity clean@561 ($r561)"
fi
grep -q 'all 214 of them' "$R6R" \
  && res PASS "R5g-r6-rigidity-said-214" "r6 Rigidity.lean:2755 'all 214 of them' -- the in-file count G3 says is now removed" \
  || res FAIL "R5g-r6-rigidity-said-214" "expected r6 in-file count missing"
sed -n '163p' "$R6L" | grep -q 'pinned to the round they were written for' \
  && res PASS "R5h-G4-quote" "r6 ledger lines 160-163: 'the REGISTER records that they are pinned to the round they were written for' -- the pointer with no target (r6 REGISTER had no such row)" \
  || res FAIL "R5h-G4-quote" "G4 crop site missing"

# --- R6: G5 repairs in the shipped files -------------------------------------
grep -q 'theorem gauge_curve_deriv (l li q r : Zp) (hli : Zp.mul l li = Zp.one)' Rigidity.lean \
  && grep -q 'Zp.add (Zp.mul q (Zp.neg r)) (Zp.mul q r) = Zp.zero' Rigidity.lean \
  && res PASS "R6a-gauge-curve-fixed" "gauge_curve_deriv now genuinely forall l li with l*li=1, cross-term conjunct q*(-r)+q*r=0 present (G5 note in-file at ~1631)" \
  || res FAIL "R6a-gauge-curve-fixed" "repaired statement/conjunct absent"
awk '/THE CERTIFICATE AT THE GOLDEN POINT/,/^theorem sos_G/' Rigidity.lean | grep -q 'never measured' \
  && res PASS "R6b-sos_G-fixed" "sos_G docstring: the budget-overrun claim is quoted as retracted ('that overrun was never measured'); split now stated as a choice" \
  || res FAIL "R6b-sos_G-fixed" "sos_G docstring correction absent"
if grep -q 'all 199 of them\|all 214 of them' Rigidity.lean; then
  res FAIL "R6c-in-file-counts-gone" "Rigidity.lean still states its own count"
else
  res PASS "R6c-in-file-counts-gone" "no 'all 199/214 of them' in shipped Rigidity.lean -- a file does not state its own count"
fi
grep -qF 'f && /^$/ { exit }' audit/transcription.sh \
  && res NOTE "R6d-extractor" "transcription.sh extractor does truncate at the first blank line (letter's description accurate); the 'noted as ... fragile later' note exists only as the G5 sentence itself, no in-script note. REVIEW, very low." \
  || res NOTE "R6d-extractor" "extractor shape changed; re-read before trusting the G5 gloss"

# --- R7: Verlinde prose spot-checks ------------------------------------------
vok=1
for n in Dsq_eq_sqrt5_phi norm_Dsq M_symm M_sq rows_orthonormal dims_from_S \
         verlinde_cleared wrong_S_fails_ttt correct_S_passes_ttt \
         fuseMult_nonconstant verlinde_anti_vacuity modular_cube \
         modular_cube_mirror pp_pm_eq_D2 pm_eq_conj_pp verlinde_tau_tau \
         pp_pow4_eq pm_pow4_eq; do
  grep -q "^theorem $n" Verlinde.lean || { vok=0; res FAIL "R7-name-$n" "missing"; }
done
[ "$vok" -eq 1 ] && res PASS "R7-names" "all 18 headline theorem names exist at column 0 in Verlinde.lean"
grep -A1 '^theorem verlinde_cleared' Verlinde.lean | grep -q 'cases a <;> cases b <;> cases c <;> rfl' \
  && res PASS "R7-cleared-shape" "verlinde_cleared: forall a b c, D^2*fuseZp = verlNum, by cases+rfl over the 8 cells -- as the ledger says" \
  || res FAIL "R7-cleared-shape" "proof shape drifted from the ledger's description"
grep -A2 '^theorem wrong_S_fails_ttt' Verlinde.lean | grep -q 'decide' \
  && res PASS "R7-wrongS-decide" "Hadamard control fails (tau,tau,tau) by decide; correct_S_passes_ttt at the same cell" \
  || res FAIL "R7-wrongS-decide" "wrong-S control shape drifted"
grep -q '#print' Verlinde.lean \
  && res FAIL "R7-receipts-stripped" "#print present -- would not compile silent" \
  || res PASS "R7-receipts-stripped" "no #print in merged Verlinde.lean; AXIOM RECEIPTS header present ($(grep -c 'AXIOM RECEIPTS' Verlinde.lean) site) and empty"
res NOTE "R7-core-axiom-free-claim" "headline 'whole cleared core axiom-free, not even propext': census shows Verlinde 50 free / 25 [propext,Quot.sound], but the shipped receipts aggregate PER FILE -- which 25 carry axioms is not receipted, so the claim is single-sided here (same shape as the letter's note on Rigidity's eighteen). Suggest a per-nest census row. REVIEW ITEM."
res NOTE "R7-eight-instruments" "'Eight instruments ship' (ledger line 15): shipped house .sh = 7 (axioms transcript ship views pointers transcription numerals); 8 counts the kernel, as Q7's chain does ('kernel -> axioms -> ... -> numerals', 8 nodes). Wording review, very low."

# --- R8: the carried .py, RUN (the REGISTER note's reason clause) ------------
if command -v python3 >/dev/null 2>&1; then
  codes=""
  nz=0
  for s in audit_c1_check.py verify_anyon.py verify_anyon_r2.py verify_c3.py verify_exchangeable_r2.py; do
    timeout 180 python3 "audit/$s" >/dev/null 2>&1; rc=$?
    codes="$codes $s=$rc"; [ "$rc" -ne 0 ] && nz=$((nz+1))
  done
  if [ "$nz" -eq 0 ]; then
    res FAIL "R8-register-note-reason" "REGISTER note (lines 35-42) says of the carried audit/*.py that 'some now exit nonzero on newer sources' -- measured HERE on the round-7 tree:$codes -- ALL FIVE EXIT 0. The exit-nonzero fact is true of the r3 instruments (ROUND6.md:150-151; r6 ledger:160-163), which are NOT in their crate (43-entry manifest carries only the five verify-era .py). A correctly-formatted note whose reason clause is transplanted from a different artifact set: an instance of their own round-8 predicted class, shipped in round 7, inside an adjudicator file."
  else
    res PASS "R8-register-note-reason" "carried .py exits:$codes -- 'some now exit nonzero' holds as written"
  fi
else
  res NOTE "R8-register-note-reason" "no python3 here; the note's reason clause stays unmeasured on this machine"
fi

# --- R9: prediction verbatim + the already-scored observation ----------------
pl=$(grep -n 'Q4, the streak' PROOFS.md | cut -d: -f1)
ql=$(grep -n 'One question back, Q7' PROOFS.md | cut -d: -f1)
if [ -n "$pl" ] && [ -n "$ql" ]; then
  res PASS "R9-blocks-located" "round-8 prediction at PROOFS.md:$pl-340; the round's one question (Q7) at PROOFS.md:$ql-353 (no formal QUESTIONS block this round -- format change, noted)"
  echo "----- ROUND-8 PREDICTION, verbatim (PROOFS.md $pl..340) -----"
  sed -n "${pl},340p" PROOFS.md | sed 's/^/    | /'
  echo "----- Q7, verbatim (PROOFS.md $ql..353) -----"
  sed -n "${ql},353p" PROOFS.md | sed 's/^/    | /'
else
  res FAIL "R9-blocks-located" "prediction/question anchors missing"
fi
grep -q 'false-on-a-correctly-exempt-number' PROOFS.md \
  && grep -q 'mislabeled reason (2766 is a live' audit/numerals.sh \
  && res PASS "R9-class-already-instanced" "SCORE-RELEVANT: their own pre-ship finding B -- the 2766 'retired-value' reason, 'false-on-a-correctly-exempt-number' (PROOFS.md G3) + the numerals.sh NOTE -- is an instance of the predicted round-8 class occurring IN round 7, caught pre-ship; R8 above is a second, shipped, instance" \
  || res FAIL "R9-class-already-instanced" "finding-B text absent from ledger or numerals.sh"

# --- R10: the gift raced on the round-6 ledger --------------------------------
if command -v python3 >/dev/null 2>&1 && [ -f audit/r7_numeral_gift.py ]; then
  nfl=$(timeout 300 python3 audit/r7_numeral_gift.py --round 6 \
        --ledger archive/PROOFS-round6.md --sources archive/src-round6 2>/dev/null \
        | sed -n 's/.*REVIEW QUEUE (\([0-9]*\) distinct.*/\1/p')
  if [ "$nfl" = "33" ]; then
    res PASS "R10-gift-33" "r7_numeral_gift.py on the round-6 ledger: 33 distinct flagged -- exactly the letter's number; gift(.py, >=2-digit, X1-X3) vs shell(numerals.sh, >=3-digit, static value exemptions, 3 docs) designs both quarantined per norm 16"
  else
    res FAIL "R10-gift-33" "gift flags '$nfl' distinct (letter said 33)"
  fi
else
  res NOTE "R10-gift-33" "gift or python3 unavailable; the letter's 33 stays their-side"
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: r7s_w2 -- every check PASS (NOTEs are review items).  PASS."
else
  echo "RESULT: r7s_w2 -- FAIL(s) above are FINDINGS about shipped prose, not about the mathematics; see the report."
fi
exit $fail
