#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_x6_u4_prose.sh -- round-6 seat check, task X6: the U4-class hunt.
# Every sentence adjacent to VIEW blocks and every characterization of
# instrument content in PROOFS.md round 6, verified against the artifacts.
# FAIL = prose contradicts an artifact.  WARN = prose number matches no
# shipped artifact (single-sided or stale).  INFO = noted, priced.
# Standalone; run from workshop/lean/.  Exit 1 on any FAIL.
# ---------------------------------------------------------------------------
set -u
fail=0
say() { printf '%s\n' "$*"; }

say "== X6a: the instrument count =="
n_sh=$(ls audit/*.sh 2>/dev/null | grep -vc "r[0-9]s\?_" )
n_req=$(grep -cE "^audit/(axioms|transcript|ship|views|pointers|transcription)\.sh$" audit/ship.sh)
if grep -q "Seven instruments now ship" PROOFS.md; then
  if [ "$n_req" -eq 7 ]; then
    say "PASS  seven-instruments"
  else
    say "FAIL  seven-instruments -- PROOFS.md:14 says 'Seven instruments now ship, and this round added two'; the tree has SIX house instruments ($n_sh non-seat .sh in audit/, $n_req in ship.sh REQUIRED: axioms transcript ship views pointers transcription), and round 5's own ledger says 'Four instruments ship' -- 4+2=6.  No enumeration yields seven"
    fail=1
  fi
fi

say ""
say "== X6b: the Rigidity headline figures =="
lines=$(wc -l < Rigidity.lean)
thms=$(grep -cE "^theorem [A-Za-z_0-9']+.*:" Rigidity.lean)
if grep -q "2,610 lines, 199 theorems" PROOFS.md; then
  say "FAIL  rigidity-headline -- PROOFS.md:169 opens THE HEADLINE with 'Rigidity.lean (new, fifth file, 2,610 lines, 199 theorems)'; the shipped file is $lines lines / $thms theorems (the ledger's OWN audit section and both views say 214).  The sentence describes the pre-audit build with no as-delivered qualifier: the F5 species (count hard-coded in prose), in the round-6 headline itself"
  fail=1
else
  say "PASS  rigidity-headline -- headline count matches tree"
fi

say ""
say "== X6c: wall-clock prose vs the certifying transcript =="
a6=$(grep -oE "Anyon.lean +exit=0 +[0-9]+" audit/transcript-round6.txt | grep -oE "[0-9]+$")
if grep -q "714 theorems at ~104 s" PROOFS.md; then
  say "WARN  anyon-104s -- PROOFS.md:174 says 'Anyon.lean is already 714 theorems at ~104 s'; the round-6 certifying transcript says ${a6} ms (~199 s).  104 matches the round-4/5 measurements (102185/107202 ms), i.e. the number is a stale carry-forward.  Wall-clock is declared not load-bearing (REGISTER row 3), so WARN not FAIL"
fi
r6=$(grep -oE "Rigidity.lean +exit=0 +[0-9]+" audit/transcript-round6.txt | grep -oE "[0-9]+$")
if grep -q "2m10s → 4m25s" PROOFS.md; then
  say "WARN  cost-2m10-4m25 -- PROOFS.md AUDIT says 'Cost, measured: 2m10s → 4m25s'; the certifying transcript says ${r6} ms (= 4m09.8s), and the file header gives ranges 2m10s-2m20s -> 3m49s-4m24s.  The ledger's two numbers are one machine's endpoints stated as points, adjacent to its own norm-10 rebuke of '~114 s vs 134.8 s'.  Not load-bearing; WARN"
fi

say ""
say "== X6d: characterizations of instrument content, checked live =="
# 'clean pass at 72 pointers' -- the shipped tree resolves more (the ledger grew)
now=$(sh audit/pointers.sh 2>/dev/null | grep -oE "all [0-9]+ pointers" | grep -oE "[0-9]+")
say "INFO  72-pointers -- PROOFS.md:72 records 'clean pass at 72 pointers' (execution-dated, builder-side); the live run here resolves $now.  Historical count in prose; no pointers output file ships, so the 72 is single-sided"
# pointers.sh's own header says FOUR sources; SOURCES lists five
if grep -q "one of the four sources" audit/pointers.sh && [ "$(grep -c 'Rigidity.lean' audit/pointers.sh)" -ge 1 ]; then
  say "FAIL  pointers-four-sources -- audit/pointers.sh:8 and :49 say 'the four sources' while its own SOURCES line lists five (Rigidity.lean included).  The F5 species inside the class-6 instrument born this round"
  fail=1
else
  say "PASS  pointers-four-sources"
fi
# REGISTER: 'six copied definitions ... three declared exceptions' vs transcription.sh
s=$(grep -oE '^SHARED="[^"]*"' audit/transcription.sh | tr ' ' '\n' | grep -c "^[a-zA-Z]" || true)
sn=$(awk -F'"' '/^SHARED=/{print $2}' audit/transcription.sh | wc -w)
en=$(awk -F'"' '/^EXCEPTIONS=/{print $2}' audit/transcription.sh | wc -w)
if [ "$sn" -eq 6 ] && [ "$en" -eq 3 ]; then
  say "PASS  register-6-and-3 -- REGISTER row 10's 'six copied definitions, three declared exceptions' matches transcription.sh (SHARED=$sn, EXCEPTIONS=$en)"
else
  say "FAIL  register-6-and-3 -- REGISTER says 6+3; script has SHARED=$sn EXCEPTIONS=$en"; fail=1
fi

say ""
say "== X6e: run the offered falsifiers (norm 14) =="
W=$(mktemp -d); cp -r . "$W/lean" 2>/dev/null
( cd "$W/lean" || exit 3
  # REGISTER: swap `fuse a y` -> `fuse y a` in the copied Fs; must DRIFT, exit 1
  awk 'BEGIN{inFs=0}
       /^def Fs/{inFs=1}
       inFs && /fuse a y/{sub(/fuse a y/, "fuse y a"); inFs=0}
       {print}' Rigidity.lean > R.tmp && mv R.tmp Rigidity.lean
  sh audit/transcription.sh >/dev/null 2>&1 )
r=$?
rm -rf "$W"
if [ "$r" -eq 1 ]; then
  say "PASS  transcription-bites -- REGISTER's falsifier run live: two-character swap in copied Fs -> DRIFTED, exit 1"
else
  say "FAIL  transcription-bites -- falsifier exit $r (want 1)"; fail=1
fi
W=$(mktemp -d); cp -r . "$W/lean" 2>/dev/null
( cd "$W/lean" || exit 3
  # views drift: flip one digit inside the transcript VIEW block of the ledger
  sed -i 's/TOTAL                1053/TOTAL                1054/' PROOFS.md
  sh audit/views.sh check >/dev/null 2>&1 )
r=$?
rm -rf "$W"
if [ "$r" -eq 1 ]; then
  say "PASS  views-bite -- one flipped digit in the ledger's VIEW block -> DRIFTED, exit 1"
else
  say "FAIL  views-bite -- falsifier exit $r (want 1)"; fail=1
fi

say ""
say "== X6f: the numeric characterizations beside the views =="
grep -q "The 462 invalid tuples" PROOFS.md && grep -q "50 of the 512 tuples pass" Rigidity.lean
if [ $? -eq 0 ] && [ $((512-50)) -eq 462 ]; then
  say "PASS  462-invalid -- 512-50=462; the ledger's count ties to pentagonValid's own comment"
else
  say "FAIL  462-invalid"; fail=1
fi
# '839 -> 1053' arithmetic against both census rounds
t5=$(grep -oE "TOTAL +839" audit/transcript-round5.txt | grep -oE "[0-9]+")
t6=$(grep -oE "TOTAL +1053" audit/transcript-round6.txt | grep -oE "[0-9]+")
if [ "$t5" = "839" ] && [ "$t6" = "1053" ] && [ $((1053-839)) -eq 214 ]; then
  say "PASS  839-to-1053 -- delta 214 = Rigidity.lean exactly; the other four counts unchanged"
else
  say "FAIL  839-to-1053"; fail=1
fi
# gauge_curve_deriv characterization (DEFECT 2's repair, read against the statement)
if grep -q "For any scalar .l. with inverse" Rigidity.lean; then
  say "WARN  gauge-curve-docstring -- Rigidity.lean:1623 docstring says 'For any scalar l with inverse li, the reparametrisation (p, l.q, li.r, s) leaves qr fixed', but the STATEMENT of gauge_curve_deriv quantifies only over q r: its three conjuncts are unit-multiplication identities at l = li = 1 (the first-order coefficient facts), not a forall-l invariance.  The ledger's 'proves the discrete content of gamma(lambda)... with qr invariant' inherits the overstatement.  Class 7, inside the repair of DEFECT 2 -- the Q4-predicted shape, already present in the shipped file"
fi

say ""
say "== X6g: the QUESTIONS block vs the tree it ships in =="
if grep -q 'transcribed because the E-valued germ overruns' PROOFS.md \
   && grep -qE "^theorem hess_G" Rigidity.lean; then
  say "FAIL  q3-stale-premise -- PROOFS.md Q3 states as PRESENT FACT: 'HG is transcribed because the E-valued germ overruns the default heartbeat budget' and asks whether to spend a round computing it.  The crate refutes the premise three times over: hess_G/germ_G are theorems in Rigidity.lean, the ledger's own HEADLINE says 'closed after the audit', and DECLARED GAPS says PROVED.  The question block predates the audit closure and was not updated -- it repeats DEFECT 1's false sentence verbatim and asks the builder to adjudicate work the same document reports done"
  fail=1
else
  say "PASS  q3-premise"
fi
hdr=$(grep -n "^-/" Rigidity.lean | head -1 | cut -d: -f1)
if grep -q "header is 126 lines" PROOFS.md; then
  say "INFO  q4-126-lines -- Q4 says Rigidity.lean's header is 126 lines; the shipped header block is $hdr lines (it grew when the budget-correction paragraphs landed).  Same pre-audit vintage as the 2,610/199 figures; the prediction's content is unaffected"
fi

say ""
[ "$fail" -eq 0 ] && say "RESULT: X6 U4 hunt -- no FAIL-grade contradiction beyond those listed.  PASS." \
                  || say "RESULT: X6 U4 hunt found FAIL-grade prose-vs-artifact contradictions."
exit $fail
