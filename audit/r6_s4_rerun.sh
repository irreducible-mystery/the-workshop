#!/bin/sh
# r6_s4_rerun.sh — ROUND-5 SEAT: round-4 source audit, check S4.
#
# Re-runs the two prior Python instruments that grep Anyon.lean by name —
#   audit/r4_claims_check.py      (round-4 claims audit, written blind)
#   audit/r3_pentagon_complete.py (round-3 pentagon audit)
# — against the CURRENT tree (round-5 sources, superset of round 4);
# diagnoses every failure/crash; re-runs r4_claims_check with its ledger
# path repointed at archive/PROOFS-round4.md (the file it was written
# against, since superseded); and diffs round-4 declaration names against
# the round-5 tree for vanished names.
#
# Expected (classified) failures:
#   C9.eight_shapes, C9.multiplicities      — E1; resolved from source by
#       r6_s3_shapes.py (criterion = in-file lemma bookkeeping; the 8 are
#       merges 21=17+4, 3=1+2, 5=3+2 of the instrument's own 11-multiset)
#   C11.* + KeyError crash                  — stale target: PROOFS.md is now
#       the ROUND-5 ledger (new-format transcript block); repointed run below
#   P10.gap_declared_in_ledger,
#   P10.no_quiet_sufficiency_claim          — round-3 state assertions that
#       round 4 rightly falsified by PROVING sufficiency (suffQ_*,
#       pentagon_exactly_two_worlds are the 'suspects': supersession, loud)
#
# PASS/FAIL lines; exit = #UNEXPECTED failures.

LEAN=/home/claude/workshop/lean
cd "$LEAN" || exit 99
fails=0

classify () {  # $1 = failing check name -> echoes EXPECTED reason or UNEXPECTED
    case "$1" in
        C9.eight_shapes|C9.multiplicities)
            echo "EXPECTED: E1 — instrument clusters by free-ring polynomial pair (7) / entry-abstracted tree (11); the ledger's 8 is lemma bookkeeping, settled from source by r6_s3_shapes.py" ;;
        C11.hygiene_zeros|C11.parsed_all_rows)
            echo "EXPECTED: stale target — PROOFS.md superseded by the round-5 ledger (new-format transcript block, no old-style census line); round-4 ledger now at archive/PROOFS-round4.md (repointed run below)" ;;
        P10.gap_declared_in_ledger|P10.no_quiet_sufficiency_claim)
            echo "EXPECTED: supersession — round 4 PROVED pentagon sufficiency; the round-3 'gap is declared, nobody claims it' assertions are rightly false against the round-4/5 tree, and the instrument fails LOUD, which is its job" ;;
        *) echo "UNEXPECTED" ;;
    esac
}

run () {  # $1 = script, $2 = label
    out=$(python3 "$1" 2>&1)
    rc=$?
    nfail=$(printf '%s\n' "$out" | grep -c '^FAIL')
    npass=$(printf '%s\n' "$out" | grep -c '^PASS')
    crash=$(printf '%s\n' "$out" | grep -c 'Traceback')
    echo "RUN   S4:$2  exit=$rc  $npass PASS / $nfail FAIL  crash=$crash"
    unexpected=0
    for name in $(printf '%s\n' "$out" | sed -n 's/^FAIL  \([^ ]*\).*/\1/p'); do
        reason=$(classify "$name")
        case "$reason" in
            UNEXPECTED) echo "FAIL  S4:$2:$name  UNEXPECTED failure"; unexpected=$((unexpected+1));;
            *)          echo "NOTE  S4:$2:$name  $reason";;
        esac
    done
    if [ "$crash" -gt 0 ]; then
        line=$(printf '%s\n' "$out" | grep -A2 'Traceback' | tail -1)
        if [ "$2" = "r4_claims_check-vs-round5-tree" ]; then
            echo "NOTE  S4:$2:crash  KeyError at C11.ledger_block_matches_transcript — the instrument dies on the superseded PROOFS.md instead of failing the check ($line); E5(i)-class hardening gap in the OLD instrument, handled by the repointed run"
        else
            echo "FAIL  S4:$2:crash  $line"; unexpected=$((unexpected+1))
        fi
    fi
    [ "$unexpected" -gt 0 ] && fails=$((fails + unexpected))
    if [ "$unexpected" -eq 0 ]; then
        echo "PASS  S4:$2:verdict  all failures classified expected (supersession/E1), none unexpected"
    fi
}

run audit/r4_claims_check.py      r4_claims_check-vs-round5-tree
run audit/r3_pentagon_complete.py r3_pentagon_complete-vs-round5-tree

# repointed run: the round-4 assertions against the ARCHIVED round-4 ledger
tmp=$(mktemp /tmp/r4_claims_repoint_XXXX.py)
sed 's|{HERE}/PROOFS.md|{HERE}/archive/PROOFS-round4.md|' audit/r4_claims_check.py > "$tmp"
out=$(python3 "$tmp" 2>&1); rc=$?
rm -f "$tmp"
nfail=$(printf '%s\n' "$out" | grep -c '^FAIL')
npass=$(printf '%s\n' "$out" | grep -c '^PASS')
names=$(printf '%s\n' "$out" | sed -n 's/^FAIL  \([^ ]*\).*/\1/p' | tr '\n' ' ')
crash=$(printf '%s\n' "$out" | grep -c 'Traceback')
if [ "$crash" -eq 0 ] && [ "$nfail" -eq 2 ] && [ "$names" = "C9.eight_shapes C9.multiplicities " ]; then
    echo "PASS  S4:r4_claims_check-repointed-at-archived-ledger  $npass PASS / 2 FAIL, no crash: ONLY the two E1 checks fail; every C11/C12 ledger-vs-instrument check is green against archive/PROOFS-round4.md (incl. the date-field discrepancy C12, still detected)"
else
    echo "FAIL  S4:r4_claims_check-repointed-at-archived-ledger  $npass PASS / $nfail FAIL crash=$crash: [$names]"
    fails=$((fails + 1))
fi

# name persistence: every theorem/def of the round-4 Anyon must still exist
python3 - <<'EOF'
import re, sys
old = open("/home/claude/workshop/lean/archive/src-round4/Anyon.lean", encoding="utf-8").read()
new = open("/home/claude/workshop/lean/Anyon.lean", encoding="utf-8").read()
names4 = re.findall(r"^(?:theorem|def) ([A-Za-z_0-9'.]+)", old, re.M)
names5 = set(re.findall(r"^(?:theorem|def) ([A-Za-z_0-9'.]+)", new, re.M))
gone = [n for n in names4 if n not in names5]
th4 = len(re.findall(r"^theorem ", old, re.M))
th5 = len(re.findall(r"^theorem ", new, re.M))
if gone:
    print(f"FAIL  S4:name-persistence  {len(gone)} round-4 names vanished from round-5: {gone[:12]}")
    sys.exit(1)
print(f"PASS  S4:name-persistence  all {len(names4)} round-4 decls (Anyon: {th4} theorems) "
      f"still present in round-5 (Anyon: {th5} theorems, +{th5 - th4})")
EOF
[ $? -ne 0 ] && fails=$((fails + 1))

# theorem-count ties to the two censuses
python3 - <<'EOF'
import re, sys
old = open("/home/claude/workshop/lean/archive/src-round4/Anyon.lean", encoding="utf-8").read()
new = open("/home/claude/workshop/lean/Anyon.lean", encoding="utf-8").read()
ax4 = open("/home/claude/workshop/lean/audit/axioms-round4.txt", encoding="utf-8").read()
ax5 = open("/home/claude/workshop/lean/audit/axioms-round5.txt", encoding="utf-8").read()
t4 = len(re.findall(r"^theorem ", old, re.M))
t5 = len(re.findall(r"^theorem ", new, re.M))
ok4 = ("565" in ax4) and t4 == 565
ok5 = ("714" in ax5) and t5 == 714
print(f"{'PASS' if ok4 else 'FAIL'}  S4:count-ties-census-round4  src-round4 Anyon theorems={t4}, census says 565")
print(f"{'PASS' if ok5 else 'FAIL'}  S4:count-ties-census-round5  round-5 Anyon theorems={t5}, census says 714")
sys.exit(0 if (ok4 and ok5) else 1)
EOF
[ $? -ne 0 ] && fails=$((fails + 1))

echo ""
echo "S4 RESULT: $fails UNEXPECTED FAIL"
exit $fails
