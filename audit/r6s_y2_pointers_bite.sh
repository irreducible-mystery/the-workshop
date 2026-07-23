#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_y2_pointers_bite.sh -- seat check I2: pointer-resolver mechanics,
# the F1 exemption question, and negative controls on COPIES of the tree.
#
# WHAT THIS CHECKS
#   a. live run of audit/pointers.sh on the real tree (expected PASS);
#   b. the F1 name `exactly_two_of_domain`: PROOFS.md:68 claims it is
#      "deliberately on neither list" -- is that true of the shipped
#      audit/quoted-names.txt?
#   c. (copy) remove the F1 exemption -> the resolver must FAIL, proving the
#      exemption is load-bearing (and therefore that the ledger claim is false);
#   d. (copy) plant a FRESH phantom -> must FAIL (the alarm still fires);
#   e. (copy) plant the DOCUMENTED test phantom `totally_made_up_theorem_name`
#      (PROOFS.md:72-74 says planting it reports UNRESOLVED and exits 1) --
#      does the documented falsifier still fire?
#
# NEVER touches the real tree: every mutation happens in /tmp copies.
# Exit: 0 if a/c/d PASS and b/e report the expected-by-ledger state; 1 if any
#       finding (b or e contradicting the ledger counts as a finding and the
#       script exits 1 -- the finding is the deliverable).
# ---------------------------------------------------------------------------
set -u
ROOT=$(pwd)
fail=0
W=/tmp/r6s_y2_work_$$
mkdir -p "$W"

echo "=============================================================="
echo " I2 -- pointers.sh: mechanics, F1 exemption, bite tests"
echo "=============================================================="
echo "mechanics (from reading the instrument, recorded for the report):"
echo "  pointer     = backticked [A-Za-z][A-Za-z_0-9.]* containing _ or ."
echo "  universe    = decls (namespace-qualified) + structure FIELDS"
echo "                + crate files (path AND basename) + VIEW names"
echo "                + in-script externals register + audit/quoted-names.txt"
echo "  exemptions  = TWO labeled registers, each entry with a reason:"
echo "                (1) externals heredoc inside pointers.sh,"
echo "                (2) audit/quoted-names.txt (4 labeled sections)"
echo "  docs        = PROOFS.md HANDOFF.md REGISTER.md only"
echo

# --- a. live run ------------------------------------------------------------
sh audit/pointers.sh > "$W/live.txt" 2>&1
rc=$?
tail -4 "$W/live.txt" | sed 's/^/  /'
if [ $rc -eq 0 ]; then echo "PASS: live run resolves (exit 0)"
else echo "FAIL: live run exit $rc"; fail=$((fail+1)); fi
tot=$(grep -oE 'all [0-9]+ pointers' "$W/live.txt" | grep -oE '[0-9]+')
echo "  live pointer total: ${tot:-?} (ledger's historical claim was 72)"

# --- b. is the F1 name exempted? --------------------------------------------
echo
if sed 's/#.*//' audit/quoted-names.txt | grep -q 'exactly_two_of_domain'; then
  echo "FAIL(finding): exactly_two_of_domain IS on audit/quoted-names.txt"
  echo "  (phantoms section) -- but PROOFS.md:68 says it is 'deliberately on"
  echo "  NEITHER list'.  The ledger sentence is false of the shipped file."
  grep -n 'exactly_two_of_domain' audit/quoted-names.txt | sed 's/^/    /'
  fail=$((fail+1))
else
  echo "PASS: exactly_two_of_domain is not exempted (matches PROOFS.md:68)"
fi

# --- copies -----------------------------------------------------------------
mkcopy() { rm -rf "$1"; mkdir -p "$1"; (cd "$ROOT" && tar -cf - --exclude='*.zip' .) | (cd "$1" && tar -xf -); }

# --- c. remove the exemption in a copy: resolver must catch the ledger's own
#        mentions of the phantom (proves the exemption is load-bearing).
C="$W/copy_noexempt"; mkcopy "$C"
sed -i '/^exactly_two_of_domain/d' "$C/audit/quoted-names.txt"
(cd "$C" && sh audit/pointers.sh) > "$W/noexempt.txt" 2>&1
rc=$?
if [ $rc -eq 1 ] && grep -q 'UNRESOLVED  exactly_two_of_domain' "$W/noexempt.txt"; then
  echo "PASS: with the exemption removed, pointers.sh FAILS (exit 1) on"
  echo "      the ledger's own F1 mentions -- exemption is load-bearing:"
  grep 'UNRESOLVED' "$W/noexempt.txt" | sed 's/^/    /'
else
  echo "FAIL: exemption removal did not produce the expected failure (exit $rc)"
  fail=$((fail+1))
fi

# --- d. fresh phantom in a copy: the alarm must still fire ------------------
C="$W/copy_fresh"; mkcopy "$C"
printf '\nPlanted by the seat for the bite test: `seat_r6s_phantom_probe`.\n' >> "$C/PROOFS.md"
(cd "$C" && sh audit/pointers.sh) > "$W/fresh.txt" 2>&1
rc=$?
if [ $rc -eq 1 ] && grep -q 'UNRESOLVED  seat_r6s_phantom_probe' "$W/fresh.txt"; then
  echo "PASS: fresh phantom seat_r6s_phantom_probe -> UNRESOLVED, exit 1 (bites)"
else
  echo "FAIL: fresh phantom not caught (exit $rc)"; fail=$((fail+1))
fi

# --- e. the DOCUMENTED phantom: does the ledger's own falsifier still fire? -
C="$W/copy_doc"; mkcopy "$C"
printf '\nPlanted again: `totally_made_up_theorem_name`.\n' >> "$C/PROOFS.md"
(cd "$C" && sh audit/pointers.sh) > "$W/doc.txt" 2>&1
rc=$?
if [ $rc -eq 1 ] && grep -q 'UNRESOLVED  totally_made_up_theorem_name' "$W/doc.txt"; then
  echo "PASS: documented phantom still trips the resolver, as PROOFS.md:72-74 claims"
else
  echo "FAIL(finding): planting totally_made_up_theorem_name NO LONGER trips"
  echo "  the resolver (exit $rc) -- it was itself exempted in quoted-names.txt"
  echo "  so the ledger's documented falsifier (PROOFS.md:72-74) is neutralized."
  echo "  Norm 7: a check that cannot fail is not a check; norm 14: this IS the"
  echo "  offered falsifier, run."
  fail=$((fail+1))
fi

rm -rf "$W"
echo
[ $fail -eq 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL ($fail finding(s) above)"
exit $((fail>0))
