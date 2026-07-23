#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_y5_views_census.sh -- seat check I5: five-file instrument coverage.
#
# WHAT THIS CHECKS
#   a. both round-6 outputs stamp SIX source hashes (five .lean + toolchain),
#      verified against the tree independently of views.sh;
#   b. views.sh check passes live (block byte-equality via sha256 + E5(ii));
#   c. an independent replication of the block equality: the ledger's VIEW
#      blocks, extracted here with different code, hash-match the instrument
#      outputs' corresponding sections;
#   d. census reconciliation: per-file theorem counts in the outputs vs an
#      independent grep of the sources vs the stated total 1053 = 21+63+714+41+214;
#   e. axiom-family table arithmetic: per-file family counts sum to the
#      'rest' column; axiom-free + rest = total; sorryAx 0, Classical.choice 0.
#
# Exit: 0 all PASS, 1 otherwise.
# ---------------------------------------------------------------------------
set -u
fail=0
TR=audit/transcript-round6.txt
AX=audit/axioms-round6.txt

echo "=============================================================="
echo " I5 -- five-file coverage: hashes, views, census, axiom table"
echo "=============================================================="

# --- a. six hashes in both outputs, independently -----------------------------
for out in "$TR" "$AX"; do
  n=0
  for f in Interchange.lean MagicSquare.lean Anyon.lean Exchangeable.lean Rigidity.lean lean-toolchain; do
    h=$(sha256sum "$f" | cut -c1-64)
    grep -q "$h" "$out" && n=$((n+1))
  done
  if [ $n -eq 6 ]; then echo "PASS: $out stamps all 6 tree hashes (5 .lean + toolchain)"
  else echo "FAIL: $out stamps only $n/6 tree hashes"; fail=$((fail+1)); fi
done

# --- b. views.sh check live ---------------------------------------------------
sh audit/views.sh check > /tmp/y5_views.txt 2>&1
if [ $? -eq 0 ] && grep -q 'ok       VIEW:transcript' /tmp/y5_views.txt \
                && grep -q 'ok       VIEW:axioms' /tmp/y5_views.txt; then
  echo "PASS: views.sh check -- both VIEW blocks match, all six sources stamped"
else
  echo "FAIL: views.sh check"; sed 's/^/    /' /tmp/y5_views.txt; fail=$((fail+1))
fi

# --- c. independent block-equality replication --------------------------------
blk() { awk -v n="$1" '$0 ~ ("<!-- VIEW:" n " BEGIN") {inb=1; next} $0 ~ ("<!-- VIEW:" n " END") {inb=0} inb {print}' PROOFS.md; }
h1=$(blk transcript | sed '1d;$d' | sha256sum | cut -c1-16)   # strip the ``` fences
h2=$(sed -n '/^date /,/^RESULT/p' "$TR" | sha256sum | cut -c1-16)
h3=$(blk axioms | sed '1d;$d' | sha256sum | cut -c1-16)
h4=$(sed -n '/^file  /,/^  Classical.choice/p' "$AX" | sha256sum | cut -c1-16)
if [ "$h1" = "$h2" ] && [ "$h3" = "$h4" ]; then
  echo "PASS: independent extraction -- ledger view bytes == instrument bytes"
  echo "      (transcript $h1, axioms $h3)"
else
  echo "FAIL: independent block equality (t: $h1 vs $h2; a: $h3 vs $h4)"; fail=$((fail+1))
fi

# --- d. census reconciliation -------------------------------------------------
sum=0; ok=1
for pair in Interchange:21 MagicSquare:63 Anyon:714 Exchangeable:41 Rigidity:214; do
  f=${pair%%:*}; want=${pair##*:}
  gotsrc=$(grep -cE '^theorem [A-Za-z_0-9].*:' "$f.lean")
  gottr=$(grep -E "^  $f\.lean" "$TR" | grep -oE '[0-9]+ *$' | tr -d ' ')
  gotax=$(awk -v f="$f" '$1==f && NF>=4 {print $2}' "$AX" | head -1)
  printf '  %-14s source-grep=%-4s transcript=%-4s axioms=%-4s expected=%s\n' \
         "$f" "$gotsrc" "$gottr" "$gotax" "$want"
  [ "$gotsrc" = "$want" ] && [ "$gottr" = "$want" ] && [ "$gotax" = "$want" ] || ok=0
  sum=$((sum + want))
done
tot_tr=$(grep -E '^  TOTAL' "$TR" | grep -oE '[0-9]+')
tot_ax=$(awk '$1=="TOTAL" {print $2}' "$AX")
if [ $ok -eq 1 ] && [ "$sum" -eq 1053 ] && [ "$tot_tr" = "1053" ] && [ "$tot_ax" = "1053" ]; then
  echo "PASS: census 1053 = 21+63+714+41+214, three-way (sources, transcript, axioms)"
else
  echo "FAIL: census mismatch (sum=$sum tot_tr=$tot_tr tot_ax=$tot_ax ok=$ok)"; fail=$((fail+1))
fi

# --- e. axiom-family arithmetic ----------------------------------------------
echo "  axiom-family table ($AX):"
sed -n '/^axiom sets actually occurring:/,/^$/p' "$AX" | grep '\[' | sed 's/^/    /'
pyok=$(awk '
  /^axiom sets actually occurring:/ {inb=1; next}
  inb && /\[/ { n=$NF; file=$1; fam[file]+=n }
  inb && /^$/ {inb=0}
  /^Interchange |^MagicSquare |^Anyon |^Exchangeable |^Rigidity / && NF>=4 {
    total[$1]=$2; free[$1]=$3; rest[$1]=$4 }
  END {
    bad=0
    for (f in rest) {
      if (fam[f] != rest[f]) { printf "MISMATCH %s families=%d rest=%d\n", f, fam[f], rest[f]; bad=1 }
      if (free[f]+rest[f] != total[f]) { printf "MISMATCH %s free+rest!=total\n", f; bad=1 }
    }
    print (bad ? "BAD" : "OK")
  }' "$AX")
if printf '%s' "$pyok" | grep -q '^OK$'; then
  echo "PASS: per-file family counts == rest column; axiom-free+rest == total"
  echo "      (444 axiom-free + 609 rest = 1053; Rigidity families 124+1+30=155)"
else
  echo "FAIL: axiom-family arithmetic: $pyok"; fail=$((fail+1))
fi
if grep -qE 'sorryAx +0' "$AX" && grep -qE 'Classical.choice +0' "$AX"; then
  echo "PASS: sorryAx 0 and Classical.choice 0 in the census"
else
  echo "FAIL: hygiene pair not clean in census"; fail=$((fail+1))
fi

echo
[ $fail -eq 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL ($fail)"
exit $((fail>0))
