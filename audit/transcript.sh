#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  Compile transcript + .olean hashes.
#
# Answers the builder's Q4: "make .olean hashes + full compile transcript
# routine each round."  The builder's auditors cannot reach a Lean toolchain,
# so the kernel reading is single-sided.  This script is the receipt: it
# records the toolchain identity, compiles each deliverable from scratch, and
# hashes the resulting .olean so that a later run on another machine can be
# compared byte for byte.
#
# PASS CONDITION, per house norm: exit 0 AND zero bytes of output for every
# file.  A warning is a failure.
#
# Usage:   sh audit/transcript.sh            (run from workshop/lean/)
# ---------------------------------------------------------------------------
set -u

export PATH="$HOME/.elan/bin:$PATH"

# The six deliverables, from the single shared manifest (round 8: FILES= folded
# into one place so a source list never drifts between instruments).
FILES=$(tr '\n' ' ' < audit/sources.txt)
OUT=/tmp/wsl_transcript_$$
mkdir -p "$OUT"

echo "=============================================================="
echo " THE WORKSHOP -> LEAN : COMPILE TRANSCRIPT"
echo "=============================================================="
echo "date        : $(date -u '+%Y-%m-%dT%H:%M:%SZ') (UTC)"
echo "host os     : $(uname -s -r -m 2>/dev/null || echo unknown)"
echo "toolchain   : $(cat lean-toolchain)"
echo "lean        : $(lean --version)"
echo
echo "--------------------------------------------------------------"
echo " SOURCES MEASURED (E5(ii): every view names what it viewed)"
echo "--------------------------------------------------------------"
for f in $FILES; do
  printf '   %-20s %s\n' "$f" "$(sha256sum "$f" | cut -c1-64)"
done
printf '   %-20s %s\n' "lean-toolchain" "$(sha256sum lean-toolchain | cut -c1-64)"
echo
echo "--------------------------------------------------------------"
echo " per-file: exit code, wall time, output bytes, .olean sha256"
echo "--------------------------------------------------------------"

fail=0
for f in $FILES; do
  base=$(basename "$f" .lean)
  s=$(date +%s%N)
  lean -o "$OUT/$base.olean" "$f" > "$OUT/$base.log" 2>&1
  rc=$?
  e=$(date +%s%N)
  ms=$(( (e - s) / 1000000 ))
  nb=$(wc -c < "$OUT/$base.log" | tr -d ' ')
  # E5(iii): exit 0 with no .olean is not a pass.  The old code printed
  # "(no olean produced)" in the hash column and let the run succeed -- a
  # transcript that certifies a compile which produced no kernel output.
  noolean=0
  if [ -f "$OUT/$base.olean" ]; then
    h=$(sha256sum "$OUT/$base.olean" | cut -c1-64)
    osz=$(wc -c < "$OUT/$base.olean" | tr -d ' ')
  else
    h="(NO OLEAN PRODUCED)"; osz=0
    [ "$rc" -eq 0 ] && noolean=1
  fi
  printf '%-18s exit=%d  %7d ms  stdout+stderr=%s bytes  olean=%s bytes\n' \
         "$f" "$rc" "$ms" "$nb" "$osz"
  printf '%-18s sha256(olean) = %s\n\n' "" "$h"
  if [ "$rc" -ne 0 ] || [ "$nb" -ne 0 ]; then
    fail=1
    echo "  !! NOT SILENT -- output follows:"
    sed 's/^/  | /' "$OUT/$base.log"
    echo
  fi
  if [ "$noolean" -eq 1 ]; then
    fail=1
    echo "  !! exit 0 but NO .olean was produced -- nothing was kernel-checked."
    echo
  fi
done

echo "--------------------------------------------------------------"
echo " hygiene sweep"
echo "--------------------------------------------------------------"
# These are TEXTUAL counts and include doc-comment prose.  The deliverables all
# say things like "no `sorry`, no `native_decide`" in their headers, so a
# nonzero count here is NOT by itself a failure -- the lines are printed so a
# reader can see for themselves which are code and which are prose.
#
# The AUTHORITATIVE check for an unproved gap is not grep at all: it is whether
# `sorryAx` appears in any `#print axioms` report.  Run `sh audit/axioms.sh`
# for that; a `sorry` anywhere in a proof term shows up there and cannot be
# hidden by a comment.
for pat in 'sorry' 'native_decide' 'maxHeartbeats' 'maxRecDepth' 'partial def'; do
  n=$(grep -cE "$pat" $FILES 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')
  printf '  %-16s %s textual occurrence(s)\n' "$pat" "$n"
  if [ "$n" -ne 0 ]; then grep -nE "$pat" $FILES | sed 's/^/      /'; fi
done
# These two must be exactly 0 and grep IS authoritative for them.
for pat in '^axiom ' '^import '; do
  n=$(grep -cE "$pat" $FILES 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')
  printf '  %-16s %s  (must be 0)\n' "$pat" "$n"
  [ "$n" -ne 0 ] && fail=1
done

echo
echo "--------------------------------------------------------------"
echo " theorem counts"
echo "--------------------------------------------------------------"
tot=0
for f in $FILES; do
  # `&& /:/` guard, same reason as in audit/axioms.sh: a doc-comment line can
  # begin with "theorem" at column 0, and a bare grep counts it as a theorem.
  n=$(awk "/^theorem [A-Za-z_0-9']+/ && /:/ {c++} END{print c+0}" "$f")
  printf '  %-20s %3d\n' "$f" "$n"
  tot=$(( tot + n ))
done
printf '  %-20s %3d\n' "TOTAL" "$tot"

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: all files compiled silent (exit 0, zero bytes).  PASS."
else
  echo "RESULT: at least one file was not silent.  FAIL."
fi
echo "artifacts kept in: $OUT"
exit $fail
