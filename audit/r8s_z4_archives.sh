#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z4_archives.sh -- ROUND-8 TERMINAL AUDIT, seat Z, check R4.
#
# ARCHIVES COMPLETE, byte-verified:
#   (a) archive/PROOFS-round1..7.md -- all seven present in the crate and
#       byte-identical to this side's archive copies;
#   (b) the letters ROUND2..8.md -- re-confirmed byte-identical
#       (verified at the ferry; re-run here so the terminal record is
#       self-contained);
#   (c) the final states of HANDOFF.md and REGISTER.md -- crate vs tree;
#   (d) PROOFS.md, the terminal ledger itself -- crate vs tree.
#
# Standalone: sh + cmp.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
set -u
C=/tmp/r8crate
L=/home/claude/workshop/lean
fail=0

cmp_one() {  # $1 = relative path
  if [ ! -f "$C/$1" ]; then printf '  ABSENT-CRATE %s\n' "$1"; fail=1
  elif [ ! -f "$L/$1" ]; then printf '  ABSENT-TREE  %s\n' "$1"; fail=1
  elif cmp -s "$C/$1" "$L/$1"; then printf '  identical    %s\n' "$1"
  else printf '  DIVERGED     %s\n' "$1"; fail=1
  fi
}

echo "=============================================================="
echo " R4 -- ARCHIVES COMPLETE: ledgers, letters, final states"
echo "=============================================================="

echo "--- (a) the seven archived ledgers ---"
i=1
while [ "$i" -le 7 ]; do cmp_one "archive/PROOFS-round$i.md"; i=$((i + 1)); done

echo
echo "--- (b) the letters, re-confirmed ---"
i=2
while [ "$i" -le 8 ]; do cmp_one "ROUND$i.md"; i=$((i + 1)); done

echo
echo "--- (c) final states ---"
cmp_one "HANDOFF.md"
cmp_one "REGISTER.md"

echo
echo "--- (d) the terminal ledger ---"
cmp_one "PROOFS.md"

# note (not a failure): the tree archive also holds src-round2..7 source
# snapshots; ship.sh REQUIRED never carried them, so their absence from the
# crate is the manifest working as designed.
echo
echo "  note: tree-side archive/src-round* snapshots are not REQUIRED cargo"
echo "        and are correctly absent from the crate (enumerate-or-forbid)."

echo
if [ "$fail" = 0 ]; then
  echo "RESULT: PROOFS-round1..7 aboard and byte-identical; letters ROUND2-8"
  echo "        re-confirmed; HANDOFF, REGISTER, and PROOFS final states match"
  echo "        the tree exactly.  PASS."
  exit 0
else
  echo "RESULT: FAIL -- divergence above."
  exit 1
fi
