#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  Build the outgoing crate, and PROVE what is in it.
#
# Why this exists (round 4, correction D5).  Round 3's ledger said the two
# audit instruments "ship with the round".  They did not: exactly nine files
# reached the builder -- the flat contents of lean/ -- and the `audit/` and
# `archive/` SUBDIRECTORIES were silently dropped in transit.  The ledger was
# true about the repo and false about the crate, and nothing caught it because
# nothing was checking the crate.
#
# The house has a norm for exactly this and it was not being applied to the
# packaging: a check that cannot fail is not a check.  "Remember to drag the
# folder" cannot fail-loudly.  This can: it builds the archive, re-reads it,
# and refuses to pass if a required file is missing from the ARCHIVE ITSELF
# rather than from the working tree.
#
# Usage:   sh audit/ship.sh <round>   (run from workshop/lean/)
# Output:  ../workshop-lean-round<N>.zip  + a manifest printed to stdout
# ---------------------------------------------------------------------------
set -u

# NO DEFAULT ROUND.  This used to be "${1:-4}", so a bare run would silently
# rebuild -- and overwrite -- an already-ferried round-4 crate.  The builder
# caught it in the round-6 audit.  There is no safe guess for which round you
# are shipping, so the argument is required.
if [ "$#" -lt 1 ]; then
  echo "usage: sh audit/ship.sh <round-number>"
  echo "  (no default: a bare run would overwrite an already-shipped crate)"
  exit 2
fi
ROUND="$1"
OUT="../workshop-lean-round${ROUND}.zip"
WORK_EXTRAS=$(mktemp)
trap 'rm -f "$WORK_EXTRAS"' EXIT

REQUIRED="
Anyon.lean
Exchangeable.lean
Interchange.lean
MagicSquare.lean
Rigidity.lean
Verlinde.lean
lean-toolchain
PROOFS.md
HANDOFF.md
audit/axioms.sh
audit/transcript.sh
audit/ship.sh
archive/PROOFS-round1.md
archive/PROOFS-round2.md
archive/PROOFS-round3.md
audit/transcript-round4.txt
audit/axioms-round4.txt
audit/transcript-round5.txt
audit/axioms-round5.txt
audit/views.sh
archive/PROOFS-round4.md
archive/PROOFS-round5.md
audit/pointers.sh
audit/transcription.sh
audit/quoted-names.txt
audit/numerals.sh
audit/transcript-round6.txt
audit/axioms-round6.txt
audit/transcript-round7.txt
audit/axioms-round7.txt
audit/transcript-round8.txt
audit/axioms-round8.txt
audit/sources.txt
REGISTER.md
ROUND2.md
ROUND3.md
ROUND4.md
ROUND5.md
ROUND6.md
ROUND7.md
ROUND8.md
archive/PROOFS-round6.md
archive/PROOFS-round7.md
"

echo "=============================================================="
echo " OUTGOING CRATE -- round ${ROUND}"
echo "=============================================================="

# 1. present in the working tree?
missing=0
for f in $REQUIRED; do
  [ -f "$f" ] || { echo "  !! MISSING FROM TREE: $f"; missing=1; }
done
[ "$missing" -ne 0 ] && { echo "RESULT: FAIL -- fix the tree first."; exit 1; }

# 2. build, preserving directory structure.
#    This box has `unzip` but no `zip`, so creation goes through .NET ZipFile
#    (see below for why NOT Compress-Archive) and verification comes back
#    through `unzip` -- the archive is written by one tool and read by a
#    different one, so a bug in either shows up as a disagreement rather than
#    as a matching pair of mistakes.
rm -f "$OUT"
# Stage to a temp copy first: this script is itself part of the payload, and a
# running `sh` holds it open, which the archiver refuses to read.
STAGE=$(mktemp -d)/lean
mkdir -p "$STAGE"
tar -cf - --exclude='*.zip' --exclude='*.olean' . | (cd "$STAGE" && tar -xf -)
STAGEWIN=$(cd "$STAGE" && pwd -W)
OUTWIN=$(cd "$(dirname "$OUT")" && pwd -W)/$(basename "$OUT")

# NOT Compress-Archive.  Windows PowerShell 5.1's Compress-Archive writes
# entry names with BACKSLASH separators, which the ZIP spec (APPNOTE 4.4.17)
# forbids -- names must use '/'.  Many extractors then treat "audit\x.sh" as a
# single flat filename instead of a path, which silently collapses every
# subdirectory.  That is the most likely mechanism behind round 3's D5: the
# audit/ and archive/ trees were IN the crate and came out flat or dropped.
# So the entries are written by hand, with forward slashes, and read back with
# a different tool below.
powershell -NoProfile -NonInteractive -Command "
  \$ErrorActionPreference = 'Stop'
  Add-Type -AssemblyName System.IO.Compression.FileSystem
  Add-Type -AssemblyName System.IO.Compression
  \$root = '$STAGEWIN'
  \$zip  = [System.IO.Compression.ZipFile]::Open('$OUTWIN', 'Create')
  try {
    Get-ChildItem -Path \$root -Recurse -File -Force | ForEach-Object {
      \$rel = \$_.FullName.Substring(\$root.Length + 1).Replace('\\','/')
      [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
         \$zip, \$_.FullName, \$rel) | Out-Null
    }
  } finally { \$zip.Dispose() }
" 2>&1 | sed 's/^/  ps: /'
rm -rf "$(dirname "$STAGE")"
[ -f "$OUT" ] || { echo "  !! archive was not created"; exit 1; }

# 3. THE CHECK THAT MATTERS: re-read the archive and confirm each required
#    path is inside IT.  This is what round 3 lacked.
echo
echo "--------------------------------------------------------------"
echo " verifying the ARCHIVE (not the tree)"
echo "--------------------------------------------------------------"
listing=$(unzip -Z1 "$OUT" 2>/dev/null)
fail=0
for f in $REQUIRED; do
  if ! printf '%s\n' "$listing" | grep -qx "\./$f\|$f"; then
    printf '  MISSING  %s\n' "$f"; fail=1; continue
  fi
  # PRESENCE IS NOT ENOUGH -- check the CONTENT matches the working tree.
  # Round 4 caught this the honest way: a ledger edit landed after the archive
  # was built, and a presence-only check called the stale crate PASS.  An
  # archive that contains an old PROOFS.md is exactly as wrong as one that
  # omits it, and harder to notice from the other end.
  th=$(sha256sum "$f" | cut -c1-64)
  ah=$(unzip -p "$OUT" "$f" 2>/dev/null | sha256sum | cut -c1-64)
  if [ "$th" = "$ah" ]; then
    printf '  ok       %s\n' "$f"
  else
    printf '  STALE    %s  (tree %s… vs archive %s…)\n' \
           "$f" "$(echo "$th" | cut -c1-12)" "$(echo "$ah" | cut -c1-12)"
    fail=1
  fi
done

# ENUMERATE-OR-FORBID (round 7, builder's ferry note).  REQUIRED checks that
# every needed file is IN the archive; it structurally cannot notice an EXTRA.
# Round 6 shipped a `PROOFS.md.bak` stowaway that way.  So: every archive entry
# must be REQUIRED, or match a labeled ALLOWED pattern, or the crate is refused.
# The builder's own crate carries the letters; ours now forbids surprises.
# Round 8: the crate is ferried WHOLE in both directions, so it carries the
# builder's side too.  ALLOWED covers, with a reason each:
#   \.py$             -- Python instruments (mine under audit/, the builder's
#                        re-verifications and gifts, and the floor's benches)
#   ^floor/           -- the builder's physics floor (benches + its README /
#                        WELD_REPORT / FINDINGS), carried for the record
#   ^audit/r[0-9].*\.sh$ -- the builder's shell re-verifications (r3-r7),
#                        pinned to their rounds, carried so each archive is whole
ALLOWED_PAT='\.py$|^floor/|^audit/r[0-9].*\.sh$'
echo
echo "--------------------------------------------------------------"
echo " enumerate-or-forbid: every entry REQUIRED or labeled-ALLOWED"
echo "--------------------------------------------------------------"
extra=0
printf '%s\n' "$listing" | sed 's|^\./||' | grep -v '/$' | while read -r e; do
  [ -n "$e" ] || continue
  # is it REQUIRED?
  if printf '%s\n' $REQUIRED | grep -qxF "$e"; then continue; fi
  # is it labeled-ALLOWED?
  if printf '%s' "$e" | grep -qE "$ALLOWED_PAT"; then continue; fi
  printf '  STOWAWAY %s  (not REQUIRED, not ALLOWED)\n' "$e"
done > "$WORK_EXTRAS"
if [ -s "$WORK_EXTRAS" ]; then cat "$WORK_EXTRAS"; extra=1; else echo "  (none)"; fi

echo
echo "--------------------------------------------------------------"
echo " full manifest ($(printf '%s\n' "$listing" | grep -c . ) entries)"
echo "--------------------------------------------------------------"
printf '%s\n' "$listing" | sed 's/^/  /'

echo
if [ "$fail" -eq 0 ] && [ "$extra" -eq 0 ]; then
  echo "RESULT: PASS -- every required file is inside $OUT, and no stowaways."
  echo "sha256($OUT) = $(sha256sum "$OUT" | cut -c1-64)"
  echo
  echo "Kelly: ferry THIS FILE, not the folder."
elif [ "$extra" -ne 0 ]; then
  echo "RESULT: FAIL -- the archive carries a stowaway (see above).  Either add"
  echo "        it to REQUIRED, extend ALLOWED_PAT with a reason, or remove it."
else
  echo "RESULT: FAIL -- the archive is short.  Do not ferry it."
fi
[ "$extra" -ne 0 ] && fail=1
exit $fail
