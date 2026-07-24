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
# Usage:   sh audit/ship.sh            (run from workshop/lean/)
# Output:  ../workshop-lean-round<N>.zip  + a manifest printed to stdout
# ---------------------------------------------------------------------------
set -u

ROUND="${1:-4}"
OUT="../workshop-lean-round${ROUND}.zip"

REQUIRED="
Anyon.lean
Exchangeable.lean
Interchange.lean
MagicSquare.lean
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

echo
echo "--------------------------------------------------------------"
echo " full manifest ($(printf '%s\n' "$listing" | grep -c . ) entries)"
echo "--------------------------------------------------------------"
printf '%s\n' "$listing" | sed 's/^/  /'

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: PASS -- every required file is inside $OUT"
  echo "sha256($OUT) = $(sha256sum "$OUT" | cut -c1-64)"
  echo
  echo "Kelly: ferry THIS FILE, not the folder."
else
  echo "RESULT: FAIL -- the archive is short.  Do not ferry it."
fi
exit $fail
