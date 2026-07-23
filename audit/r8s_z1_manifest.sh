#!/bin/sh
# ---------------------------------------------------------------------------
# r8s_z1_manifest.sh -- ROUND-8 TERMINAL AUDIT, seat Z (full-crate
# reconciliation), check R1.
#
#   (a) enumerate every entry of the extracted round-8 crate (/tmp/r8crate)
#       and CLASSIFY it; the claimed partition is
#         floor 33 + builder audit 46 + their audit 24 + archive 7
#         + lean 6 + docs 11  =  127
#       (builder audit = audit/r[0-9]*, the r3-r7 instruments;
#        their audit   = the 7 shell gates + 12 .txt outputs/manifests
#                        + the 5 carried verify/audit_c1 .py)
#       -- verify the sums AND the membership of every class by name.
#   (b) reconcile against the crate's own audit/ship.sh: every REQUIRED
#       path present, every entry REQUIRED or labeled-ALLOWED, zero
#       unlisted, and REQUIRED + ALLOWED = 127 exactly.
#
# Standalone: sh + coreutils only.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
set -u
C=/tmp/r8crate
W=/tmp/r8s_z1_$$
mkdir -p "$W"
trap 'rm -rf "$W"' EXIT
fail=0

echo "=============================================================="
echo " R1 -- CRATE MANIFEST: 127 entries, classified and reconciled"
echo "=============================================================="
[ -d "$C" ] || { echo "FAIL: no crate at $C"; exit 1; }

( cd "$C" && find . -type f | sed 's|^\./||' | sort ) > "$W/entries.txt"
TOTAL=$(wc -l < "$W/entries.txt")
echo " total entries        : $TOTAL   (claim: 127)"
[ "$TOTAL" = "127" ] || { echo "  FAIL: total != 127"; fail=1; }

# --- (a) classification ------------------------------------------------------
grep '^floor/'      "$W/entries.txt" > "$W/floor.txt"   || true
grep '^archive/'    "$W/entries.txt" > "$W/archive.txt" || true
grep '^audit/r[0-9]' "$W/entries.txt" > "$W/builder.txt" || true
grep '^audit/' "$W/entries.txt" | grep -v '^audit/r[0-9]' > "$W/theirs.txt" || true
grep -v '/' "$W/entries.txt" | grep '\.lean$' > "$W/lean.txt" || true
grep -v '/' "$W/entries.txt" | grep -v '\.lean$' > "$W/docs.txt" || true

nfloor=$(wc -l < "$W/floor.txt");  narch=$(wc -l < "$W/archive.txt")
nbld=$(wc -l < "$W/builder.txt");  nth=$(wc -l < "$W/theirs.txt")
nlean=$(wc -l < "$W/lean.txt");    ndocs=$(wc -l < "$W/docs.txt")
echo
echo " class                  found  claimed"
printf '  floor/                %4d     33\n' "$nfloor"
printf '  builder audit r[0-9]* %4d     46\n' "$nbld"
printf '  their audit (rest)    %4d     24\n' "$nth"
printf '  archive/              %4d      7\n' "$narch"
printf '  lean sources          %4d      6\n' "$nlean"
printf '  docs (top, non-lean)  %4d     11\n' "$ndocs"
sum=$((nfloor + nbld + nth + narch + nlean + ndocs))
printf '  SUM                   %4d    127\n' "$sum"
[ "$nfloor" = 33 ] && [ "$nbld" = 46 ] && [ "$nth" = 24 ] && \
[ "$narch" = 7 ] && [ "$nlean" = 6 ] && [ "$ndocs" = 11 ] && [ "$sum" = 127 ] \
  || { echo "  FAIL: partition does not match the claim"; fail=1; }

# --- membership, class by class (exact expected name sets) -------------------
sort > "$W/exp_lean.txt" <<'EOF'
Anyon.lean
Exchangeable.lean
Interchange.lean
MagicSquare.lean
Rigidity.lean
Verlinde.lean
EOF
sort > "$W/exp_docs.txt" <<'EOF'
HANDOFF.md
PROOFS.md
REGISTER.md
ROUND2.md
ROUND3.md
ROUND4.md
ROUND5.md
ROUND6.md
ROUND7.md
ROUND8.md
lean-toolchain
EOF
sort > "$W/exp_archive.txt" <<'EOF'
archive/PROOFS-round1.md
archive/PROOFS-round2.md
archive/PROOFS-round3.md
archive/PROOFS-round4.md
archive/PROOFS-round5.md
archive/PROOFS-round6.md
archive/PROOFS-round7.md
EOF
sort > "$W/exp_theirs.txt" <<'EOF'
audit/audit_c1_check.py
audit/axioms-round4.txt
audit/axioms-round5.txt
audit/axioms-round6.txt
audit/axioms-round7.txt
audit/axioms-round8.txt
audit/axioms.sh
audit/numerals.sh
audit/pointers.sh
audit/quoted-names.txt
audit/ship.sh
audit/sources.txt
audit/transcript-round4.txt
audit/transcript-round5.txt
audit/transcript-round6.txt
audit/transcript-round7.txt
audit/transcript-round8.txt
audit/transcript.sh
audit/transcription.sh
audit/verify_anyon.py
audit/verify_anyon_r2.py
audit/verify_c3.py
audit/verify_exchangeable_r2.py
audit/views.sh
EOF
echo
for cls in lean docs archive theirs; do
  if diff -q "$W/exp_$cls.txt" "$W/$cls.txt" > /dev/null 2>&1; then
    echo "  membership ok        : $cls (matches expected name set exactly)"
  else
    echo "  MEMBERSHIP FAIL      : $cls"; diff "$W/exp_$cls.txt" "$W/$cls.txt" | sed 's/^/      /'
    fail=1
  fi
done
# floor: 30 .py + FINDINGS.md + README.md + WELD_REPORT.txt, nothing else
npy=$(grep -c '\.py$' "$W/floor.txt" || true)
nmd=$(grep -cE '^floor/(FINDINGS\.md|README\.md|WELD_REPORT\.txt)$' "$W/floor.txt" || true)
if [ "$npy" = 30 ] && [ "$nmd" = 3 ] && [ "$((npy + nmd))" = "$nfloor" ]; then
  echo "  membership ok        : floor (30 .py + README/WELD_REPORT/FINDINGS)"
else
  echo "  MEMBERSHIP FAIL      : floor ($npy py + $nmd docs of $nfloor)"; fail=1
fi
# builder: every audit/r[0-9]* is .py or .sh, split 29 + 17
nbpy=$(grep -c '\.py$' "$W/builder.txt" || true)
nbsh=$(grep -c '\.sh$' "$W/builder.txt" || true)
if [ "$nbpy" = 29 ] && [ "$nbsh" = 17 ] && [ "$((nbpy + nbsh))" = "$nbld" ]; then
  echo "  membership ok        : builder audit (29 .py + 17 .sh, r3-r7 rounds)"
else
  echo "  MEMBERSHIP FAIL      : builder audit ($nbpy py + $nbsh sh of $nbld)"; fail=1
fi

# --- (b) ship.sh REQUIRED / ALLOWED reconciliation ---------------------------
echo
echo "--------------------------------------------------------------"
echo " ship.sh reconciliation (the crate's own manifest law)"
echo "--------------------------------------------------------------"
awk '/^REQUIRED="/,/^"/' "$C/audit/ship.sh" | sed '1d;$d' | grep -v '^$' | sort > "$W/req.txt"
NREQ=$(wc -l < "$W/req.txt")
echo " REQUIRED parsed      : $NREQ paths (from the crate's own ship.sh)"
[ "$NREQ" = 43 ] || { echo "  note: expected 43 REQUIRED"; fail=1; }
missing=0
while IFS= read -r f; do
  grep -qxF "$f" "$W/entries.txt" || { echo "  MISSING REQUIRED: $f"; missing=1; }
done < "$W/req.txt"
[ "$missing" = 0 ] && echo " every REQUIRED path  : present in the crate"
[ "$missing" = 0 ] || fail=1
ALLOWED_PAT='\.py$|^floor/|^audit/r[0-9].*\.sh$'
unlisted=0; nallowed=0
while IFS= read -r e; do
  if grep -qxF "$e" "$W/req.txt"; then continue; fi
  if printf '%s' "$e" | grep -qE "$ALLOWED_PAT"; then nallowed=$((nallowed+1)); continue; fi
  echo "  UNLISTED (stowaway): $e"; unlisted=1
done < "$W/entries.txt"
echo " labeled-ALLOWED      : $nallowed entries (claim: 84; 43+84=127)"
[ "$nallowed" = 84 ] || { echo "  FAIL: ALLOWED != 84"; fail=1; }
if [ "$unlisted" = 0 ]; then
  echo " unlisted entries     : ZERO -- every entry REQUIRED or labeled-ALLOWED"
else
  echo "  FAIL: stowaway(s) above"; fail=1
fi

echo
if [ "$fail" = 0 ]; then
  echo "RESULT: 127 entries enumerated; partition 33+46+24+7+6+11 verified by"
  echo "        name; all 43 REQUIRED aboard; 84 labeled-ALLOWED; zero unlisted."
  echo "        PASS."
else
  echo "RESULT: FAIL -- see lines above."
fi
exit $fail
