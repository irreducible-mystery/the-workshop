#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  The transcription check.
#
# ADJUDICATOR DECLARATION (norm 15, this artifact's own entry):
#   WHAT THIS CHECKS: that definitions Rigidity.lean copies from Anyon.lean are
#     byte-identical to their originals, modulo a short list of DECLARED and
#     JUSTIFIED differences.
#   WHAT IT DOES NOT CHECK: the declared differences themselves.  Each one is a
#     human claim that a change is meaning-preserving, and this script only
#     verifies that the change is the one that was declared -- not that the
#     declaration is true.  Those are adjudicated by the builder's source audit.
#
# WHY IT EXISTS (round 6, and it is a class the round CREATED).
#
# Round 6 added a fifth deliverable, `Rigidity.lean`, under the standing rule
# from round 4's Q5: never trade the zero-imports property; if a split is ever
# needed, prefer the duplicated-ring-layer split that keeps every file
# import-free.  That rule is right, and it has a cost nobody named at the time:
#
#   Rigidity.lean COPIES the pentagon machinery from Anyon.lean, and -- having
#   zero imports by construction -- CANNOT state, let alone prove, that its copy
#   agrees with the original.  Its docstring says "verbatim from Anyon.lean" and
#   "same content, same convention".  Those are cross-file claims.  Nothing in
#   the crate checked them, and no theorem in either file can.
#
# If the transcription ever drifts, every theorem in Rigidity.lean remains true
# -- of a different pentagon.  That is the worst failure shape this project can
# produce: fully kernel-checked, entirely sound, and about the wrong object.
#
# The architecture decision was joint and correct.  The unadjudicated class it
# created is this one, declared here at birth rather than found next round.
#
# Usage:   sh audit/transcription.sh      (run from workshop/lean/)
# Exit:    0 if every shared definition matches or matches its declared
#          exception; 1 otherwise.
# ---------------------------------------------------------------------------
set -u

SRC=Anyon.lean
DST=Rigidity.lean

# Definitions Rigidity.lean claims to copy verbatim.
SHARED="fuse memA isOne sumOver Fs pentagonValid"

# DECLARED EXCEPTIONS -- copied with a stated, justified change.  Each is listed
# with the reason, and the script reports them rather than silently passing.
#   Fg           : generalized from `KK` to an arbitrary ring `R`, because this
#                  file works over Zp and Ep, never over KK.  Same four cases.
#   pentResid    : Anyon.lean has `pentagonCheck` (LHS `beq` RHS); this file
#                  needs the DIFFERENCE as a ring element to square it, so it
#                  has `pentResid` = LHS + neg RHS.  The two LHS/RHS expressions
#                  must still be verbatim identical -- checked below.
#   pentOK       : the Boolean form, phrased through `DecidableEq Zp` on the
#                  residual because this file's `Rng` carries `neg` and not
#                  `beq`.  NOT CHECKED HERE: that `pentOK` and `pentagonCheck`
#                  agree.  That is a cross-file semantic claim and is exactly
#                  what this script's boundary excludes.
EXCEPTIONS="Fg pentResid pentOK"

echo "=============================================================="
echo " TRANSCRIPTION CHECK -- $DST vs $SRC"
echo "=============================================================="
echo " checks:      copied definitions are byte-identical"
echo " DOES NOT:    verify that the declared exceptions preserve meaning"
echo "=============================================================="

extract() {
  awk -v n="$2" '
    $0 ~ ("^def " n " ") || $0 ~ ("^def " n "$") { f = 1 }
    f { print }
    f && /^$/ { exit }
  ' "$1" | sed 's/[[:space:]]\+/ /g' | sed 's/^ //; s/ $//' | grep -v '^$'
}

fail=0
for d in $SHARED; do
  a=$(extract "$SRC" "$d")
  b=$(extract "$DST" "$d")
  if [ -z "$a" ]; then printf '  ABSENT-SRC  %-18s not found in %s\n' "$d" "$SRC"; fail=1; continue; fi
  if [ -z "$b" ]; then printf '  ABSENT-DST  %-18s not found in %s\n' "$d" "$DST"; fail=1; continue; fi
  if [ "$a" = "$b" ]; then
    printf '  identical   %s\n' "$d"
  else
    printf '  DRIFTED     %-18s copy differs from original\n' "$d"
    printf '%s\n' "$a" | sed 's/^/      src: /'
    printf '%s\n' "$b" | sed 's/^/      dst: /'
    fail=1
  fi
done

# The one structural check inside an exception that CAN be made mechanically:
# pentResid's two halves must be the same expressions pentagonCheck compares.
echo
echo "--------------------------------------------------------------"
echo " declared exceptions (reported, not silently passed)"
echo "--------------------------------------------------------------"
for d in $EXCEPTIONS; do printf '  declared    %s\n' "$d"; done

echo
# Pull the two compared expressions out of each definition separately.  The
# LHS is the `sumOver ... (fuse b c)` clause; the RHS is the product of two
# `Fs` calls.  Isolating them is what lets the DECLARED `K.neg` wrapper on the
# RHS pass while a change to either expression fails.
half() {  # $1 file, $2 defname, $3 = lhs|rhs
  body=$(awk -v n="$2" '$0 ~ ("^def " n " ") {f=1} f{print} f&&/^$/{exit}' "$1" \
         | sed 's/[[:space:]]\+/ /g' | tr -d '\n')
  case "$3" in
    lhs) printf '%s' "$body" | sed 's/.*\(sumOver K (fun u =>.*(fuse b c)\).*/\1/' ;;
    rhs) printf '%s' "$body" | sed 's/.*\(K\.mul (Fs K F x c dd t y w) (Fs K F a b w t x v)\).*/\1/' ;;
  esac
}

for side in lhs rhs; do
  s=$(half "$SRC" pentagonCheck "$side")
  d=$(half "$DST" pentResid     "$side")
  if [ -n "$s" ] && [ "$s" = "$d" ]; then
    printf '  identical   pentResid %s == pentagonCheck %s\n' "$side" "$side"
  else
    printf '  DRIFTED     pentResid %s differs from pentagonCheck %s\n' "$side" "$side"
    echo "      src: $s"
    echo "      dst: $d"
    fail=1
  fi
done

# --- Verlinde.lean: the SIXTH file also copies rings (round 7) ---------------
# Verlinde.lean transcribes Zp AND Z5 from Anyon.lean for the modular-data
# re-derivation.  Same class-10 risk: a drifted `mul` and every fusion identity
# is true of a different ring.  The ring cores are namespaced (`def mul` inside
# `namespace Zp` / `namespace Z5`), so instead of the name-based extract we
# compare the exact one-line formulas, which are unique in each file.
if [ -f Verlinde.lean ]; then
  echo
  echo "--------------------------------------------------------------"
  echo " Verlinde.lean ring cores vs Anyon.lean"
  echo "--------------------------------------------------------------"
  # Zp.mul: the (ac+bd, ad+bc+bd) line
  zp_a=$(grep -F 'u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n' "$SRC" | head -1 | tr -s ' ')
  zp_v=$(grep -F 'u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n' Verlinde.lean | head -1 | tr -s ' ')
  if [ -n "$zp_a" ] && [ "$zp_a" = "$zp_v" ]; then
    echo "  identical   Zp.mul"
  else
    echo "  DRIFTED     Zp.mul (or absent)"; fail=1
  fi
  # Z5.mul: the reduced-tuple output line
  z5_a=$(grep -F 'c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4' "$SRC" | head -1 | tr -s ' ')
  z5_v=$(grep -F 'c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4' Verlinde.lean | head -1 | tr -s ' ')
  if [ -n "$z5_a" ] && [ "$z5_a" = "$z5_v" ]; then
    echo "  identical   Z5.mul"
  else
    echo "  DRIFTED     Z5.mul (or absent)"; fail=1
  fi
  # fuse: the fusion rule itself
  fu_a=$(extract "$SRC" fuse); fu_v=$(extract Verlinde.lean fuse)
  if [ -n "$fu_a" ] && [ "$fu_a" = "$fu_v" ]; then
    echo "  identical   fuse"
  else
    echo "  DRIFTED     fuse (or absent)"; fail=1
  fi
  echo "  DECLARED    Zp.conj (NEW in Verlinde -- the source has only Z5/KK conj;"
  echo "              labeled NEW at its definition, not a copy)"
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: every copied definition matches its original.  PASS."
  echo "        (the declared exceptions above are NOT verified for meaning)"
else
  echo "RESULT: FAIL -- a copied definition has drifted from its original."
  echo "        The copying file's theorems would be about a different object."
fi
exit $fail
