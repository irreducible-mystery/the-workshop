#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  The pointer resolver.
#
# ADJUDICATOR DECLARATION (norm 15, this artifact's own entry):
#   WHAT THIS CHECKS: that every backticked identifier and every "see X" in the
#     ledger, HANDOFF and REGISTER names something that exists -- a Lean
#     declaration in one of the four sources, a file in the crate, or a VIEW
#     block in PROOFS.md.
#   WHAT IT DOES NOT CHECK: whether the pointer points at the RIGHT thing.
#     `see hexagon_exactly_two` resolves whether or not that theorem says what
#     the sentence claims. Binding is adjudicated by the builder's source audit
#     and by the round-over-round prediction loop, not here.
#
# WHY IT EXISTS (round 6, findings F1 + F4 + F5).
#
# Round 5 moved counts and hashes into instrument-rendered VIEW blocks, which
# closed that register. The defects then moved exactly one layer out, as
# predicted, into the prose that POINTS at things:
#
#   F1  `exactly_two_of_domain` -- a named theorem row in a ledger table and a
#       citation in HANDOFF, for a theorem that never existed in any source.
#       A scratch-file development name that never landed. TABLES ARE INVENTORY
#       TOO, and the grep pledge of round 4 covered prose, not tables.
#   F5  an instrument comment citing "correction C1'" -- which now lives only
#       in archive/.
#
# A phantom name is the cheapest possible defect to catch mechanically and the
# most expensive to catch by reading, because it reads exactly like a real one.
#
# Usage:   sh audit/pointers.sh          (run from workshop/lean/)
# Exit:    0 if every pointer resolves, 1 otherwise.
# ---------------------------------------------------------------------------
set -u

# The six deliverables, from the single shared manifest (round 8: FILES= folded).
SOURCES=$(tr '\n' ' ' < audit/sources.txt)
DOCS="PROOFS.md HANDOFF.md REGISTER.md README.md VERIFY.md"
WORK=/tmp/wsl_pointers_$$
mkdir -p "$WORK"

echo "=============================================================="
echo " POINTER RESOLVER -- does every name in the prose exist?"
echo "=============================================================="
echo " checks:      identifier exists as a declaration / file / view"
echo " DOES NOT:    check the pointer points at the right thing"
echo "=============================================================="

# --- the universe of real names --------------------------------------------
# every declaration in the four sources, unqualified and qualified
for f in $SOURCES; do
  awk '
    /^namespace /  { st[++n] = $2; next }
    /^end /        { if (n > 0 && $2 == st[n]) n--; next }
    /^(theorem|def|abbrev|structure|inductive) [A-Za-z_0-9]/ {
        nm = $2; sub(/[^A-Za-z_0-9'"'"'].*/, "", nm)
        print nm
        p = ""; for (i = 1; i <= n; i++) p = p st[i] "."
        print p nm
        # remember the current structure so its FIELDS become names too
        if ($1 == "structure") { cur = nm } else { cur = "" }
        next
    }
    # STRUCTURE FIELDS.  Prose legitimately writes `Rng.neg`, `Rng.mul` etc.,
    # and a field is not a top-level declaration -- an earlier version of this
    # script flagged them as phantoms, which is the false-positive class this
    # instrument must not have.  Two-space-indented `name : type` inside a
    # structure block is a field.
    cur != "" && /^  [a-z][A-Za-z_0-9]* +:/ {
        fld = $1
        print cur "." fld
        p = ""; for (i = 1; i <= n; i++) p = p st[i] "."
        print p cur "." fld
    }
    /^$/ { cur = "" }' "$f"
done | sort -u > "$WORK/decls.txt"

# every file in the crate -- both its path and its bare basename, since prose
# says `ship.sh` where the tree says `audit/ship.sh`
find . -type f | sed 's|^\./||' | sort -u > "$WORK/files.txt"
find . -type f -exec basename {} \; | sort -u >> "$WORK/files.txt"

# KNOWN EXTERNALS: Lean core names the prose legitimately cites but which are
# not our declarations, and names quoted precisely BECAUSE they are wrong (the
# round-2 misnomers HANDOFF records as corrections).  This list is the
# instrument's own honest boundary: everything on it is unchecked by design,
# so it is kept short and each entry is justified.
cat > "$WORK/externals.txt" <<'EXT'
cmd.exe
Classical.choice
Quot.sound
Nat.le_refl
Nat.succ_ne_zero
Nat.zero_lt_succ
Nat.strongRecOn
Nat.noConfusion
Nat.mod_lt
Fin.instOfNat
Fin.ofNat
OfNat.ofNat
NeZero.mk
Int.mul_emod
decide_eq_true
of_decide_eq_true
eq_of_beq
native_decide
lean_code
workshop.zip
EXT

# NAMES THE PROSE MENTIONS BUT DOES NOT USE.  Superseded names quoted as
# history, phantoms quoted inside the corrections that report them, and
# artifacts living in the BUILDER's crate rather than this one.
#
# These live in `audit/quoted-names.txt`, one per line with a required reason,
# rather than buried in this script -- so the exemptions are reviewable in the
# crate instead of hidden in an instrument.  A ledger that *reports* a phantom
# will always trip a phantom detector; the honest fix is a visible, reasoned
# list, not a silent regex.
if [ -f audit/quoted-names.txt ]; then
  sed 's/#.*//' audit/quoted-names.txt | tr -d ' \t' | grep -v '^$' \
    > "$WORK/quoted.txt"
else
  : > "$WORK/quoted.txt"
fi

grep -oE '<!-- VIEW:[A-Za-z_0-9]+' PROOFS.md 2>/dev/null \
  | sed 's/<!-- VIEW://' | sort -u > "$WORK/views.txt"

cat "$WORK/decls.txt" "$WORK/files.txt" "$WORK/views.txt" \
    "$WORK/externals.txt" "$WORK/quoted.txt" | sort -u > "$WORK/universe.txt"
echo " universe: $(wc -l < "$WORK/decls.txt") declarations, \
$(wc -l < "$WORK/files.txt") files, $(wc -l < "$WORK/views.txt") views"
echo

# --- candidate pointers in the prose ---------------------------------------
# A backticked token that looks like a Lean identifier: contains an underscore
# or a dot, is not obviously prose, not a shell flag, not a file glob.  The
# heuristic is deliberately narrow: FALSE NEGATIVES ARE ACCEPTABLE HERE (a
# missed pointer is caught by the audit loop), FALSE POSITIVES ARE NOT (they
# would train the reader to ignore this instrument, which is worse than not
# having it).
fail=0
total=0
for d in $DOCS; do
  [ -f "$d" ] || continue
  grep -oE '`[A-Za-z][A-Za-z_0-9.]*`' "$d" \
    | tr -d '`' \
    | grep -E '_|\.' \
    | grep -vE '^(audit|archive)\.' \
    | sort -u > "$WORK/cand_$d.txt" 2>/dev/null || true
  n=0; bad=0
  while IFS= read -r p; do
    [ -n "$p" ] || continue
    n=$((n + 1))
    # strip a trailing dot-suffix used for conjunct projection (foo.2.1)
    base=$(printf '%s' "$p" | sed 's/\.[0-9][0-9.]*$//')
    if grep -qxF "$p" "$WORK/universe.txt" || grep -qxF "$base" "$WORK/universe.txt"; then
      :
    else
      # last chance: a suffix match on a qualified name
      if grep -qE "(^|\.)$(printf '%s' "$base" | sed 's/[.[\*^$]/\\&/g')$" "$WORK/universe.txt"; then
        :
      else
        printf '  UNRESOLVED  %-46s in %s\n' "$p" "$d"
        bad=$((bad + 1)); fail=1
      fi
    fi
  done < "$WORK/cand_$d.txt"
  total=$((total + n))
  printf '  %-14s %4d pointers checked, %d unresolved\n' "$d" "$n" "$bad"
done

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: all $total pointers resolve.  PASS."
  echo "        (resolution only -- binding is the audit loop's job)"
else
  echo "RESULT: FAIL -- at least one name in the prose does not exist."
  echo "        Either the name is wrong, or the thing was never written."
fi
rm -rf "$WORK"
exit $fail
