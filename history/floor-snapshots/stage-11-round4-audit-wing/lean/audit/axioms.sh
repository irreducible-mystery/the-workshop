#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> LEAN.  Axiom census.
#
# Runs `#print axioms` on EVERY theorem in the four deliverables and tallies
# the result.  This is the instrument behind PROOFS.md's axiom table; round 3
# added it to the repo precisely because round 2's table was disputed and the
# dispute could only be settled by re-running the instrument.
#
# METHOD.  Each source file is copied, and one `#print axioms <fully-qualified
# name>` line is appended per theorem.  The qualified name is rebuilt from the
# `namespace`/`end` stack, so theorems inside inner namespaces (Z5, KK,
# Interchanging, PreInterchanging) are named correctly.  Names containing a
# prime (`rt'_root_quadratic`) are matched too -- an earlier version of this
# script silently dropped them and undercounted Anyon by one.
#
# READ THIS BEFORE INTERPRETING THE OUTPUT.  `#print axioms T` reports the
# axioms of the whole transitive dependency closure of T -- which includes the
# DEFINITIONS APPEARING IN T's STATEMENT, not merely the proof term.  So a
# theorem proved by a literal `rfl` can and does report `propext` when a
# definition it mentions depends on `propext`.  In MagicSquare.lean the source
# is `Fin`-indexed definitions (`rowPar`, `inCtx`, and everything downstream);
# `mkY`, `par` and `yEnumSize` are clean, which is why exactly 14 theorems come
# out axiom-free.  See PROOFS.md, correction C1'.
#
# Usage:   sh audit/axioms.sh            (run from workshop/lean/)
# ---------------------------------------------------------------------------
set -u

export PATH="$HOME/.elan/bin:$PATH"

WORK=/tmp/wsl_axioms_$$
mkdir -p "$WORK"

echo "=============================================================="
echo " AXIOM CENSUS -- #print axioms on every theorem"
echo " toolchain: $(cat lean-toolchain)   $(lean --version)"
echo "--------------------------------------------------------------"
echo " WHAT THIS COLUMN MEANS (round 4, at the builder's request):"
echo " the axioms of the #print axioms closure, STATEMENT INCLUDED --"
echo " a toolchain-relative OVER-APPROXIMATION of logical dependence."
echo " A theorem may be derivable axiom-free and still report propext"
echo " here, because a definition named in its statement carries one."
echo " This census measures the first thing, not the second."
echo "=============================================================="

for f in Interchange MagicSquare Anyon Exchangeable; do
  cp "$f.lean" "$WORK/$f.lean"
  echo "" >> "$WORK/$f.lean"
  awk '
    /^namespace /  { st[++n] = $2; next }
    /^end /        { if (n > 0 && $2 == st[n]) n--; next }
    # The /:/ guard matters: a doc-comment line may legitimately begin with the
    # word "theorem" at column 0 -- one does, in Anyon.lean section 6.  Every
    # real declaration has a type ascription, so requiring a colon on the line
    # separates declarations from prose.  Without the guard the census emits a
    # print-axioms for a non-existent constant and reports itself INCOMPLETE.
    # (No apostrophes in this comment: the awk program is single-quoted.)
    # A `_root_.`-qualified declaration names itself absolutely and must NOT be
    # prefixed with the enclosing namespace stack.  Round 4 hit this: a lemma
    # declared as `theorem _root_.Workshop.Anyon.Z5.foo` from inside
    # `namespace KK` produced the nonexistent `Workshop.Anyon.KK._root_`, and
    # the census correctly reported itself INCOMPLETE rather than skipping it.
    # Handled here so the next one does not cost a run.
    /^theorem _root_\./ && /:/ {
        nm = $2; sub(/^_root_\./, "", nm); sub(/[^A-Za-z_0-9'"'"'.].*/, "", nm)
        print "#print axioms " nm
        next
    }
    /^theorem [A-Za-z_0-9'"'"']+/ && /:/ {
        nm = $2; sub(/[^A-Za-z_0-9'"'"'].*/, "", nm)
        p = ""; for (i = 1; i <= n; i++) p = p st[i] "."
        print "#print axioms " p nm
    }' "$f.lean" >> "$WORK/$f.lean"
  echo "===== $f ====="
  lean "$WORK/$f.lean" 2>&1
done > "$WORK/raw.txt"

# ---- tally -----------------------------------------------------------------
awk '
  /^===== /                        { file = $2; next }
  /does not depend on any axioms/  { free[file]++; tot[file]++; next }
  /depends on axioms/              {
      tot[file]++
      match($0, /\[[^]]*\]/); set = substr($0, RSTART, RLENGTH)
      kind[file "|" set]++
      next
  }
  /error/                          { err++ ; print "SCRIPT ERROR: " $0 }
  END {
      printf "\n%-16s %7s %12s %10s\n", "file", "theorems", "axiom-free", "rest"
      printf "%-16s %7s %12s %10s\n", "----", "--------", "----------", "----"
      order = "Interchange MagicSquare Anyon Exchangeable"
      n = split(order, o, " ")
      T = 0; F = 0
      for (i = 1; i <= n; i++) {
          f = o[i]
          printf "%-16s %7d %12d %10d\n", f, tot[f], free[f]+0, tot[f]-free[f]
          T += tot[f]; F += free[f]+0
      }
      printf "%-16s %7d %12d %10d\n", "TOTAL", T, F, T-F
      printf "\naxiom sets actually occurring:\n"
      sorryax = 0; choice = 0
      for (k in kind) {
          split(k, a, "|"); printf "  %-16s %-28s %d\n", a[1], a[2], kind[k]
          if (a[2] ~ /sorryAx/)          sorryax += kind[k]
          if (a[2] ~ /Classical.choice/) choice  += kind[k]
      }
      printf "\nTHE TWO THAT MATTER:\n"
      printf "  sorryAx           %d   (must be 0 -- this is the authoritative\n", sorryax
      printf "                        gap check; a `sorry` in any proof term\n"
      printf "                        appears here and cannot be hidden)\n"
      printf "  Classical.choice  %d   (must be 0 -- the files are constructive)\n", choice
      if (sorryax > 0 || choice > 0) printf "\n!! HYGIENE FAILURE\n"
      if (err > 0) printf "\n!! %d script errors -- the census is INCOMPLETE\n", err
  }' "$WORK/raw.txt"

echo
echo "raw output kept in: $WORK/raw.txt"
