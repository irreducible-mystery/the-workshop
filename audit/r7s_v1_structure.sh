#!/bin/sh
# ---------------------------------------------------------------------------
# r7s_v1_structure.sh -- ROUND-7 SEAT: Verlinde.lean structure + hygiene audit
# (checks V1 and V7 of the seat charge).
#
# WHAT THIS CHECKS
#   S1  zero imports / zero axiom declarations (line-start, whole file)
#   S2  comment-stripped forbidden tokens: sorry, native_decide, axiom,
#       maxHeartbeats, maxRecDepth, partial def, unsafe, extern, Classical
#       -- after stripping /- -/ blocks and -- line comments, count must be 0
#   S3  header discipline: PARK / LABEL / ADJUDICATOR / CLEARED all stated
#       BEFORE the first declaration
#   S4  the two transcript prose hits (sorry, native_decide) are both
#       Verlinde.lean:7, header prose, and are the ONLY textual hits
#   S5  omega discipline: every omega site sits behind a refine-split
#       (no conjunctive-goal omega -- HANDOFF trap 1)
#   S6  no zeta20 constructed: token absent from comment-stripped code
#   S7  theorem count = 75, and the file's hash matches both instrument
#       outputs (transcript-round7.txt, axioms-round7.txt)
#   S8  the house transcription check runs and PASSES (covers Zp.mul,
#       Z5.mul, fuse for Verlinde; Zp.conj declared NEW)
#   S9  the AXIOM RECEIPTS header is present and EMPTY (receipts stripped
#       for silent compile, as the ledger records) -- no #print in file
#
# WHAT IT DOES NOT CHECK: semantics of any identity (r7s_v2_semantics.py),
# ledger reconciliation and the full copied-surface byte comparison
# (r7s_v3_ledger.py).  Exit 0 iff every PASS.
# Usage: sh audit/r7s_v1_structure.sh     (from workshop/lean/)
# ---------------------------------------------------------------------------
set -u
F=Verlinde.lean
fail=0
say() { printf '%s\n' "$1"; }
res() { # $1 PASS/FAIL  $2 name  $3 detail
  printf '%-4s  %-28s %s\n' "$1" "$2" "$3"
  [ "$1" = "FAIL" ] && fail=1
}

[ -f "$F" ] || { echo "FAIL  file-missing  $F not found"; exit 1; }

# --- comment stripper (Lean block + line comments), used by S2/S6 ---------
strip_comments() {
  python3 - "$1" <<'EOF'
import sys,re
s=open(sys.argv[1],encoding="utf-8").read()
# remove nested /- ... -/ blocks
out=[];i=0;depth=0
while i<len(s):
    if s.startswith("/-",i): depth+=1; i+=2; continue
    if depth and s.startswith("-/",i): depth-=1; i+=2; continue
    if depth==0: out.append(s[i])
    i+=1
t="".join(out)
t=re.sub(r'--[^\n]*','',t)      # line comments
sys.stdout.write(t)
EOF
}

CODE=$(strip_comments "$F")

# S1: zero imports / axiom declarations -----------------------------------
ni=$(grep -c '^import' "$F" || true)
na=$(grep -c '^axiom' "$F" || true)
if [ "$ni" -eq 0 ] && [ "$na" -eq 0 ]; then
  res PASS S1_zero_imports "line-start import=0 axiom=0"
else
  res FAIL S1_zero_imports "import=$ni axiom=$na"
fi

# S2: forbidden tokens in comment-stripped code ---------------------------
bad=""
for tok in "sorry" "native_decide" "axiom" "maxHeartbeats" "maxRecDepth" \
           "partial def" "unsafe" "@\[extern" "Classical" "#print" "#eval"; do
  n=$(printf '%s' "$CODE" | grep -c "$tok" || true)
  [ "$n" -gt 0 ] && bad="$bad $tok:$n"
done
if [ -z "$bad" ]; then
  res PASS S2_stripped_tokens "0 forbidden tokens in code (11 token classes swept)"
else
  res FAIL S2_stripped_tokens "found:$bad"
fi

# S3: header discipline ---------------------------------------------------
first_decl=$(grep -n '^namespace\|^inductive\|^def\|^theorem\|^structure' "$F" | head -1 | cut -d: -f1)
head_txt=$(head -n "$((first_decl-1))" "$F")
ok=1
for want in "PARK" "LABEL" "ADJUDICATOR" "CLEARED" "NO imports"; do
  printf '%s' "$head_txt" | grep -q "$want" || { ok=0; bad="$want"; }
done
if [ "$ok" -eq 1 ]; then
  res PASS S3_header_discipline "PARK/LABEL/ADJUDICATOR/CLEARED/NO-imports all before first decl (line $first_decl)"
else
  res FAIL S3_header_discipline "missing '$bad' before line $first_decl"
fi

# S4: the two transcript prose hits are line 7 and are the only hits ------
s_lines=$(grep -n 'sorry' "$F" | cut -d: -f1 | tr '\n' ' ')
n_lines=$(grep -n 'native_decide' "$F" | cut -d: -f1 | tr '\n' ' ')
l7=$(sed -n '7p' "$F")
if [ "$s_lines" = "7 " ] && [ "$n_lines" = "7 " ] && \
   printf '%s' "$l7" | grep -q 'No `sorry`, no `native_decide`'; then
  res PASS S4_prose_hits "sorry+native_decide each exactly once, both at line 7 (header prose)"
else
  res FAIL S4_prose_hits "sorry at [$s_lines] native_decide at [$n_lines]"
fi

# S5: omega discipline ----------------------------------------------------
nomega=$(grep -c 'omega' "$F" || true)
nsplit=$(grep 'omega' "$F" | grep -c 'refine ⟨' || true)
if [ "$nomega" -gt 0 ] && [ "$nomega" -eq "$nsplit" ]; then
  res PASS S5_omega_discipline "$nomega omega sites, all on refine-split lines (no conjunctive-goal omega)"
else
  res FAIL S5_omega_discipline "$nomega omega sites, only $nsplit behind refine-split"
fi

# S6: no zeta20 constructed ----------------------------------------------
nz20code=$(printf '%s' "$CODE" | grep -ci 'zeta20\|ζ₂₀' || true)
nz20all=$(grep -ci 'zeta20\|ζ₂₀' "$F" || true)
if [ "$nz20code" -eq 0 ] && [ "$nz20all" -gt 0 ]; then
  res PASS S6_no_zeta20_in_code "zeta20 only in comments ($nz20all mentions), never in code -- the park is real"
elif [ "$nz20code" -eq 0 ]; then
  res FAIL S6_no_zeta20_in_code "zeta20 absent even from comments -- park not documented?"
else
  res FAIL S6_no_zeta20_in_code "zeta20 appears in CODE ($nz20code): the park is broken"
fi

# S7: theorem count and hashes -------------------------------------------
nthm=$(grep -c '^theorem .*:' "$F" || true)
h=$(sha256sum "$F" | cut -d' ' -f1)
ht=$(grep -A0 'Verlinde.lean' audit/transcript-round7.txt | head -1 | awk '{print $2}')
ha=$(grep 'Verlinde.lean' audit/axioms-round7.txt | head -1 | awk '{print $2}')
if [ "$nthm" -eq 75 ] && [ "$h" = "$ht" ] && [ "$h" = "$ha" ]; then
  res PASS S7_count_and_hash "75 theorems; sha256 $h matches transcript + axioms outputs"
else
  res FAIL S7_count_and_hash "theorems=$nthm hash=$h transcript=$ht axioms=$ha"
fi

# S8: house transcription check ------------------------------------------
if sh audit/transcription.sh >/tmp/r7s_transcription.out 2>&1; then
  vl=$(grep -A6 'Verlinde.lean ring cores' /tmp/r7s_transcription.out | grep -c 'identical' || true)
  if [ "$vl" -eq 3 ]; then
    res PASS S8_transcription_sh "exit 0; Verlinde section: Zp.mul, Z5.mul, fuse identical; Zp.conj declared NEW"
  else
    res FAIL S8_transcription_sh "exit 0 but Verlinde identical-count=$vl (want 3)"
  fi
else
  res FAIL S8_transcription_sh "audit/transcription.sh exited nonzero"
fi

# S9: AXIOM RECEIPTS header present and empty ----------------------------
rl=$(grep -n 'AXIOM RECEIPTS' "$F" | cut -d: -f1)
np=$(grep -c '#print' "$F" || true)
if [ -n "$rl" ] && [ "$np" -eq 0 ]; then
  res PASS S9_receipts_stripped "AXIOM RECEIPTS header at line $rl, no #print in file (stripped for silent compile, per ledger)"
else
  res FAIL S9_receipts_stripped "header line='$rl' #print count=$np"
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: structure + hygiene PASS (9/9)."
else
  echo "RESULT: FAIL -- see lines above."
fi
exit $fail
