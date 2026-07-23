#!/bin/sh
# ---------------------------------------------------------------------------
# r7s_v4_bite.sh -- ROUND-7 SEAT: norm-14 falsifier run on the class-10
# instrument's NEW Verlinde section.  A check that cannot fail is not a
# check (norm 7); an unrun falsifier is a sentence about the model (norm 14).
#
# In a /tmp copy of the tree:
#   B1  flip one character in Verlinde's Zp.mul formula     -> DRIFTED, exit 1
#   B2  flip one character in Verlinde's Z5.mul c-vector    -> DRIFTED, exit 1
#   B3  swap `fuse a b` case order in Verlinde's fuse       -> DRIFTED, exit 1
#   B4  clean copy                                          -> PASS,   exit 0
# The planted drifts are the smallest meaning-changing edits available --
# exactly the "true of a different ring" failure class-10 exists to catch.
# Exit 0 iff all four behave.  Usage: sh audit/r7s_v4_bite.sh
# ---------------------------------------------------------------------------
set -u
fail=0
res() { printf '%-4s  %-24s %s\n' "$1" "$2" "$3"; [ "$1" = "FAIL" ] && fail=1; }

stage() {  # fresh /tmp tree with the three files transcription.sh reads
  W=$(mktemp -d /tmp/r7s_bite.XXXXXX)
  cp Anyon.lean Rigidity.lean Verlinde.lean "$W"/
  mkdir -p "$W/audit"; cp audit/transcription.sh "$W/audit/"
  echo "$W"
}

# B1: Zp.mul drift (u.n * v.n -> u.n * v.m in the second component)
W=$(stage)
sed -i 's/u\.m \* v\.n + u\.n \* v\.m + u\.n \* v\.n⟩/u.m * v.n + u.n * v.m + u.n * v.m⟩/' "$W/Verlinde.lean"
out=$( cd "$W" && sh audit/transcription.sh 2>&1 ); rc=$?
if [ $rc -ne 0 ] && printf '%s' "$out" | grep -q 'DRIFTED     Zp.mul'; then
  res PASS B1_zp_mul_drift "one-char drift in Zp.mul -> DRIFTED + exit $rc"
else
  res FAIL B1_zp_mul_drift "exit=$rc; DRIFTED not reported"
fi
rm -rf "$W"

# B2: Z5.mul drift (c2 - c4 -> c2 + c4)
W=$(stage)
sed -i 's/c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4/c0 - c4 + c5, c1 - c4 + c6, c2 + c4, c3 - c4/' "$W/Verlinde.lean"
out=$( cd "$W" && sh audit/transcription.sh 2>&1 ); rc=$?
if [ $rc -ne 0 ] && printf '%s' "$out" | grep -q 'DRIFTED     Z5.mul'; then
  res PASS B2_z5_mul_drift "one-char drift in Z5.mul -> DRIFTED + exit $rc"
else
  res FAIL B2_z5_mul_drift "exit=$rc; DRIFTED not reported"
fi
rm -rf "$W"

# B3: fuse drift (swap the .tau,.tau channel order [.one,.tau] -> [.tau,.one])
W=$(stage)
python3 - "$W/Verlinde.lean" <<'EOF'
import sys
p=sys.argv[1]; s=open(p,encoding="utf-8").read()
old="""def fuse : Anyon → Anyon → List Anyon
  | .one, b    => [b]
  | a,    .one => [a]
  | .tau, .tau => [.one, .tau]"""
new=old.replace("[.one, .tau]","[.tau, .one]")
assert s.count(old)==1
open(p,"w",encoding="utf-8").write(s.replace(old,new))
EOF
out=$( cd "$W" && sh audit/transcription.sh 2>&1 ); rc=$?
if [ $rc -ne 0 ] && printf '%s' "$out" | grep -q 'DRIFTED     fuse'; then
  res PASS B3_fuse_drift "channel-order drift in fuse -> DRIFTED + exit $rc"
else
  res FAIL B3_fuse_drift "exit=$rc; DRIFTED not reported"
fi
rm -rf "$W"

# B4: clean copy passes
W=$(stage)
out=$( cd "$W" && sh audit/transcription.sh 2>&1 ); rc=$?
if [ $rc -eq 0 ] && printf '%s' "$out" | grep -q 'RESULT: every copied definition matches'; then
  res PASS B4_clean_passes "unmodified copy -> PASS + exit 0 (the alarm is quiet when it should be)"
else
  res FAIL B4_clean_passes "exit=$rc on a clean tree"
fi
rm -rf "$W"

echo
if [ "$fail" -eq 0 ]; then
  echo "RESULT: the class-10 alarm fires on all three planted Verlinde drifts and is quiet on clean.  PASS."
else
  echo "RESULT: FAIL -- an alarm did not behave."
fi
exit $fail
