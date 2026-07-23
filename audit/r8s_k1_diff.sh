#!/bin/sh
# r8s_k1_diff.sh -- ROUND-8 TERMINAL AUDIT, K1 (the coker seat).
# Diff archive/src-round7/MagicSquare.lean vs MagicSquare.lean: the round-8
# change must be exactly (a) the rewritten S6 disclaimer and (b) one inserted
# section S6.5 of 220 lines; enumerate every new declaration; theorem count
# must go 63 -> 85 (+22).
# Standalone: needs only sh + diff + python3. Exit 0 = PASS, 1 = FAIL.
set -u
L=/home/claude/workshop/lean
OLD="$L/archive/src-round7/MagicSquare.lean"
NEW="$L/MagicSquare.lean"
fail=0
say() { echo "$@"; }

[ -f "$OLD" ] && [ -f "$NEW" ] || { echo "FAIL: files missing"; exit 1; }

# --- (1) the diff shape: exactly two hunks -----------------------------------
HUNKS=$(diff "$OLD" "$NEW" | grep -c '^[0-9]')
H1=$(diff "$OLD" "$NEW" | grep '^[0-9]' | sed -n 1p)
H2=$(diff "$OLD" "$NEW" | grep '^[0-9]' | sed -n 2p)
say "hunk count            : $HUNKS   (want 2)"
say "hunk 1 (disclaimer)   : $H1   (want 310c310 + 314,320c314,323 pattern...)"
say "hunk 2 (new section)  : $H2"
[ "$HUNKS" = "3" ] || [ "$HUNKS" = "2" ] || { say "FAIL: unexpected hunk count"; fail=1; }
# expected hunks: 310c310 ; 314,320c314,323 ; 469a473,692
diff "$OLD" "$NEW" | grep '^[0-9]' > /tmp/r8s_k1_hunks.txt
if ! diff /tmp/r8s_k1_hunks.txt - <<'EOF' >/dev/null 2>&1
310c310
314,320c314,323
469a473,692
EOF
then say "FAIL: hunk addresses differ from expected (310c310 / 314,320c314,323 / 469a473,692)"; cat /tmp/r8s_k1_hunks.txt; fail=1
else say "hunk addresses        : 310c310, 314,320c314,323, 469a473,692  -- disclaimer rewrite + one pure 220-line insertion  OK"
fi
INS=$(diff "$OLD" "$NEW" | grep -c '^> ')
DEL=$(diff "$OLD" "$NEW" | grep -c '^< ')
say "inserted lines        : $INS  (want 231 = 1 title + 10 disclaimer + 220 section)"
say "deleted lines         : $DEL  (want 8 = 1 title + 7 old disclaimer)"
[ "$INS" = "231" ] && [ "$DEL" = "8" ] || { say "FAIL: line arithmetic"; fail=1; }
NEWSEC=$((692 - 473 + 1))
say "new section lines     : 473..692 = $NEWSEC"
[ "$NEWSEC" = "220" ] || fail=1

# --- (2) enumerate every new declaration (comment-stripped) ------------------
python3 - "$OLD" "$NEW" <<'PY' || fail=1
import re, sys
def strip(txt):
    out, i, depth, n = [], 0, 0, len(txt)
    while i < n:
        if txt.startswith('/-', i): depth += 1; i += 2; continue
        if depth and txt.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: out.append('\n' if txt[i]=='\n' else ' '); i += 1; continue
        if txt.startswith('--', i):
            j = txt.find('\n', i); i = n if j < 0 else j; continue
        out.append(txt[i]); i += 1
    return ''.join(out)
def decls(path):
    t = strip(open(path, encoding='utf-8').read())
    return [(k, nm) for k, nm in re.findall(
        r'^(theorem|def|abbrev|inductive|structure)\s+([A-Za-z0-9_\'.]+)', t, re.M)]
old, new = decls(sys.argv[1]), decls(sys.argv[2])
oldset = {nm for _, nm in old}
newdecls = [(k, nm) for k, nm in new if nm not in oldset]
thms = [nm for k, nm in newdecls if k == 'theorem']
defs = [nm for k, nm in newdecls if k == 'def']
abbr = [nm for k, nm in newdecls if k == 'abbrev']
print(f"round-7 theorem decls : {sum(1 for k,_ in old if k=='theorem')}  (want 63)")
print(f"round-8 theorem decls : {sum(1 for k,_ in new if k=='theorem')}  (want 85)")
print(f"new decls             : {len(newdecls)}  = {len(thms)} theorems + {len(defs)} defs + {len(abbr)} abbrev")
print("new defs              :", ', '.join(defs))
print("new abbrev            :", ', '.join(abbr))
print("new theorems          :")
for nm in thms: print("   ", nm)
EXP_T = ['image_iff_even','imageCount_eq_32','b_not_in_image','phiBits_xor',
         'phiV_vxor','xor_false_iff','cokerRel_iff','cokerRel_refl',
         'cokerRel_symm','cokerRel_trans','phiV_zeroVec','phiV_bVec','toZ2_mk',
         'phiV_cond','toZ2_fromZ2','fromZ2_toZ2','toZ2_hom','coker_two_classes',
         'coker_classes_distinct','class_of_b_nonzero','coker_identifies',
         'coker_separates']
EXP_D = ['phiV','phiBits','inImage','imageCount','vxor','zeroVec','bVec',
         'inImageV','cokerRel','cokerSetoid','toZ2','fromZ2']
ok = (thms == EXP_T and defs == EXP_D and abbr == ['Coker']
      and sum(1 for k,_ in old if k=='theorem') == 63
      and sum(1 for k,_ in new if k=='theorem') == 85)
print("declaration audit     :", "OK (22 theorems + 12 defs + abbrev Coker; 63 -> 85)" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
PY

if [ "$fail" = "0" ]; then echo "r8s_k1_diff: PASS"; exit 0
else echo "r8s_k1_diff: FAIL"; exit 1; fi
