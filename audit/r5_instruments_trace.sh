#!/bin/sh
# ---------------------------------------------------------------------------
# r5_instruments_trace.sh -- round-4 adversarial audit of the three shell
# instruments (audit/axioms.sh, audit/transcript.sh, audit/ship.sh).
#
# No Lean toolchain exists here, so the two Lean-invoking instruments are run
# END-TO-END against a STUB kernel placed at $HOME/.elan/bin/lean (the exact
# path axioms.sh/transcript.sh prepend to PATH).  This traces the real shipped
# scripts byte-for-byte, not a transcription of them.
#
# One PASS/FAIL line per check.  Exit 1 on any FAIL.
# ---------------------------------------------------------------------------
set -u
LEAN=/home/claude/workshop/lean
SB=/tmp/r5sb
fails=0
ck() { # ck NAME 0/1
  if [ "$2" -eq 0 ]; then echo "PASS  $1"; else echo "FAIL  $1"; fails=$((fails+1)); fi
}

rm -rf "$SB"
mkdir -p "$SB/home/.elan/bin" "$SB/lean/audit" "$SB/real/audit"

# ---- stub kernel ----------------------------------------------------------
cat > "$SB/home/.elan/bin/lean" <<'STUB'
#!/bin/sh
# stub Lean kernel for instrument tracing
if [ "${1:-}" = "--version" ]; then echo "Lean (stub 4.32.0)"; exit 0; fi
if [ "${1:-}" = "-o" ]; then
  # transcript mode: lean -o out.olean src
  if [ -z "${STUB_NO_OLEAN:-}" ]; then printf 'stub-olean-of %s\n' "$3" > "$2"; fi
  [ -n "${STUB_NOISY:-}" ] && echo "warning: stub noise on $3"
  exit 0
fi
# census mode: answer each '#print axioms X' line; ORACLE mode accepts all
src="$1"
while IFS= read -r line; do
  case "$line" in
    "#print axioms "*)
      name=${line#"#print axioms "}
      if [ -n "${STUB_ORACLE:-}" ]; then
        echo "'$name' does not depend on any axioms"; continue
      fi
      case "$name" in
        "Workshop.Anyon.KK.rt'_root_quadratic")
          echo "'$name' depends on axioms: [propext]";;
        Workshop.Anyon.Z5.add_comm|Workshop.Anyon.Z5.eq_of_sub_eq_zero|W.i_one|MS.real_one|EX.e_one)
          echo "'$name' does not depend on any axioms";;
        *)
          echo "$src:1:0: error: unknown constant '$name'";;
      esac;;
  esac
done < "$src"
exit 0
STUB
chmod +x "$SB/home/.elan/bin/lean"

# ---- synthetic sandbox sources -------------------------------------------
printf 'leanprover/lean4:v4.32.0\n' > "$SB/lean/lean-toolchain"

cat > "$SB/lean/Interchange.lean" <<'EOF'
namespace W
theorem i_one : True := trivial
theorem multiline_head
  : True := trivial
end W
EOF

cat > "$SB/lean/MagicSquare.lean" <<'EOF'
namespace MS
theorem real_one : (1 : Nat) = 1 := rfl
end MS
/- section-6 style prose, at column 0, replicating MagicSquare.lean:320:
theorems below as the only part machine-checked. -/
EOF

cat > "$SB/lean/Anyon.lean" <<'EOF'
namespace Workshop.Anyon
namespace Z5
theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b
end Z5
namespace KK
theorem _root_.Workshop.Anyon.Z5.eq_of_sub_eq_zero (h : True) : True := trivial
theorem rt'_root_quadratic : True := trivial
end KK
end Workshop.Anyon
EOF

cat > "$SB/lean/Exchangeable.lean" <<'EOF'
namespace EX
theorem e_one : True := trivial
end EX
EOF

cp "$LEAN/audit/axioms.sh" "$LEAN/audit/transcript.sh" "$SB/lean/audit/"

# ===========================================================================
# RUN A: real axioms.sh over the synthetic sandbox (clean pass)
# ===========================================================================
outA=$(cd "$SB/lean" && HOME="$SB/home" sh audit/axioms.sh 2>&1)
rcA=$?
work=$(printf '%s\n' "$outA" | sed -n 's/^raw output kept in: \(.*\)\/raw.txt$/\1/p')

ck "A1 axioms.sh run A clean: no SCRIPT ERROR, no INCOMPLETE" \
   "$(printf '%s\n' "$outA" | grep -c 'SCRIPT ERROR\|INCOMPLETE' )"

emitted=$(grep '^#print axioms ' "$work/Anyon.lean" 2>/dev/null)
printf '%s\n' "$emitted" | grep -qx '#print axioms Workshop.Anyon.Z5.add_comm'
ck "A2 nested-namespace name rebuilt: Workshop.Anyon.Z5.add_comm" $?

printf '%s\n' "$emitted" | grep -qx '#print axioms Workshop.Anyon.Z5.eq_of_sub_eq_zero'
r1=$?
printf '%s\n' "$emitted" | grep -q '_root_\.\|KK\.eq_of_sub'
r2=$?   # must NOT find: literal '_root_.' residue or a wrong KK. prefix
        # (note rt'_root_quadratic legitimately CONTAINS '_root_' sans dot)
[ $r1 -eq 0 ] && [ $r2 -ne 0 ]; ck "A3 _root_ branch: absolute name emitted, no KK prefix, no _root_ residue" $?

printf '%s\n' "$emitted" | grep -qx "#print axioms Workshop.Anyon.KK.rt'_root_quadratic"
ck "A4 primed name survives the shell-quote dance verbatim" $?
printf '%s\n' "$outA" | grep -q 'Anyon *\[propext\] *1'
ck "A4b tally attributes the primed theorem: Anyon [propext] 1" $?

n_ms=$(grep -c '^#print axioms ' "$work/MagicSquare.lean")
[ "$n_ms" -eq 1 ]; ck "A5 MagicSquare prose line ('theorems below...') NOT censused (1 real theorem -> 1 print)" $?

# guard probes: what actually excludes the D3 line?
probe_nog=$(printf 'theorems below as the only part machine-checked. -/\n' | awk "/^theorem [A-Za-z_0-9']+/ {c++} END{print c+0}")
[ "$probe_nog" -eq 0 ]; ck "A5b D3 line excluded by the SPACE anchor alone (guard not operative on it)" $?
probe_real320=$(sed -n '320p' "$LEAN/MagicSquare.lean" | awk "/^theorem [A-Za-z_0-9']+/ {c++} END{print c+0}")
[ "$probe_real320" -eq 0 ]; ck "A5c real MagicSquare.lean:320 likewise excluded pattern-side without the /:/ guard" $?
p1=$(printf 'theorem foo is discussed in prose above with no colon\n' | awk "/^theorem [A-Za-z_0-9']+/ {c++} END{print c+0}")
p2=$(printf 'theorem foo is discussed in prose above with no colon\n' | awk "/^theorem [A-Za-z_0-9']+/ && /:/ {c++} END{print c+0}")
[ "$p1" -eq 1 ] && [ "$p2" -eq 0 ]; ck "A6 the /:/ guard IS operative for singular 'theorem <word>' prose (its real function)" $?

n_int=$(grep -c '^#print axioms ' "$work/Interchange.lean")
tbl_int=$(printf '%s\n' "$outA" | awk '$1=="Interchange"{print $2}')
[ "$n_int" -eq 1 ] && [ "$tbl_int" = "1" ]; ck "A7 SILENT UNDER-COVERAGE DEMONSTRATED: multi-line header theorem skipped, no error, table shows 1 of 2" $?

printf '%s\n' "$outA" | awk '$1=="TOTAL"{exit !($2==6 && $3==5 && $4==1)}'
ck "A9 tally arithmetic: TOTAL 6, free 5, rest 1" $?

# ===========================================================================
# RUN B: adversarial prose WITH a colon -> census must go loud (INCOMPLETE)
# ===========================================================================
cp "$SB/lean/Exchangeable.lean" "$SB/lean/Exchangeable.lean.bak"
printf 'theorem bar means: the discussion above, in prose at column zero -/\n' >> "$SB/lean/Exchangeable.lean"
outB=$(cd "$SB/lean" && HOME="$SB/home" sh audit/axioms.sh 2>&1)
rcB=$?
printf '%s\n' "$outB" | grep -q "SCRIPT ERROR: .*unknown constant 'bar'" && \
printf '%s\n' "$outB" | grep -q 'script errors -- the census is INCOMPLETE'
ck "B1 error branch: prose-with-colon emits bad constant -> SCRIPT ERROR + INCOMPLETE (loud, not silent)" $?
[ "$rcB" -eq 0 ]; ck "B2 FINDING CONFIRMED: axioms.sh exits 0 even when INCOMPLETE (alarm is print-only)" $?
mv "$SB/lean/Exchangeable.lean.bak" "$SB/lean/Exchangeable.lean"

# ===========================================================================
# RUN C/D/E: real transcript.sh -- clean pass, noisy fail, missing olean
# ===========================================================================
outC=$(cd "$SB/lean" && HOME="$SB/home" sh audit/transcript.sh 2>&1); rcC=$?
printf '%s\n' "$outC" | grep -q 'RESULT: all files compiled silent' && [ "$rcC" -eq 0 ]
ck "C1 transcript.sh clean run: RESULT PASS, exit 0" $?
cnts=$(printf '%s\n' "$outC" | awk '/^  (Interchange|MagicSquare|Anyon|Exchangeable)\.lean/{printf "%s ", $2} /^  TOTAL/{print $2}')
[ "$cnts" = "1 1 3 1 6" ]; ck "C2 transcript theorem counts 1/1/3/1=6 == census run-A total 6 (same regex, agreement by construction)" $?

outD=$(cd "$SB/lean" && HOME="$SB/home" STUB_NOISY=1 sh audit/transcript.sh 2>&1); rcD=$?
printf '%s\n' "$outD" | grep -q 'NOT SILENT' && printf '%s\n' "$outD" | grep -q 'RESULT: at least one file was not silent' && [ "$rcD" -eq 1 ]
ck "D1 nonzero log CANNOT pass: noisy stub -> NOT SILENT + RESULT FAIL + exit 1" $?

outE=$(cd "$SB/lean" && HOME="$SB/home" STUB_NO_OLEAN=1 sh audit/transcript.sh 2>&1); rcE=$?
printf '%s\n' "$outE" | grep -q '(no olean produced)' && [ "$rcE" -eq 0 ]
ck "E1 FINDING CONFIRMED: silent exit-0 run with NO .olean still passes (absence printed, not failed)" $?

# ===========================================================================
# RUN G: real axioms.sh over the REAL round-3 sources with an oracle stub
#         -> the generator's per-file emission counts, end to end
# ===========================================================================
cp "$LEAN/Interchange.lean" "$LEAN/MagicSquare.lean" "$LEAN/Anyon.lean" \
   "$LEAN/Exchangeable.lean" "$LEAN/lean-toolchain" "$SB/real/"
cp "$LEAN/audit/axioms.sh" "$SB/real/audit/"
outG=$(cd "$SB/real" && HOME="$SB/home" STUB_ORACLE=1 sh audit/axioms.sh 2>&1)
workG=$(printf '%s\n' "$outG" | sed -n 's/^raw output kept in: \(.*\)\/raw.txt$/\1/p')
printf '%s\n' "$outG" | awk '
  $1=="Interchange"  && $2==21  {a=1}
  $1=="MagicSquare"  && $2==63  {b=1}
  $1=="Anyon"        && $2==245 {c=1}
  $1=="Exchangeable" && $2==41  {d=1}
  $1=="TOTAL"        && $2==370 {e=1}
  END{exit !(a&&b&&c&&d&&e)}'
ck "G1 census emission counts on REAL round-3 sources: 21/63/245/41 = 370 (matches round-3 ledger exactly)" $?
printf '%s\n' "$outG" | grep -q 'SCRIPT ERROR\|INCOMPLETE'
[ $? -ne 0 ]; ck "G2 no errors censusing real sources (no prose false-positive fires on round-3 text)" $?
bad_names=$(grep '^#print axioms ' "$workG/Anyon.lean" | grep -cv '^#print axioms Workshop\.Anyon\.')
[ "$bad_names" -eq 0 ]; ck "G3 every Anyon emission carries the Workshop.Anyon. prefix (namespace stack coherent over 2469 lines)" $?
grep -qx "#print axioms Workshop.Anyon.rt'_root_quadratic" "$workG/Anyon.lean" && \
grep -qx "#print axioms Workshop.Anyon.rt'_root_quadratic_structural" "$workG/Anyon.lean"
r=$?
# rt'_root_quadratic at 633: between end KK(341) and namespace Z5(667) -> Workshop.Anyon level
# rt'_root_quadratic_structural at 2023: between end KK(1879) and namespace Zp(2116) -> same level
ck "G4 spot-check both primed round-3 theorems emitted with hand-derived nesting" $r

# ===========================================================================
# S: ship.sh receive-side semantics (grep -qx + unzip), tested with real tools
# ===========================================================================
printf 'archive/PROOFS-round1.md\n' | grep -qx "\./PROOFS.md\|PROOFS.md"
[ $? -ne 0 ]; ck "S1 grep -x: required name as SUBSTRING/suffix of another entry does NOT false-match" $?
printf 'PROOFS.md\n' | grep -qx "\./PROOFS.md\|PROOFS.md" && \
printf './PROOFS.md\n' | grep -qx "\./PROOFS.md\|PROOFS.md"
ck "S2 grep -x: both accepted forms (bare and ./-prefixed) whole-line match" $?
printf 'PROOFS.md.bak\n' | grep -qx "\./PROOFS.md\|PROOFS.md"
[ $? -ne 0 ]; ck "S3 grep -x: trailing-junk entry rejected (alternation is whole-line anchored per branch)" $?
printf 'audit\\axioms.sh\n' | grep -qx "\./audit/axioms.sh\|audit/axioms.sh"
[ $? -ne 0 ]; ck "S4 round-3 disease: backslash entry name reported MISSING (fail-loud, as designed)" $?
printf 'PROOFSxmd\n' | grep -qx "\./PROOFS.md\|PROOFS.md"
ck "S5 REGEX LAXITY CONFIRMED: unescaped '.' is a wildcard, PROOFSxmd satisfies the presence check" $?

# unzip round-trip: presence laxity is caught by the content (staleness) step
mkdir -p "$SB/zip/audit"
printf 'round-4 ledger content\n'  > "$SB/zip/PROOFS.md"
printf 'echo instrument\n'         > "$SB/zip/audit/axioms.sh"
python3 - "$SB" <<'PY'
import sys, zipfile, os
sb = sys.argv[1]
z = zipfile.ZipFile(os.path.join(sb, "crate.zip"), "w")
z.write(os.path.join(sb, "zip/PROOFS.md"), "PROOFSxmd")          # wildcard-satisfying decoy
z.write(os.path.join(sb, "zip/audit/axioms.sh"), "audit/axioms.sh")
z.writestr("audit\\transcript.sh", "backslash disease entry")     # round-3 disease
z.close()
PY
listing=$(unzip -Z1 "$SB/crate.zip")
printf '%s\n' "$listing" | grep -qx "\./PROOFS.md\|PROOFS.md"
pres=$?   # 0 = presence check (wrongly) satisfied by decoy
th=$(sha256sum "$SB/zip/PROOFS.md" | cut -c1-64)
ah=$(cd "$SB/zip" && unzip -p "$SB/crate.zip" "PROOFS.md" 2>/dev/null | sha256sum | cut -c1-64)
[ "$pres" -eq 0 ] && [ "$th" != "$ah" ]
ck "S6 COMPOSITION SOUND: wildcard decoy passes presence but content step yields empty-extract hash mismatch -> STALE -> FAIL" $?
th2=$(sha256sum "$SB/zip/audit/axioms.sh" | cut -c1-64)
ah2=$(unzip -p "$SB/crate.zip" "audit/axioms.sh" 2>/dev/null | sha256sum | cut -c1-64)
[ "$th2" = "$ah2" ]; ck "S7 honest entry: unzip -p exact-name extraction hash == tree hash (staleness check mechanics sound)" $?
printf 'tampered\n' >> "$SB/zip/audit/axioms.sh"
th3=$(sha256sum "$SB/zip/audit/axioms.sh" | cut -c1-64)
[ "$th3" != "$ah2" ]; ck "S8 staleness bites: post-build tree edit diverges from archive hash (STALE branch reachable)" $?
printf '%s\n' "$listing" | grep -qx "\./audit/transcript.sh\|audit/transcript.sh"
[ $? -ne 0 ]; ck "S9 backslash entry in a real zip is NOT matched for the required path (MISSING, loud)" $?

# REQUIRED-list arithmetic from the shipped ship.sh
req=$(awk '/^REQUIRED="/,/^"/' "$LEAN/audit/ship.sh" | grep -v '"' | grep -c .)
[ "$req" -eq 15 ]; ck "S10 REQUIRED list is exactly 15 paths; 22-entry crate leaves exactly 7 unrequired" $?
miss=0
for f in $(awk '/^REQUIRED="/,/^"/' "$LEAN/audit/ship.sh" | grep -v '"'); do
  [ -f "$LEAN/$f" ] || { miss=1; echo "        absent builder-side: $f"; }
done
ck "S11 all 15 REQUIRED paths exist in the builder-side tree (four .lean here are ROUND-3 versions)" $miss

echo
if [ "$fails" -eq 0 ]; then echo "r5_instruments_trace: ALL CHECKS PASS"; else echo "r5_instruments_trace: $fails FAILURE(S)"; fi
exit "$fails"
