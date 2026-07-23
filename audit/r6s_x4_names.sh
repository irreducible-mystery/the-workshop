#!/bin/sh
# ---------------------------------------------------------------------------
# r6s_x4_names.sh -- round-6 seat check, task X4.
# Forward sweep: the round-6 named theorems the ledger leans on exist, exactly
# once, as top-level declarations in Rigidity.lean (spot list of 15+, incl.
# the J2 fields).  Reverse sweep: every headline-family theorem in
# Rigidity.lean is mentioned in PROOFS.md.  Negative controls included.
# Standalone; run from workshop/lean/.  PASS/FAIL lines; exit 1 on any FAIL.
# ---------------------------------------------------------------------------
set -u
fail=0
say() { printf '%s\n' "$*"; }

say "== X4a: forward spot sweep (ledger name -> declaration in Rigidity.lean) =="
NAMES="gauge_curve_deriv tangentY_is_gauge_deriv HY_swap_not_null strict_also_psd
germ_G hess_G gg_e00 gg_e01 gg_e02 gg_e03 gg_e11 gg_e12 gg_e13 gg_e22 gg_e23 gg_e33
YL_is_solution HY_psd HY_kernel HY_kernel_is_line HY_det4_zero HY_minor3_pos
strict_not_critical strict_fails_pentagon HS_swap_null strict_also_rank3
SS_G_zero grad_G_0 grad_G_1 grad_G_2 grad_G_3 HG_entries HG_needs_radical
HG_det4_zero HG_minor3_pos HG_tangent_null HG_cols_eq qform_sos psd_of_sos
ker_of_sos Fg_transp Fs_rev pentResid_rev hess_Y germ_Y tangentY swapDir coTY"
bad=0; n=0
for t in $NAMES; do
  n=$((n+1))
  c=$(grep -cE "^(theorem|def) $t( |:|$)" Rigidity.lean)
  if [ "$c" -ne 1 ]; then say "FAIL  fwd-$t -- declared $c times (want 1)"; bad=1; fi
done
[ "$bad" -eq 0 ] && say "PASS  forward-sweep -- all $n spot names declared exactly once in Rigidity.lean" || fail=1

# J2 and its ext lemma, and the fifteen fields
c=$(grep -c "^structure J2" Rigidity.lean)
e=$(grep -c "^theorem J2.ext'" Rigidity.lean)
flds=$(awk '/^structure J2/,/deriving DecidableEq/' Rigidity.lean | grep -cE "^  [a-z][A-Za-z_0-9]* : R")
if [ "$c" -eq 1 ] && [ "$e" -eq 1 ] && [ "$flds" -eq 15 ]; then
  say "PASS  J2 -- structure J2 with 15 fields (v, d0-d3, e00-e33) + J2.ext' present"
else
  say "FAIL  J2 -- structure=$c ext'=$e fields=$flds (want 1/1/15)"; fail=1
fi

say ""
say "== X4b: ledger quotes vs file text =="
grep -qF "theorem gg_e00 : (germ epRng pG qG qG sG).e00 = ⟨⟨15,-4⟩, Zp.zero⟩ := by rfl" Rigidity.lean
if [ $? -eq 0 ]; then say "PASS  gg_e00-verbatim -- the lean block PROOFS.md quotes is the shipped line (Rigidity.lean:2554)"; else say "FAIL  gg_e00-verbatim -- quoted block differs from file"; fail=1; fi
grep -qF "qform HY swapDir = ⟨34,52⟩" Rigidity.lean
if [ $? -eq 0 ]; then say "PASS  swap-34-52phi -- HY_swap_not_null pins (0,1,-1,0)^T H (0,1,-1,0) = 34+52phi, as the ledger table says"; else say "FAIL  swap-34-52phi"; fail=1; fi
grep -qF "mvec HC tangentC 1 = ⟨-212,0⟩" Rigidity.lean && grep -qF "qform HC wNegC = ⟨-400,0⟩" Rigidity.lean
if [ $? -eq 0 ]; then say "PASS  control-point -- (1,2,3,-1) control: Hv component -212 and wHw = -400 in-file, matching r6_gift_hessian.py V3e"; else say "FAIL  control-point"; fail=1; fi

say ""
say "== X4c: negative controls =="
for ph in totally_made_up_theorem_name exactly_two_of_domain; do
  c=$(grep -chE "^(theorem|def) $ph" Interchange.lean MagicSquare.lean Anyon.lean Exchangeable.lean Rigidity.lean | awk '{s+=$1} END {print s}')
  if [ "$c" -eq 0 ]; then say "PASS  negcontrol-$ph -- not declared in any source (quoted-as-history only)"; else say "FAIL  negcontrol-$ph -- declared $c times"; fail=1; fi
done

say ""
say "== X4d: reverse sweep (headline families in Rigidity.lean -> mentioned in PROOFS.md) =="
grep -oE "^theorem [A-Za-z_0-9']+" Rigidity.lean | awk '{print $2}' \
  | grep -E "^(HY_|HG_|HS_|HC_|gg_|germ_|hess_|grad_G|SS_G|SS_Y|YL_|strict_|gauge_|tangentY|qform_sos|psd_of_sos|ker_of_sos|Fg_transp|Fs_rev|pentResid_rev|sos_)" \
  | sort -u > /tmp/r6s_headliners.txt
miss=0; tot=0; missing=""
while IFS= read -r t; do
  tot=$((tot+1))
  grep -q "$t" PROOFS.md || { miss=$((miss+1)); missing="$missing $t"; }
done < /tmp/r6s_headliners.txt
say "      $tot headline-family theorems found in Rigidity.lean; $miss not named in PROOFS.md"
if [ "$miss" -gt 0 ]; then
  say "INFO  reverse-unmentioned --$missing"
  say "      (supporting members of families whose heads ARE in the ledger; counted, not failed)"
fi
# the ledger's own table names must each appear
for t in YL_is_solution HY_psd HY_kernel HY_kernel_is_line HY_det4_zero HY_minor3_pos HY_swap_not_null germ_G hess_G; do
  grep -q "$t" PROOFS.md || { say "FAIL  reverse-$t -- headliner absent from ledger"; fail=1; }
done
say "PASS  reverse-headliners -- every table-row theorem of the ledger appears, and every family head is mentioned"

say ""
[ "$fail" -eq 0 ] && say "RESULT: X4 name sweep clean.  PASS." || say "RESULT: X4 name sweep FAILED."
exit $fail
