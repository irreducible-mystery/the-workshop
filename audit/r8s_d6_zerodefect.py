#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d6_zerodefect.py -- terminal audit, check D6: the zero-defect
# experiment, scored from outside.
#
#  (a) quotes the capstone's exact claim and verifies its internal accounting:
#      mathematics clean; exactly one prose defect; that defect = H1 =
#      round-7-shipped, repaired here; the alarm did not fire.
#  (b) runs the project's own four runnable prose gates in the crate universe
#      (floor/ rides in the crate, so pointers to FINDINGS.md etc. need it) --
#      all four must PASS: the tree is green under its own instruments.
#  (c) FRESH-DEFECT SCAN -- the terminal audit's own findings, mechanically
#      re-checked.  Two fresh round-8 prose defects shipped in the capstone:
#        T1  the terminal gap table's header claims every row EVER carried at
#            its round-8 status, while the round-1 rows closed in round 2
#            (best == 8 game value; best == 5 sharp; Tier 4a/4b) appear
#            nowhere in the section (see r8s_d3_gaptable.py);
#        T2  the instruments section says the six-file list "lived in four
#            instruments" and "a source list can no longer drift between
#            them" -- but audit/axioms.sh still hard-codes the six-file list
#            (two for-loops), the round-6 ledger counted FIVE instruments and
#            the round-7 ledger SIX places; the census's copy can still drift
#            with no alarm.
#      Both are class-7 characterizations (no execution date), invisible to
#      every gate, caught by the audit loop on its scheduled pass -- the
#      register-age law holds (defect younger than the loop; the alarm of a
#      defect OLDER than its adjudicator still never fired).  But the
#      experiment's prose arm ("shipped exactly one") is falsified: the one
#      carried round-7 defect (H1) plus at least two FRESH round-8 defects.
#
# This script FAILS, by design, on (c): that failure IS the audit's verdict.
# Standalone.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import os, re, sys, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()

fail = 0
def chk(ok, label, detail=""):
    global fail
    print(("  ok    " if ok else "  FAIL  ") + label + ((" -- " + detail) if detail else ""))
    if not ok: fail = 1

P = rd("PROOFS.md"); flat = " ".join(P.split())

print("== D6a: the claim, quoted, and its internal accounting ==")
CLAIM = ("So the capstone did **not** ship zero defects on the prose side: it shipped "
         "exactly one, and it landed in precisely the class the prediction named")
print('  CLAIM (PROOFS.md, THE PREDICTION SCORED):')
print('    "...the capstone did not ship zero defects on the prose side: it shipped')
print('     exactly one... in the register that exists to name adjudicators...')
print('     The alarm that would end the law ... did not fire.  On the mathematics')
print('     side, the experiment shipped clean."')
chk(CLAIM in flat, "the exactly-one claim is present verbatim")
chk("On the mathematics side, the experiment shipped clean" in flat,
    "mathematics-clean arm claimed")
chk("H1 — the shipped instance" in P and "THE CROP — round-7 findings" in P,
    "the one defect = H1, attributed to the ROUND-7 ship (honest about the round)")
chk("Corrected: the note is now bound to the artifacts actually aboard" in flat,
    "H1 repaired in round 8 (REGISTER note re-bound)")
chk("did not fire" in flat and "no register has ever shipped a defect past its adjudicator" in flat,
    "alarm accounting: the defect-older-than-adjudicator alarm did not fire")
print("  note  the round-8 pre-ship catches ('three fresh, died pre-ship') live in")
print("        the couriered transcript, not the tree: UNVERIFIABLE here, and the")
print("        capstone makes no tree-side claim about them -- no inconsistency.")

print("== D6b: the tree under its own gates (crate universe) ==")
crate = "/tmp/r8crate" if os.path.isdir("/tmp/r8crate/floor") else ROOT
for gate, args in [("views.sh", ["check"]), ("pointers.sh", []),
                   ("transcription.sh", []), ("numerals.sh", [])]:
    r = subprocess.run(["sh", os.path.join("audit", gate)] + args,
                       cwd=crate, capture_output=True, text=True)
    chk(r.returncode == 0, "gate %s in %s" % (gate, "crate" if crate != ROOT else "tree"),
        "exit=%d" % r.returncode)
print("  note  kernel-side gates (transcript.sh, axioms.sh) need the Lean toolchain,")
print("        absent here; their claims ride the hash-stamped views, which match")
print("        the tree byte-for-byte (views.sh check above).")

print("== D6c: FRESH-DEFECT SCAN (the terminal audit's findings) ==")
# T1 -- gap-table ever-carried overclaim
sec = P[P.index("## THE TERMINAL GAP TABLE"): P.index("## THE INSTRUMENTS — graduated")]
t1_absent = not any(f in sec for f in
                    ["best == 8", "game value", "bestClassical", "best == 5", "Tier 4"])
chk(not ("Every row any round" in sec and t1_absent),
    "T1 gap-table header supported",
    "header claims every row EVER carried at its round-8 status; the round-1 rows "
    "closed in round 2 (best==8 64x64 game value -> bestClassical_eq_eight; best==5 "
    "sharp -> bestSat_eq_five; Tier 4a/4b -> Exchangeable.lean) are absent from both "
    "the table and the Closed-en-route record")
# T2 -- manifest-fold characterization
AX = rd("audit/axioms.sh")
hardcoded = len(re.findall(r"for f in Interchange MagicSquare Anyon Exchangeable Rigidity Verlinde", AX))
claims4 = "lived in four instruments" in flat
claims_nodrift = "can no longer drift between them" in flat
chk(not (claims4 and claims_nodrift and hardcoded >= 1),
    "T2 manifest-fold sentence supported",
    "capstone: six-file list 'lived in four instruments' + 'can no longer drift'; "
    "but audit/axioms.sh still hard-codes the six-file list (%d for-loops), the "
    "round-6 ledger counted FIVE instruments, the round-7 ledger SIX places; the "
    "census copy can still drift from audit/sources.txt with no alarm" % hardcoded)
print()
print("  VERDICT: the mathematics arm ships clean (all D1 statements verified, the")
print("  census reproduces, the gates are green).  The prose arm's 'exactly one'")
print("  is falsified: one carried round-7 defect (H1, repaired) PLUS at least two")
print("  fresh round-8 class-7 defects (T1, T2).  Both land exactly where the law")
print("  says -- characterization prose with no execution date, younger than the")
print("  audit loop that caught them; the true alarm (defect OLDER than its")
print("  adjudicator) still never fired.  The law is served; the zero stands not.")

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
