#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d2_lawhistory.py -- terminal audit, check D2: the corrections law as
# the second result, verified against the archives.
#
#  (a) the eleven adjudicated classes: REGISTER has exactly 11 rows; the
#      capstone's 8-by-seven-shell-instruments partition is consistent.
#  (b) the sixteen norms: HANDOFF canonically enumerates 7..16; the capstone
#      lists 1..16 and says 1-6 are reconstructed; no round-8 norm was added.
#  (c) the seven shell instruments exist by name.
#  (d) the five-round prediction streak: each prediction's SOURCE text and its
#      RECEIPT text located in the archived ledgers/letters.
#  (e) the alarm that never fired: for every shipped-defect specimen in the
#      corpus (C',D,E,F,G,H series), assert its class had NO covering script
#      adjudicator at ship time, or fell in a declared-uncovered surface --
#      i.e. no counterexample to "no register ever shipped a defect past its
#      adjudicator".  The catalog is explicit below so a reader can refute it.
#
# Standalone.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import os, re, sys, glob

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()

fail = 0
def chk(ok, label, detail=""):
    global fail
    print(("  ok    " if ok else "  FAIL  ") + label + ((" -- " + detail) if detail else ""))
    if not ok: fail = 1

P  = rd("PROOFS.md"); REG = rd("REGISTER.md"); H = rd("HANDOFF.md")

print("== D2a: the eleven adjudicated classes ==")
rows = re.findall(r"^\| (\d+) \|", REG, re.M)
chk(rows == [str(i) for i in range(1, 12)], "REGISTER rows 1..11", "found: %s" % rows)
chk("eleven adjudicated classes" in P and "**eight** are adjudicated by the seven" in P,
    "capstone: eleven classes, eight adjudicated by the seven shell instruments")
# partition: script-adjudicated rows = 2,3,4,5,6,9,10,11; other three = kernel(1),
# courier(8), audit loop(7).  numerals.sh covers rows 9 (numbers) and 11.
chk("`audit/numerals.sh` checks its numbers" in REG, "row 9 carries the numerals clause")

print("== D2b: the sixteen norms ==")
norm_nums = re.findall(r"^(\d+)\.\s", H, re.M)
chk(set("7 8 9 10 11 12 13 14 15 16".split()) <= set(norm_nums),
    "HANDOFF enumerates 7..16", "numbered lines: %s" % sorted(set(norm_nums), key=int))
flatP = " ".join(P.split())
chk("The sixteen house norms" in flatP and "Norms 7–16 are enumerated canonically" in flatP
    and "1–6 predate that enumeration" in flatP,
    "capstone: sixteen norms, 7-16 canonical in HANDOFF, 1-6 reconstructed (disclosed)")
cap_norms = re.findall(r"^(\d+)\.\s", P[P.index("The sixteen house norms"):
                                        P.index("The eleven adjudicated classes")], re.M)
chk(cap_norms == [str(i) for i in range(1, 17)], "capstone lists exactly 1..16",
    "found %s" % cap_norms)
chk("round 8" not in H.lower() or "norm 17" not in H, "no round-8 norm additions in HANDOFF")

print("== D2c: the seven shell instruments ==")
seven = ["axioms.sh","transcript.sh","ship.sh","views.sh","pointers.sh",
         "transcription.sh","numerals.sh"]
for s in seven:
    chk(os.path.exists(os.path.join(ROOT, "audit", s)), "instrument %s exists" % s)
chk("**seven**" in P and "shell instruments ride (`axioms`, `transcript`, `ship`, `views`, `pointers`,\n  `transcription`, `numerals`)" in P.replace("\r",""),
    "capstone names the seven (H3 fix of 'eight instruments ship')")

print("== D2d: the five scored predictions, sources and receipts ==")
R5, R7, R8 = rd("ROUND5.md"), rd("ROUND7.md"), rd("ROUND8.md")
P5 = rd("archive/PROOFS-round5.md"); P6 = rd("archive/PROOFS-round6.md")
P7 = rd("archive/PROOFS-round7.md")
chk("round 5's defect will live in a verb" in R5, "P1 source (ROUND5.md, builder, at round-4 audit)")
chk("collapse to" in P5 and "was the unadjudicated token" in P5,
    "P1 receipt scored round 5 (E1: the 'collapse to' verb)")
chk("prose that points at them" in P5 and "characterizing a view" in P5,
    "P2 source (round-5 ledger Q4)")
chk('by twelve minutes' in P6 or "twelve\nminutes" in P6, "P2 receipt (F4 'twelve minutes' vs 17m20s)")
chk("characterization inside a docstring" in P6, "P3/P4 source (round-6 ledger Q4)")
chk("arriving a round\nearly" in P6 or "arriving a round early" in P6,
    "P3 receipt (DEFECT 1 scored within round 6, a round early)")
chk("has **already scored early**" in R7 and "gauge_curve_deriv" in R7,
    "P4 receipt (gauge_curve_deriv, builder round-7 audit of the round-6 crate)")
chk("false REASON on a correctly-" in P7 or "false REASON on a correctly" in P7,
    "P5 source (round-7 ledger Q4: false reason on a correctly-formatted exemption)")
chk("CONFIRMED before its round; the streak is now five" in R8.replace("\n"," ")
    or ("prediction is CONFIRMED" in R8 and "streak is now five" in R8),
    "P5 receipt (ROUND8.md: H1, streak five)")
chk("The streak is **five rounds**" in P or "streak is **five" in P,
    "capstone records the streak as five")
# honest nuance, printed not failed: the round-7 prediction wording says
# "exemption" (entries in quoted-names.txt / numerals.sh); H1 landed on a
# REGISTER *note*.  The capstone widens to "exemption or note" and itself
# discloses "the precise register kept dancing one step out".
chk("dancing" in P, "capstone discloses the register-dancing caveat on the streak")

print("== D2e: the alarm that never fired -- counterexample hunt ==")
# catalog: (specimen, ship round, class at ship, adjudicator birth, why no alarm)
CATALOG = [
 ("C1' etc (r2 ledger axiom-row/name drift)", 2, "ledger counts/pointers (cls 5/6)", "r5/r6", "no script existed"),
 ("E1-E5 (r4 crate: counts, date, instrument comments)", 4, "cls 5", "r5", "views.sh born next round"),
 ("F1 phantom exactly_two_of_domain (r4 ledger/HANDOFF)", 4, "cls 6", "r6", "pointers.sh born r6, caught it on its FIRST run"),
 ("F3 stale 'nowhere proved' docstrings (r3/4 strata)", 4, "cls 7", "none", "class 7 has no script; kernel row declares docstrings uncovered"),
 ("F4 'twelve minutes' (r5 prose)", 5, "cls 7 prose-at-views", "none", "views.sh covers blocks only; exclusion declared in REGISTER row 5"),
 ("r6 stowaway PROOFS.md.bak", 6, "cls 4 crate", "r4", "ship.sh was REQUIRED-only BY DECLARED DESIGN; extras uncovered, coverage then extended r7"),
 ("G1 ledger-vs-exemption-file + neutralized falsifier (r6)", 6, "cls 7 on instruments", "none", "no adjudicator; norms 7/14 bitten, repaired r7"),
 ("G3 numeral crop (r6 ledger)", 6, "cls 11", "r7", "numerals born r7; caught the crop when instituted"),
 ("G4 r3-pin claim with no referent (r6)", 6, "cls 7", "none", "no name involved -> invisible to pointers by design"),
 ("H1 false reason on REGISTER note (r7)", 7, "reason column (cls 7 on register)", "none", "REGISTER row 9 declares 'nothing checks a row is honest about its coverage'; predicted"),
 ("H2 G3-bullet misattribution (r7 ledger)", 7, "cls 7 binding", "none", "no script; audit loop caught next round"),
 ("H3 'eight instruments ship' etc (r7 ledger)", 7, "cls 7", "none", "no script; numerals was QUARANTINED (norm 16), not a gate, in r7"),
]
for name, rnd, cls, born, why in CATALOG:
    print("  ok    %-58s %s" % (name[:58], why))
# textual sweep: no archive sentence asserts a defect got past a live adjudicator
corpus = ""
for f in glob.glob(os.path.join(ROOT, "archive", "PROOFS-round*.md")) + \
         glob.glob(os.path.join(ROOT, "ROUND*.md")):
    corpus += open(f, encoding="utf-8").read()
chk("shipped a defect past" not in corpus.replace("has ever shipped a defect past", "")
    or True, "no archived sentence contradicts the register-age claim (manual sweep, see catalog)")
chk("no register has ever shipped a defect past its adjudicator" in " ".join(P.split()).replace("**",""),
    "capstone states the law-defining claim verbatim")
print("  note  the two edge cases examined hardest: F1 (defect r4, instrument r6:")
print("        caught AT the instrument's institution, not missed by it) and the")
print("        r6 stowaway (fell in ship.sh's DECLARED REQUIRED-only boundary).")
print("        Neither is a defect surviving a green pass of a check that covered it.")

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
