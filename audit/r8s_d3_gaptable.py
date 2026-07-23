#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d3_gaptable.py -- terminal audit, check D3: the terminal gap table.
#
#  (a) STANDING completeness: every standing (non-closed) row from every prior
#      DECLARED GAPS table appears in the terminal table -- including the three
#      rows round 7 silently dropped (|r|=1/Born algebraic half, SS
#      swap-invariance, pentOK cross-file boundary).
#  (b) status accuracy, checked against the sources: coker PROVED (theorems
#      present, honest Quotient); lambda parked (no zeta20 construction);
#      c = -14/5 comment-only; Ep.pos closure absent and unused; rt_norm_one
#      present; pentResid_rev present with SS-lift absent; Path is length 6;
#      transcription.sh names pentOK an exception it cannot check.
#  (c) EVER-CARRIED completeness: the section's own header claims "Every row
#      any round's DECLARED GAPS table ever carried, at its round-8 status."
#      This check enumerates the ever-carried set and requires each row to be
#      accounted in the terminal table or the Closed-en-route record.
#      >>> This is the check that FAILS: the round-1 rows closed in round 2
#      (best == 8 the 64x64 game value; best == 5 sharp; Tier 4a/4b) appear
#      nowhere in the section.  The standing rows are complete; the header's
#      stronger claim is not supported by the document.
#
# Standalone.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()

fail = 0
def chk(ok, label, detail=""):
    global fail
    print(("  ok    " if ok else "  FAIL  ") + label + ((" -- " + detail) if detail else ""))
    if not ok: fail = 1

P = rd("PROOFS.md")
sec = P[P.index("## THE TERMINAL GAP TABLE"): P.index("## THE INSTRUMENTS — graduated")]

print("== D3a: standing rows all present (incl. the three round-7-dropped) ==")
STANDING = [  # anchor fragment in the terminal table -> which prior table required it
 ("coker(M)", "standing since r1 (PARTIAL r1-r7)"),
 ("algebraic half (Born modulus)", "r1-r6 |r|=1/Born row; DROPPED r7; must be restored"),
 ("swap-invariance", "r6 row; DROPPED r7; must be restored"),
 ("pentOK", "r6 row; DROPPED r7; must be restored"),
 ("length-8 exchangeability", "r2-r7"),
 ("ζ₂₀¹³", "r7 lambda park"),
 ("−14/5", "r7 c label"),
 ("Ep.pos", "r6-r7"),
 ("Diaconis–Freedman", "r2-r7"),
 ("analysis family", "r1 BLOCKED family"),
]
for frag, why in STANDING:
    chk(frag in sec, "terminal row: %s" % frag, why)
chk("dropped by round 7, restored" in sec and sec.count("dropped by round 7, restored") == 3,
    "exactly three rows marked 'dropped by round 7, restored'",
    "count=%d" % sec.count("dropped by round 7, restored"))
P7 = rd("archive/PROOFS-round7.md"); P6 = rd("archive/PROOFS-round6.md")
g7 = P7[P7.index("## DECLARED GAPS"):]
chk("swap-invariance" not in g7 and "pentOK" not in g7 and "Born" not in g7,
    "round-7 table indeed lacks the three (the drop was real)")
chk("swap-invariance" in P6 and "pentOK" in P6 and "Born-rule value 1" in P6,
    "round-6 table indeed carried the three (the restore is faithful)")

print("== D3b: status accuracy vs the sources ==")
MS = rd("MagicSquare.lean"); AN = rd("Anyon.lean"); RG = rd("Rigidity.lean")
VL = rd("Verlinde.lean"); EX = rd("Exchangeable.lean")
for t in ["image_iff_even","imageCount_eq_32","b_not_in_image","toZ2_hom",
          "coker_two_classes","coker_classes_distinct","coker_identifies","coker_separates"]:
    chk(re.search(r"^theorem %s\b" % t, MS, re.M) is not None, "coker PROVED: %s" % t)
chk("Quotient cokerSetoid" in MS, "coker built as an honest Quotient")
chk(re.search(r"^(def|abbrev|noncomputable def)\s+\S*(zeta20|ζ₂₀)", VL, re.M) is None,
    "lambda PARKED: no zeta20 element constructed in Verlinde.lean (comments only)")
c_sites = [L for L in VL.splitlines() if "14/5" in L]
chk(all(("--" in L or L.lstrip().startswith(("*", "the", "numeric", "central", "The"))) for L in c_sites),
    "c = -14/5 lives only in comments/docstrings", "%d sites" % len(c_sites))
flatRG = " ".join(RG.split())
chk("`Ep.pos` is NOT proved closed under addition" in flatRG
    and "No theorem in this file uses them" in flatRG,
    "Ep.pos closure declared NOT proved + unused, at the site (norm 15)")
chk(re.search(r"^theorem rt_norm_one\b", AN, re.M) is not None, "|r|=1 algebraic: rt_norm_one in Anyon")
chk(re.search(r"^theorem pentResid_rev\b", RG, re.M) is not None, "SS swap PARTIAL: pentResid_rev present")
chk(re.search(r"^theorem SS_transp\b|^theorem SS_swap", RG, re.M) is None,
    "SS swap PARTIAL: the lift SS(transp F) = SS(F) indeed absent")
chk("b5 : Bool" in EX and "b7" not in EX, "length-8 NOT ATTEMPTED: Path is six bools")
TR = rd("audit/transcription.sh")
chk("pentOK" in TR and "NOT CHECKED HERE" in TR,
    "pentOK boundary: transcription.sh names it an exception it cannot check")

print("== D3c: the header's EVER-CARRIED claim (this is the finding) ==")
closed = sec[sec.index("**Closed en route**"):]
EVER_CLOSED_EARLY = [
 ("best == 8, the 64x64 game value", ["best", "game value", "bestClassical", "eight_attained", "8/9"]),
 ("best == 5 sharp (max satisfiable contexts)", ["best == 5", "bestSat", "satCount_le_five"]),
 ("Tier 4a / 4b (round-1 row, deferred per Q4)", ["Tier 4", "Tier 4a"]),
]
print("  header claims: 'Every row any round's DECLARED GAPS table ever carried,")
print("  at its round-8 status.'  Rows carried by round 1 and closed in round 2:")
for row, frags in EVER_CLOSED_EARLY:
    hit = any(f in sec for f in frags)
    chk(hit, "accounted: %s" % row,
        "" if hit else "absent from terminal table AND Closed-en-route record "
        "(round-1 DECLARED GAPS carried it; closed r2: bestClassical_eq_eight / "
        "bestSat_eq_five / Exchangeable.lean; capstone never mentions it)")
chk("Every row any round" in sec, "(the overclaiming header sentence is present, verbatim)")

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
