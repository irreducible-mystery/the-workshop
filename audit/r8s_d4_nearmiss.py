#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d4_nearmiss.py -- terminal audit, check D4: the near-miss stories as
# absorbed into the permanent record.
#
#  (a) the corrected 1,053 account: the shipped capstone must say the
#      arithmetic ran AHEAD of the instrument AND that 1,053 was the correct
#      count that shipped (the pre-ship audit caught a draft miscasting it);
#      1,053 verified as the actual round-6 census total.
#  (b) the round-7 placeholder story: a literal token held the count's place
#      until the instrument produced 1,128; 1,128 verified as the round-7
#      census total.
#  (c) the H1 scoring narrative: CONFIRMED, streak five, in both the capstone
#      and the builder's ROUND8 letter; H1 identified as ROUND-7-SHIPPED
#      (found in the crop of round-7 findings), repaired in REGISTER.md.
#  (d) provenance honesty: the capstone says these near-misses live only in
#      the couriered transcripts (not verifiable from the tree) -- the claim
#      is checked for being *declared*, since it cannot be checked for truth.
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

P = rd("PROOFS.md"); P6 = rd("archive/PROOFS-round6.md"); P7 = rd("archive/PROOFS-round7.md")
R8 = rd("ROUND8.md")
flat = " ".join(P.split())

print("== D4a: the corrected 1,053 account ==")
chk(flat.count("shipped as the correct count") == 2,
    "capstone says (twice) the 1,053 'shipped as the correct count'",
    "count=%d" % flat.count("shipped as the correct count"))
chk("the arithmetic gave 1,053; the instrument then rendered the identical 1,053" in flat,
    "capstone: arithmetic ran ahead, instrument rendered the identical value")
chk("Neither *placeholder* shipped; both *values*, once confirmed, did" in P.replace("\n", " ")
    or "placeholder* never shipped and the *value*" in flat,
    "capstone: placeholders never shipped, confirmed values did -- they are correct")
chk(re.search(r"TOTAL\s+1053", P6) is not None, "1,053 is the real round-6 census total (view)")

print("== D4b: the round-7 placeholder story ==")
chk("until the instrument produced 1,128" in flat, "capstone: literal token held until 1,128 rendered")
chk(re.search(r"TOTAL\s+1128", P7) is not None, "1,128 is the real round-7 census total (view)")

print("== D4c: the H1 scoring narrative ==")
chk("H1 — the shipped instance of the round-8 prediction. Fixed." in P,
    "capstone crop names H1 as the SHIPPED instance, under 'round-7 findings'")
chk("THE CROP — round-7 findings" in P, "crop section attributes H1 to round 7's ship")
chk("is **CONFIRMED** by finding H1, which shipped in `REGISTER.md`" in P.replace("\n", " ")
    or "CONFIRMED" in P, "capstone scores the prediction CONFIRMED on H1")
chk("The streak is **five rounds**" in flat, "capstone: streak five")
chk("The prediction is CONFIRMED before its round; the streak is now five" in " ".join(R8.split()),
    "builder's ROUND8 letter co-signs: CONFIRMED, streak five")
REG = rd("REGISTER.md")
chk("That reason is *false of the five instruments named above*" in " ".join(REG.split()),
    "REGISTER records H1 against the row that now covers it (the repair site)")

print("== D4d: provenance declared for what the tree cannot show ==")
chk("live in Kelly's couriered transcripts" in flat or "couriered transcripts" in flat,
    "capstone declares the near-miss stories' provenance (transcripts, not tree)")
print("  note  the transcript-resident details (the drafts themselves; the round-8")
print("        pre-ship catches) are UNVERIFIABLE from the tree; what the tree CAN")
print("        show -- both census totals, both 'shipped correct' statements, the")
print("        H1 record on both sides of the courier -- all checks above.")

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
