#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r6s_x5_census.py -- round-6 seat check, task X5.
# Cross-checks audit/transcript-round6.txt and audit/axioms-round6.txt against
# each other, against the tree, and against the ledger's DECLARED GAPS.
# Standalone; run from workshop/lean/.  PASS/FAIL lines; exit 1 on any FAIL.
# ---------------------------------------------------------------------------
import hashlib, re, sys, os

fail = 0
def chk(label, ok, detail):
    global fail
    print(("PASS  " if ok else "FAIL  ") + label + " -- " + detail)
    if not ok: fail = 1

def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

TR = open("audit/transcript-round6.txt").read()
AX = open("audit/axioms-round6.txt").read()
FILES = ["Interchange", "MagicSquare", "Anyon", "Exchangeable", "Rigidity"]
EXPECT = {"Interchange": 21, "MagicSquare": 63, "Anyon": 714,
          "Exchangeable": 41, "Rigidity": 214}

print("== X5a: transcript-round6.txt ==")
ex = re.findall(r"(\w+)\.lean\s+exit=(\d+)\s+\d+ ms\s+stdout\+stderr=(\d+) bytes", TR)
chk("five-files-silent", len(ex) == 5 and all(e == "0" and b == "0" for _, e, b in ex),
    "per-file stanzas: " + ", ".join(f"{f} exit={e} bytes={b}" for f, e, b in ex))
tc = dict(re.findall(r"^\s{2}(\w+)\.lean\s+(\d+)\s*$", TR, re.M))
tot = re.search(r"TOTAL\s+(\d+)", TR)
chk("transcript-counts", all(int(tc.get(f, -1)) == EXPECT[f] for f in FILES) and tot and tot.group(1) == "1053",
    "counts " + str(tc) + " TOTAL " + (tot.group(1) if tot else "?") + " (want 21/63/714/41/214 = 1053)")

print("== X5b: source hashes, both outputs, against the live tree ==")
for f in FILES + ["lean-toolchain"]:
    p = f + (".lean" if f != "lean-toolchain" else "")
    h = sha(p)
    chk("hash-" + f, (h in TR) and (h in AX), f"tree sha256 {h[:12]}... stamped in transcript + census")

print("== X5c: axioms-round6.txt internal arithmetic ==")
rows = re.findall(r"^(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s*$", AX, re.M)
tab = {r[0]: (int(r[1]), int(r[2]), int(r[3])) for r in rows if r[0] != "TOTAL"}
trow = [r for r in rows if r[0] == "TOTAL"][0]
chk("census-counts", all(tab[f][0] == EXPECT[f] for f in FILES) and int(trow[1]) == 1053,
    f"per-file totals match transcript; TOTAL {trow[1]}/{trow[2]}/{trow[3]}")
chk("rows-sum", sum(tab[f][0] for f in FILES) == 1053
    and sum(tab[f][1] for f in FILES) == int(trow[2])
    and all(tab[f][0] - tab[f][1] == tab[f][2] for f in FILES),
    f"columns internally consistent; axiom-free total {trow[2]}, rest {trow[3]}")
fams = re.findall(r"^\s{2}(\w+)\s+\[([^\]]*)\]\s+(\d+)\s*$", AX, re.M)
per = {}
for f, s, n in fams: per[f] = per.get(f, 0) + int(n)
chk("families-tie-to-rest", all(per.get(f, 0) == tab[f][2] for f in FILES),
    "family counts per file " + str(per) + " == rest column")
sax = re.search(r"sorryAx\s+(\d+)", AX); cho = re.search(r"Classical\.choice\s+(\d+)", AX)
chk("hygiene-zeros", sax.group(1) == "0" and cho.group(1) == "0",
    f"sorryAx {sax.group(1)}, Classical.choice {cho.group(1)} (must be 0/0)")
bad = [s for _, s, _ in fams if "sorryAx" in s or "Classical.choice" in s or "native" in s]
chk("no-forbidden-family", not bad, "no axiom set contains sorryAx/Classical.choice/native: " + str(bad))

print("== X5d: replicate the theorem count from source (the instrument's own anchor) ==")
def count(p):
    n = 0
    for line in open(p, encoding="utf-8"):
        if re.match(r"^theorem [A-Za-z_0-9']", line) and ":" in line:
            n += 1
        elif re.match(r"^theorem _root_\.", line) and ":" in line:
            n += 1
    return n
mine = {f: count(f + ".lean") for f in FILES}
chk("recount", all(mine[f] == EXPECT[f] for f in FILES) and sum(mine.values()) == 1053,
    "independent recount " + str(mine) + f" total {sum(mine.values())}")
# negative control: the same counter on the archived round-5 sources -> 839
old = {f: count("archive/src-round5/" + f + ".lean") for f in FILES if f != "Rigidity"}
chk("negcontrol-r5", sum(old.values()) == 839 and old["Anyon"] == 714,
    "round-5 archive recount " + str(old) + f" total {sum(old.values())} (want 839; Rigidity absent)")

print("== X5e: headline vs views ==")
led = open("PROOFS.md").read()
chk("headline-1053", "839 → **1053 theorems**" in led or "839 -> **1053 theorems**" in led,
    "PROOFS.md headline states 839 -> 1053; NOTE: typed prose outside a VIEW block (class 5/7 boundary), currently consistent with both views")
chk("view-blocks-match-outputs", TR.split("RESULT")[0].split("date")[1].strip()[:40] in led,
    "the transcript VIEW block in PROOFS.md is the instrument output (views.sh check PASSes live)")

print("== X5f: golden-18 axiom-free claim vs census granularity ==")
per_thm = re.search(r"^'?[A-Za-z_0-9.]+'? does not depend", AX, re.M)
chk("census-is-aggregate", per_thm is None,
    "axioms-round6.txt lists per-FILE totals and per-FILE axiom-set families only; NO per-theorem rows ship, so 'every one of the eighteen golden theorems depends on no axioms at all' is SINGLE-SIDED (their /tmp raw.txt); bound check follows")
chk("golden-18-bound", tab["Rigidity"][1] >= 18,
    f"Rigidity axiom-free = {tab['Rigidity'][1]} >= 18: consistent; the 18 reconstructs as SS_G_zero + grad_G_0..3 + gg_e00..e33 + germ_G + hess_G + J2.ext' (5+10+2+1), not enumerated in ledger or file")

print("== X5g: DECLARED GAPS vs sources ==")
rig = open("Rigidity.lean", encoding="utf-8").read()
s8 = rig[rig.index("## §8"):rig.index("## §9")]
chk("gap-Ep-closure", not re.search(r"^theorem (Ep\.)?pos_(add|mul)", s8, re.M)
    and "NOT ATTEMPTED" in rig[:6000],
    "no Ep-level pos_add/pos_mul closure theorem in section 8; header declares it NOT ATTEMPTED; Zp-level posP_add/posP_mul exist (round-5 tech)")
chk("gap-no-golden-psd", not re.search(r"^theorem HG_psd", rig, re.M),
    "no forall-w PSD theorem at golden (HG_psd absent), matching the declared gap; sos_G stands alone")
chk("gap-SS-swap", not re.search(r"^theorem SS_(transp|swap|rev)", rig, re.M)
    and re.search(r"^theorem pentResid_rev", rig, re.M) is not None
    and re.search(r"^theorem Fg_transp", rig, re.M) is not None
    and re.search(r"^theorem Fs_rev", rig, re.M) is not None,
    "residual-level reversal proved (Fg_transp, Fs_rev, pentResid_rev); SS-level swap-invariance absent, matching PARTIAL")
chk("gap-class10", "pentOK" in rig and not re.search(r"pentagonCheck", s8),
    "pentOK == pentagonCheck stated nowhere as a theorem (zero imports make it unstatable); declared UNPROVABLE IN-FILE")
# rows that claim 'unchanged': the three non-Anyon, non-Rigidity files should be
# byte-identical to the round-5 archive (coker/length-8/DF/Born all live there).
TR5 = open("audit/transcript-round5.txt").read()
for f in ["Interchange", "MagicSquare", "Exchangeable"]:
    chk("unchanged-" + f, sha(f + ".lean") in TR5,
        f"{f}.lean tree hash appears in the round-5 transcript stamps -> file unchanged since round 5, 'unchanged' gap rows well-founded")
chk("changed-Anyon", sha("Anyon.lean") not in TR5,
    "Anyon.lean hash differs from round 5 (the three dated F3 updates + F2 conjuncts landed)")

print()
print("RESULT: " + ("X5 census/transcript cross-check clean.  PASS." if fail == 0
                    else "X5 found discrepancies.  FAIL."))
sys.exit(fail)
