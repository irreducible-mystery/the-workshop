#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_z5_census.py -- ROUND-8 TERMINAL AUDIT, seat Z, check R5.
#
# THE CENSUS, THREE WAYS, AND THE STAMPS:
#   (1) 1,150 = 21+85+714+41+214+75 from the transcript table
#       (audit/transcript-round8.txt);
#   (2) the same six numbers and total from the axiom census
#       (audit/axioms-round8.txt), plus 503 axiom-free, 0 sorryAx,
#       0 Classical.choice, and the axiom-sets sub-table summing exactly
#       to the per-file "rest" column;
#   (3) an INDEPENDENT RECOUNT here, applying the project's census rule
#       (line starts "theorem <name>" and carries a ":") to the six .lean
#       sources -- run twice, once on the tree and once on the crate.
#   (4) the six source SHA-256s + lean-toolchain stamped in BOTH round-8
#       outputs match the actual files in BOTH tree and crate; the two
#       outputs ride byte-identical in tree and crate; the toolchain
#       stamp equals the lean-toolchain file's content.
#   (5) the from-crate recompile table is RECORDED: six per-file rows,
#       exit=0, stdout+stderr=0 bytes, .olean hash present.  SINGLE-SIDED:
#       no Lean toolchain exists on this side, so the kernel reading
#       cannot be re-run here -- this check verifies the record, and says
#       so rather than claiming more.
#   (6) context pin: the archived round-7 MagicSquare counts 63 under the
#       same rule (the coker section grew it 63 -> 85, +22).
#
# Standalone: python3 + hashlib.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import hashlib
import re
import sys

L = "/home/claude/workshop/lean"
C = "/tmp/r8crate"
ORDER = ["Interchange", "MagicSquare", "Anyon", "Exchangeable", "Rigidity", "Verlinde"]
CLAIM = {"Interchange": 21, "MagicSquare": 85, "Anyon": 714,
         "Exchangeable": 41, "Rigidity": 214, "Verlinde": 75}
CLAIM_FREE = {"Interchange": 21, "MagicSquare": 25, "Anyon": 307,
              "Exchangeable": 41, "Rigidity": 59, "Verlinde": 50}

fail = []
def ok(label, cond, detail=""):
    print(f"  {'ok   ' if cond else 'FAIL '} {label}" + (f"  {detail}" if detail else ""))
    if not cond:
        fail.append(label)

def sha256(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()

def read(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read()

print("=" * 62)
print(" R5 -- CENSUS THREE WAYS, HASH STAMPS, RECOMPILE RECORD")
print("=" * 62)

# --- (1) transcript table ----------------------------------------------------
tr = read(f"{L}/audit/transcript-round8.txt")
sec = tr.split("theorem counts")[1]
tr_counts = {}
for name in ORDER:
    m = re.search(rf"^\s*{name}\.lean\s+(\d+)\s*$", sec, re.M)
    tr_counts[name] = int(m.group(1)) if m else -1
m = re.search(r"^\s*TOTAL\s+(\d+)\s*$", sec, re.M)
tr_total = int(m.group(1)) if m else -1
print("\n--- way 1: the transcript table ---")
row = " + ".join(str(tr_counts[n]) for n in ORDER)
ok("transcript per-file", tr_counts == CLAIM, row)
ok("transcript TOTAL = 1150", tr_total == 1150, f"TOTAL={tr_total}")

# --- (2) axiom census table --------------------------------------------------
ax = read(f"{L}/audit/axioms-round8.txt")
ax_counts, ax_free, ax_rest = {}, {}, {}
for name in ORDER:
    m = re.search(rf"^{name}\s+(\d+)\s+(\d+)\s+(\d+)\s*$", ax, re.M)
    if m:
        ax_counts[name], ax_free[name], ax_rest[name] = map(int, m.groups())
m = re.search(r"^TOTAL\s+(\d+)\s+(\d+)\s+(\d+)\s*$", ax, re.M)
ax_total, ax_free_total, ax_rest_total = (map(int, m.groups()) if m else (-1, -1, -1))
ax_total, ax_free_total, ax_rest_total = int(ax_total), int(ax_free_total), int(ax_rest_total)
print("\n--- way 2: the axiom census ---")
ok("census per-file theorems", ax_counts == CLAIM,
   " + ".join(str(ax_counts.get(n, -1)) for n in ORDER))
ok("census TOTAL = 1150", ax_total == 1150, f"TOTAL={ax_total}")
ok("census axiom-free = 503", ax_free_total == 503, f"free={ax_free_total}")
ok("census per-file axiom-free", ax_free == CLAIM_FREE,
   " + ".join(str(ax_free.get(n, -1)) for n in ORDER))
ok("rows internally consistent (free + rest = theorems, totals add)",
   all(ax_free[n] + ax_rest[n] == ax_counts[n] for n in ORDER)
   and ax_free_total + ax_rest_total == ax_total
   and sum(ax_counts.values()) == ax_total
   and sum(ax_free.values()) == ax_free_total)
# axiom-sets sub-table must sum, per file, to the "rest" column
sets = {}
for m in re.finditer(r"^\s{2}(\w+)\s+(\[[^\]]*\])\s+(\d+)\s*$", ax, re.M):
    sets[m.group(1)] = sets.get(m.group(1), 0) + int(m.group(3))
ok("axiom-sets sub-table sums to per-file rest",
   all(sets.get(n, 0) == ax_rest[n] for n in ORDER),
   "; ".join(f"{n}:{sets.get(n,0)}={ax_rest[n]}" for n in ORDER if ax_rest[n]))
m_s = re.search(r"sorryAx\s+(\d+)", ax)
m_c = re.search(r"Classical\.choice\s+(\d+)", ax)
ok("sorryAx 0", m_s and m_s.group(1) == "0")
ok("Classical.choice 0", m_c and m_c.group(1) == "0")
ok("no Classical.choice in any occurring axiom set",
   "Classical.choice" not in "".join(re.findall(r"\[[^\]]*\]", ax)))

# --- (3) independent recount, tree and crate ---------------------------------
CENSUS = re.compile(r"^theorem [A-Za-z_0-9']+")
def recount(root):
    got = {}
    for name in ORDER:
        n = 0
        with open(f"{root}/{name}.lean", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if CENSUS.match(line) and ":" in line:
                    n += 1
        got[name] = n
    return got

print("\n--- way 3: independent recount (census rule re-applied here) ---")
for root, tag in ((L, "tree "), (C, "crate")):
    got = recount(root)
    row = " + ".join(str(got[n]) for n in ORDER)
    ok(f"recount {tag} per-file matches claim", got == CLAIM, row)
    ok(f"recount {tag} TOTAL = 1150", sum(got.values()) == 1150,
       f"TOTAL={sum(got.values())}")

# --- (4) hash stamps ---------------------------------------------------------
print("\n--- stamps: six sources + toolchain, in both outputs, both universes ---")
tr_c = read(f"{C}/audit/transcript-round8.txt")
ax_c = read(f"{C}/audit/axioms-round8.txt")
ok("transcript-round8.txt byte-identical tree/crate", tr == tr_c)
ok("axioms-round8.txt byte-identical tree/crate", ax == ax_c)
allstamp = True
for name in ORDER + ["lean-toolchain"]:
    fn = f"{name}.lean" if name in ORDER else name
    h_tree, h_crate = sha256(f"{L}/{fn}"), sha256(f"{C}/{fn}")
    hit_tr, hit_ax = h_tree in tr, h_tree in ax
    good = (h_tree == h_crate) and hit_tr and hit_ax
    allstamp &= good
    print(f"    {'ok  ' if good else 'FAIL'} {fn:<18} tree==crate:{h_tree == h_crate}"
          f"  in-transcript:{hit_tr}  in-census:{hit_ax}  {h_tree[:12]}...")
ok("all seven hashes stamped in both outputs and matching both universes", allstamp)
tc = read(f"{L}/lean-toolchain").strip()
ok("toolchain stamp matches lean-toolchain file", tc == "leanprover/lean4:v4.32.0"
   and f"toolchain   : {tc}" in tr and f"toolchain: {tc}" in ax, tc)

# --- (5) the from-crate recompile table (single-sided) -----------------------
print("\n--- the recompile table, as recorded (single-sided) ---")
rows = re.findall(r"^(\w+)\.lean\s+exit=(\d+)\s+(\d+) ms\s+stdout\+stderr=(\d+) bytes\s+olean=(\d+) bytes",
                  tr, re.M)
names = [r[0] for r in rows]
ok("six per-file compile rows recorded", sorted(names) == sorted(ORDER),
   ",".join(names))
ok("every row exit=0 and 0 output bytes",
   all(r[1] == "0" and r[3] == "0" for r in rows))
ok("every row carries a sha256(olean)",
   len(re.findall(r"sha256\(olean\) = [0-9a-f]{64}", tr)) == 6)
ok("RESULT line: all files compiled silent, PASS",
   "RESULT: all files compiled silent (exit 0, zero bytes).  PASS." in tr)
print("    NOTE  single-sided: no Lean toolchain on this side; the kernel")
print("          reading is the prover's record, hash-bound to these exact")
print("          sources (stamps above), not re-executed here.")

# --- (6) context pin: 63 -> 85 -----------------------------------------------
print("\n--- context pin: the coker growth ---")
n7 = 0
with open(f"{L}/archive/src-round7/MagicSquare.lean", encoding="utf-8") as fh:
    for line in fh:
        if CENSUS.match(line) and ":" in line:
            n7 += 1
ok("archived round-7 MagicSquare counts 63 (85 = 63 + 22 coker theorems)",
   n7 == 63, f"round-7 count={n7}")

print()
if not fail:
    print("RESULT: 1,150 reproduced three ways (21+85+714+41+214+75), 503")
    print("        axiom-free, 0 sorryAx, 0 Classical.choice; all seven hash")
    print("        stamps verified in both outputs against both universes;")
    print("        recompile table recorded (single-sided, noted).  PASS.")
    sys.exit(0)
print(f"RESULT: FAIL -- {len(fail)} check(s): {fail}")
sys.exit(1)
