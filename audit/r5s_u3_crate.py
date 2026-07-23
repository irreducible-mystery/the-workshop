#!/usr/bin/env python3
"""r5s_u3_crate.py -- round-5 source audit, check U3: ship.sh vs the ferried crate.

Reconciles:
  1. ship.sh's REQUIRED list gained the round-5 entries (views.sh, both
     round-5 instrument outputs, archive/PROOFS-round4.md);
  2. the actual ferried round-5 zip (26 entries; all three uploaded copies
     byte-identical) against REQUIRED: nothing required is missing; the
     extras are enumerated; the builder letters ROUND4.md/ROUND5.md are or
     are not aboard;
  3. every crate member is byte-identical to the working tree;
  4. the frozen round-4 crate against PROOFS.md's ferry paragraph (hash,
     size, entry count, .lean line counts, toolchain).

Standalone.  PASS/FAIL lines; exit 1 if any FAIL.
"""
import hashlib, io, os, re, sys, zipfile

LEAN = "/home/claude/workshop/lean"
UP = "/root/.claude/uploads/2f80c594-7369-5679-8dd4-4edf1999b180"
R5 = [f"{UP}/{n}" for n in ("1bfd7e6a-workshopleanround5.zip",
                            "651426e8-workshopleanround5.zip",
                            "6e06b773-workshopleanround5.zip")]
FROZEN = f"{UP}/6c1cf17e-workshopleanround4FROZEN.zip"

npass = nfail = 0
def ok(m):
    global npass; npass += 1; print("PASS ", m)
def bad(m):
    global nfail; nfail += 1; print("FAIL ", m)
def sha(b): return hashlib.sha256(b).hexdigest()

# -- 1. REQUIRED list -------------------------------------------------------
ship = open(f"{LEAN}/audit/ship.sh").read()
m = re.search(r'REQUIRED="\n(.*?)"', ship, re.S)
required = m.group(1).split()
print(f"REQUIRED list in ship.sh: {len(required)} entries")
for want in ("audit/views.sh", "audit/transcript-round5.txt",
             "audit/axioms-round5.txt", "archive/PROOFS-round4.md"):
    (ok if want in required else bad)(f"REQUIRED gained round-5 entry: {want}")
if 'ROUND="${1:-4}"' in ship:
    print('INFO  ship.sh default round is still 4 (ROUND="${1:-4}"); round-5 build needs `sh audit/ship.sh 5` -- cosmetic')

# -- 2. the ferried round-5 zip --------------------------------------------
h = [sha(open(p, "rb").read()) for p in R5]
(ok if len(set(h)) == 1 else bad)(f"all three uploaded round-5 zips byte-identical, sha256={h[0][:16]}...")
zf = zipfile.ZipFile(R5[0])
names = sorted(n for n in zf.namelist() if not n.endswith("/"))
(ok if len(names) == 26 else bad)(f"crate manifest has {len(names)} entries (expected 26)")

missing = [r for r in required if r not in names]
extras = [n for n in names if n not in required]
(ok if not missing else bad)(f"required-but-missing from crate: {missing if missing else 'NONE'}")
print(f"INFO  beyond REQUIRED ({len(extras)} extras): {', '.join(extras)}")
exp_extras = {"ROUND2.md", "ROUND3.md", "audit/audit_c1_check.py",
              "audit/verify_anyon.py", "audit/verify_anyon_r2.py",
              "audit/verify_c3.py", "audit/verify_exchangeable_r2.py"}
(ok if set(extras) == exp_extras else bad)(
    "extras are exactly the two old letters + five round-1/2 verify scripts")
for letter in ("ROUND4.md", "ROUND5.md"):
    present = letter in names
    print(f"INFO  builder letter {letter}: {'IN crate' if present else 'NOT in crate'}")

# -- 3. crate members vs working tree --------------------------------------
stale = []
for n in names:
    p = os.path.join(LEAN, n)
    if not os.path.exists(p):
        stale.append(n + " (absent from tree)")
    elif sha(zf.read(n)) != sha(open(p, "rb").read()):
        stale.append(n)
(ok if not stale else bad)(f"all 26 crate members byte-identical to the working tree"
                           + ("" if not stale else f" -- STALE: {stale}"))

# -- 4. the frozen round-4 crate vs PROOFS.md's ferry paragraph -------------
proofs = open(f"{LEAN}/PROOFS.md").read()
fb = open(FROZEN, "rb").read()
(ok if sha(fb) == "e1da33edbfab2a715cf51c101a7983efcb8fceacaf78934dc11b10ad6ae64bcc"
 and "e1da33edbfab2a715cf51c101a7983efcb8fceacaf78934dc11b10ad6ae64bcc" in proofs
 else bad)("frozen round-4 zip sha256 e1da33ed... matches the hash printed in PROOFS.md")
(ok if len(fb) == 191924 and "191,924 bytes" in proofs else bad)(
    f"frozen zip is {len(fb)} bytes; PROOFS.md says 191,924")
zf4 = zipfile.ZipFile(io.BytesIO(fb))
n4 = sorted(n for n in zf4.namelist() if not n.endswith("/"))
(ok if len(n4) == 22 and "22 entries" in proofs else bad)(
    f"frozen zip has {len(n4)} entries; PROOFS.md says 22")
counts = {f: zf4.read(f).decode().count("\n") for f in
          ("Anyon.lean", "MagicSquare.lean", "Interchange.lean", "Exchangeable.lean")}
want = {"Anyon.lean": 5239, "MagicSquare.lean": 1049,
        "Interchange.lean": 413, "Exchangeable.lean": 548}
(ok if counts == want else bad)(
    f"frozen .lean line counts {tuple(counts.values())} == ledger's 5239/1049/413/548")
tc = zf4.read("lean-toolchain")
(ok if tc == b"leanprover/lean4:v4.32.0" and len(tc) == 24 else bad)(
    "frozen lean-toolchain reads leanprover/lean4:v4.32.0 (24 bytes, no newline) as the ledger says")
same = all(zf4.read(f) == open(os.path.join(LEAN, "archive/src-round4", f), "rb").read()
           for f in counts)
(ok if same else bad)("frozen crate's four .lean byte-identical to archive/src-round4/ "
                      "(the round-4 sources audited this round are the ferried ones)")

print(f"\nr5s_u3: {npass} PASS, {nfail} FAIL")
print("RESULT: U3 " + ("PASS" if nfail == 0 else "FAIL"))
sys.exit(0 if nfail == 0 else 1)
