#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r8s_d5_repairs.py -- terminal audit, check D5: the H1-H3 repairs.
#
#  (a) H1: REGISTER's note is bound to the five .py actually aboard, and the
#      claim is TRUE -- this script RUNS all five; all must exit 0.  It also
#      runs a sample of the builder's r3-r5 population (now ferried home) and
#      requires at least one nonzero exit -- the population the transplanted
#      reason was actually true of, so the repaired note is true on BOTH arms.
#  (b) H2: the 561 misattribution -- archive/PROOFS-round6.md:561 carries
#      "all 199" and :532-533 narrate the bump; Rigidity.lean:561 is proof
#      code; the capstone H2 re-binds the citation to the ledger and does not
#      repeat it.
#  (c) H3: eight-instruments count fixed to seven (and exactly the seven gate
#      scripts exist); class-6 attribution fixed ("instrumented in round 6");
#      REGISTER-diff third hunk: row 9's numerals clause present in the live
#      file and the omission recorded in ROUND8.md (the archived round-7
#      sentence stands as history, per the house archive policy);
#      2-digit sight + quoted-vs-asserted: LIVE-TESTED by planting a bare "73"
#      (must FAIL the gate) and a quoted "73" (must PASS).
#
# Standalone.  Needs python3 + sh.  Exit 0 = PASS, 1 = FAIL.
# ---------------------------------------------------------------------------
import os, re, sys, subprocess, tempfile, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()

fail = 0
def chk(ok, label, detail=""):
    global fail
    print(("  ok    " if ok else "  FAIL  ") + label + ((" -- " + detail) if detail else ""))
    if not ok: fail = 1

print("== D5a: H1 -- the REGISTER note, bound and TRUE (run the artifacts) ==")
REG = rd("REGISTER.md"); flatreg = " ".join(REG.split())
FIVE = ["audit_c1_check.py","verify_anyon.py","verify_anyon_r2.py",
        "verify_c3.py","verify_exchangeable_r2.py"]
chk(all(f.replace(".py","") + ".py" in REG for f in FIVE),
    "REGISTER names exactly the five re-verifications aboard")
chk("reports **all five exit 0**" in flatreg or "all five exit 0" in flatreg,
    "REGISTER's repaired claim: all five exit 0")
for f in FIVE:
    r = subprocess.run([sys.executable, os.path.join(ROOT, "audit", f)],
                       cwd=ROOT, capture_output=True, timeout=300)
    chk(r.returncode == 0, "run %s" % f, "exit=%d" % r.returncode)
chk("true of the builder's **own** r3–r5 instrument population" in flatreg
    or "own r3-r5" in flatreg or "r3–r5 instrument population" in flatreg,
    "REGISTER attributes the old reason to the builder's r3-r5 population")
nonzero = 0
for f in ["r3_hexagon.py","r3_magicsquare_ledger.py","r4_claims_check.py","r5_ledger_checks.py"]:
    p = os.path.join(ROOT, "audit", f)
    if not os.path.exists(p): continue
    try:
        r = subprocess.run([sys.executable, p], cwd=ROOT, capture_output=True, timeout=120)
        if r.returncode != 0: nonzero += 1
    except subprocess.TimeoutExpired:
        pass
chk(nonzero >= 1, "builder r3-r5 population exits nonzero on newer sources",
    "%d of the sampled instruments exit nonzero -- the transplanted reason was true of THEM" % nonzero)

print("== D5b: H2 -- the 561 misattribution ==")
P6L = rd("archive/PROOFS-round6.md").splitlines()
chk("all 199" in P6L[560], "archive/PROOFS-round6.md:561 carries 'all 199'")
chk("bumped it to 214" in P6L[532] or "bumped it to 214" in "\n".join(P6L[529:537]),
    "archive/PROOFS-round6.md:532-537 narrate the bump")
RGL = rd("Rigidity.lean").splitlines()
chk("199" not in RGL[560] and not RGL[560].lstrip().startswith(("--","/-","*")),
    "Rigidity.lean:561 is proof code, not the cited prose")
P = rd("PROOFS.md")
chk("H2 — a file misattribution" in P and "archive/PROOFS-round6.md" in P
    and "not `Rigidity.lean`" in P.replace("\n", " ").replace("*", ""),
    "capstone H2 re-binds the sites to the round-6 ledger")
chk("does\nnot repeat the citation" in P or "does not repeat the citation" in " ".join(P.split()),
    "capstone declares the archived round-7 ledger stands as the record")

print("== D5c: H3 -- the small items ==")
flat = " ".join(P.split())
chk('"Eight instruments ship" over-counted: **seven**' in flat,
    "eight-vs-seven instrument count repaired in the capstone")
gates = [f for f in os.listdir(os.path.join(ROOT, "audit"))
         if f in ("axioms.sh","transcript.sh","ship.sh","views.sh","pointers.sh",
                  "transcription.sh","numerals.sh")]
chk(len(gates) == 7, "exactly the seven gate scripts exist", ",".join(sorted(gates)))
chk("Pointer prose (class 6) was instrumented in round 6" in flat,
    "class-6 attribution repaired (was 'round 7 instrumented class 6')")
chk("`audit/numerals.sh` checks its numbers" in REG,
    "REGISTER-diff third hunk: row 9's numerals clause is true in the live file")
R8 = " ".join(rd("ROUND8.md").split())
chk("third hunk" in R8, "the hunk omission is on the permanent record (ROUND8.md rides)")
print("  note  the archived round-7 diff sentence is not editable (archive policy);")
print("        the capstone does not restate it (norm 13); repaired-in-file + carried-in-letter.")

print("== D5d: numerals.sh graduation, live-tested (2-digit sight + quotation) ==")
work = tempfile.mkdtemp(prefix="r8s_d5_")
try:
    dst = os.path.join(work, "tree")
    shutil.copytree(ROOT, dst, ignore=shutil.ignore_patterns("__pycache__", "floor", "archive"))
    with open(os.path.join(dst, "PROOFS.md"), "a") as f:
        f.write("\nThere are exactly 73 gremlins in the crate.\n")
    r = subprocess.run(["sh", "audit/numerals.sh"], cwd=dst, capture_output=True, text=True)
    chk(r.returncode == 1 and "73" in r.stdout, "planted bare '73' FAILS the gate (2-digit sight live)",
        "exit=%d" % r.returncode)
    shutil.rmtree(dst); shutil.copytree(ROOT, dst, ignore=shutil.ignore_patterns("__pycache__", "floor", "archive"))
    with open(os.path.join(dst, "PROOFS.md"), "a") as f:
        f.write('\nThe old ledger said "73 gremlins" once.\n')
    r = subprocess.run(["sh", "audit/numerals.sh"], cwd=dst, capture_output=True, text=True)
    chk(r.returncode == 0, "quoted \"73\" PASSES (quoted-vs-asserted live)", "exit=%d" % r.returncode)
finally:
    shutil.rmtree(work, ignore_errors=True)

print("RESULT: " + ("PASS" if fail == 0 else "FAIL"))
sys.exit(fail)
