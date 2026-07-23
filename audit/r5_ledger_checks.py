#!/usr/bin/env python3
"""r5_ledger_checks.py -- round-4 audit: shipped outputs as documents, plus the
exact arithmetic the round-4 headline claims rest on (definitions fixed since
round 1; independent reimplementation, not reusing r4_domain_certificates.py).

One PASS/FAIL line per check.  FAIL lines are genuine discrepancies (the
script does not stop; the exit code is the number of failures)."""
import re, os, itertools, glob

L = "/home/claude/workshop/lean"
fails = 0
def ck(name, ok, detail=""):
    global fails
    print(("PASS  " if ok else "FAIL  ") + name + (("  [" + detail + "]") if detail else ""))
    if not ok: fails += 1

rd = lambda p: open(os.path.join(L, p), encoding="utf-8").read()
proofs   = rd("PROOFS.md")
round4   = rd("ROUND4.md")
p3       = rd("archive/PROOFS-round3.md")
axtxt    = rd("audit/axioms-round4.txt")
trtxt    = rd("audit/transcript-round4.txt")
axsh     = rd("audit/axioms.sh")
trsh     = rd("audit/transcript.sh")
shipsh   = rd("audit/ship.sh")

# ---------- 1. round-4 census table: internal arithmetic ----------
rows = dict(re.findall(r"^(Interchange|MagicSquare|Anyon|Exchangeable)\s+(\d+\s+\d+\s+\d+)\s*$", axtxt, re.M))
tab = {k: tuple(map(int, v.split())) for k, v in rows.items()}
ck("census rows: 21/21, 63/16, 565/250, 41/41",
   tab == {"Interchange": (21,21,0), "MagicSquare": (63,16,47),
           "Anyon": (565,250,315), "Exchangeable": (41,41,0)}, str(tab))
tot = re.search(r"^TOTAL\s+(\d+)\s+(\d+)\s+(\d+)", axtxt, re.M).groups()
ck("census totals row 690/328/362 and columns sum", tuple(map(int, tot)) == (690,328,362)
   and sum(t[0] for t in tab.values()) == 690 and sum(t[1] for t in tab.values()) == 328
   and all(t[0]-t[1] == t[2] for t in tab.values()))
sets = re.findall(r"^\s+(Anyon|MagicSquare)\s+(\[[^\]]*\])\s+(\d+)\s*$", axtxt, re.M)
per = {}
for f, s, n in sets: per[f] = per.get(f, 0) + int(n)
ck("occurring sets sum to the rest column per file (Anyon 19+8+288=315, MS 2+45=47)",
   per == {"Anyon": 315, "MagicSquare": 47}, str(per))
ck("sorryAx 0 and Classical.choice 0 in shipped census output",
   re.search(r"sorryAx\s+0", axtxt) is not None and re.search(r"Classical\.choice\s+0", axtxt) is not None)

# ---------- 2. PROOFS.md census block == shipped output ----------
pr_rows = dict(re.findall(r"^(Interchange|MagicSquare|Anyon|Exchangeable)\s+(\d+\s+\d+\s+\d+)\s*$", proofs, re.M))
ck("PROOFS.md census table numerically identical to axioms-round4.txt",
   {k: tuple(map(int, v.split())) for k, v in pr_rows.items()} == tab)
ck("PROOFS.md occurring-sets sentence (288/2, 19/45, 8) matches output table",
   "`[propext, Quot.sound]` 288 in Anyon and 2 in MagicSquare" in proofs
   and "`[propext]` 19 in Anyon and 45 in MagicSquare" in proofs
   and "`[Quot.sound]` alone 8 in Anyon" in proofs
   and dict(((f, s), int(n)) for f, s, n in sets) ==
       {("Anyon","[propext]"):19, ("MagicSquare","[propext, Quot.sound]"):2,
        ("MagicSquare","[propext]"):45, ("Anyon","[Quot.sound]"):8,
        ("Anyon","[propext, Quot.sound]"):288})

# ---------- 3. transcript: PROOFS.md block vs shipped output ----------
def tr_facts(txt):
    h  = re.findall(r"sha256(?:\(olean\))?\s*=?\s*([0-9a-f]{64})", txt)
    ms = re.findall(r"exit=0\s+(\d+)\s*ms", txt)
    return h, ms
h_txt, ms_txt = tr_facts(trtxt)
blk = proofs[proofs.index("### Compile transcript"): proofs.index("| file | round 3 |")]
h_pr  = re.findall(r"sha256\s+([0-9a-f]{64})", blk)
ms_pr = re.findall(r"exit=0\s+(\d+)\s*ms", blk)
ck("4 olean hashes identical between PROOFS.md block and transcript-round4.txt", h_pr == h_txt and len(h_txt) == 4)
ck("4 wall-times identical (1659/51082/102185/18219 ms)", ms_pr == ms_txt == ["1659","51082","102185","18219"])
d_txt = re.search(r"date\s*:\s*(\S+)", trtxt).group(1)
d_pr  = re.search(r"date\s*:\s*(\S+)", blk).group(1)
ck("DATE fields agree between PROOFS.md block and shipped transcript",
   d_txt == d_pr, "txt=%s vs PROOFS=%s -- the known transcription edit" % (d_txt, d_pr))
ck("transcript txt: all four exit=0, stdout+stderr=0 bytes, RESULT PASS",
   trtxt.count("exit=0") == 4 and trtxt.count("stdout+stderr=0 bytes") == 4
   and "RESULT: all files compiled silent (exit 0, zero bytes).  PASS." in trtxt)

# ---------- 4. round-3 ledger cross-checks (unchanged files) ----------
h3 = re.findall(r"sha256\s+([0-9a-f]{64})", p3)[:4]
ck("three unchanged olean hashes bit-identical to round-3 ledger; Anyon's moved",
   h3[0] == h_txt[0] and h3[1] == h_txt[1] and h3[3] == h_txt[3] and h3[2] != h_txt[2],
   "r3 Anyon %s.. vs r4 %s.." % (h3[2][:8], h_txt[2][:8]))
ck("round-3 table rows for unchanged files identical in round-4 census (21/21, 63/16, 41/41)",
   "| `Interchange.lean` | 21 | 21 |" in p3 and "| `MagicSquare.lean` | 63 | 16 |" in p3
   and "| `Exchangeable.lean` | 41 | 41 |" in p3)
ck("theorem growth arithmetic: 245->565 is +320; 370->690 is +320; headline says 370 -> 690",
   565-245 == 320 and 690-370 == 320 and "370 → **690 theorems**" in proofs)
ck("Anyon axiom-set deltas from round 3 (141f/96/6/2 -> 250f/288/8/19) all non-negative and sum to +320",
   (250-141) + (288-96) + (8-6) + (19-2) == 320
   and "| `Anyon.lean` | 245 | 141 | 96 `propext, Quot.sound`; 6 `Quot.sound`; 2 `propext` |" in p3)
ck("Q5 narrative numbers match transcripts: 102185 ms ~ '102 s'; round-3 Anyon 55941 ms ~ '56 s'",
   "102185 ms" in trtxt and "**102 s**" in proofs and "55941 ms" in p3 and "56 s" in proofs)
ck("olean sizes consistent across docs (Anyon 6160504 -> 10836872 B)",
   "olean=10836872 bytes" in trtxt and "10836872" in proofs and "6160504" in p3)

# ---------- 5. shipped hygiene hits vs round-3 sources (unchanged files) ----------
def line(p, n): return open(os.path.join(L, p), encoding="utf-8").read().split("\n")[n-1]
ok = ("Status: PROVED, no `sorry`." in line("Interchange.lean", 35)
  and "no `native_decide`" in line("Interchange.lean", 27)
  and "Theorem A is proved twice" in line("MagicSquare.lean", 21)
  and "`native_decide`.  (An earlier header" in line("MagicSquare.lean", 17)
  and "Self-contained: NO imports." in line("Exchangeable.lean", 31))
ck("transcript hygiene-hit line numbers+text match round-3 sources for the 3 unchanged files", ok)
ck("shipped counts for unchanged files equal local recount (21/63/41)",
   all(x in trtxt for x in ["Interchange.lean      21", "MagicSquare.lean      63", "Exchangeable.lean     41"]))

# ---------- 6. instruments-as-documents ----------
gloss = ["STATEMENT INCLUDED", "toolchain-relative OVER-APPROXIMATION of logical dependence",
         "measures the first thing, not the second"]
r4flat = re.sub(r"\s+", " ", round4)
ck("I2: requested C1 gloss present in axioms.sh header AND in shipped census output",
   all(g in axsh for g in gloss) and all(g in axtxt for g in gloss)
   and "statement included: a toolchain-relative over-approximation of logical dependence" in r4flat)
ck("transcript.sh states the authoritative sorryAx delegation",
   "AUTHORITATIVE check for an unproved gap is not grep" in trsh and "`sorryAx` appears in any `#print axioms` report" in trsh)
ck("D3 CONSISTENCY: axioms.sh comment should not still say 'Anyon.lean section 6' after PROOFS.md D3 says the survivor is MagicSquare.lean:320 and 'Anyon has none'",
   "Anyon.lean section 6" not in axsh,
   "shipped comment says: 'one does, in Anyon.lean section 6'")
l320 = line("MagicSquare.lean", 320)
ck("MagicSquare.lean:320 begins with the PLURAL 'theorems ' -- excluded by the space anchor, so the /:/ guard is inert on the very line both ledgers credit it with",
   l320.startswith("theorems ") and ":" not in l320)
ck("axioms.sh has no failing exit path in its text (no 'exit' after tally) -- alarm is print-only",
   re.search(r"^exit", axsh, re.M) is None)
ck("neither instrument output records SOURCE hashes (census/transcript pair cannot be tied to one source state)",
   "sha256" not in axtxt
   and all(("sha256(olean)" in ln or ".olean sha256" in ln)
           for ln in trtxt.splitlines() if "sha256" in ln))

# ---------- 7. ship.sh REQUIRED bookkeeping ----------
req = re.search(r'REQUIRED="\n(.*?)\n"', shipsh, re.S).group(1).split()
ck("REQUIRED = 15 paths incl. four .lean, toolchain, PROOFS/HANDOFF, 3 scripts, 2 outputs, 3 archived ledgers",
   len(req) == 15 and all(f in req for f in
   ["Anyon.lean","Exchangeable.lean","Interchange.lean","MagicSquare.lean","lean-toolchain",
    "PROOFS.md","HANDOFF.md","audit/axioms.sh","audit/transcript.sh","audit/ship.sh",
    "archive/PROOFS-round1.md","archive/PROOFS-round2.md","archive/PROOFS-round3.md",
    "audit/transcript-round4.txt","audit/axioms-round4.txt"]))
ck("ROUND2/3/4.md are NOT required (3 of the plausible 7 extras; ship.sh stages the whole tree so they ride if present)",
   not any(r in req for r in ["ROUND2.md","ROUND3.md","ROUND4.md"]))
ck("ship.sh prints the crate hash at build time (self-hash rides the courier message, not the artifact)",
   'sha256($OUT) = $(sha256sum "$OUT" | cut -c1-64)' in shipsh and "ferry THIS FILE, not the folder" in shipsh
   and "not recorded here" in proofs)

# ---------- 8. ferry-vs-crate arithmetic ----------
flat9 = ["Anyon.lean","Exchangeable.lean","Interchange.lean","MagicSquare.lean",
         "lean-toolchain","PROOFS.md","HANDOFF.md","ROUND2.md","ROUND3.md"]
ck("round-3 loss: 9 arrived == exactly the flat lean/ contents; crate should have had 13 (9 + 2 scripts + 2 archived ledgers)",
   all(os.path.exists(os.path.join(L, f)) for f in flat9) and 9 + 2 + 2 == 13
   and "nine files" in round4.lower() + proofs.lower())
t0 = os.path.getmtime(os.path.join(L, "PROOFS.md"))
arrivals = [os.path.relpath(p, L) for p in glob.glob(L + "/**/*", recursive=True)
            if os.path.isfile(p) and abs(os.path.getmtime(p) - t0) <= 120
            and not os.path.basename(p).startswith(("r4_claims", "r5_"))]
lean_arrived = [a for a in arrivals if a.endswith(".lean") or a == "lean-toolchain"]
ck("round-4 arrival cluster (mtime) contains NO .lean and no lean-toolchain -- root-level files missing while SUBDIR files arrived, incompatible with the round-3 backslash-collapse mechanism",
   len(lean_arrived) == 0 and any(a.startswith("audit/") for a in arrivals)
   and any(a.startswith("archive/") for a in arrivals), "arrived: " + ", ".join(sorted(arrivals)))

# ---------- 9. the 2bbadfaa anecdote ----------
others = [f for f in ["ROUND4.md","archive/PROOFS-round3.md","audit/axioms-round4.txt",
                      "audit/transcript-round4.txt","HANDOFF.md"] if "2bbadfaa" in rd(f)]
ck("2bbadfaa appears ONLY in PROOFS.md narrative (no shipped receipt; consistent -- distinct from final 5bec0f8b -- but unverifiable)",
   "2bbadfaa" in proofs and not others and not h_txt[2].startswith("2bbadfaa"))
ck("no shipped document carries the mid-session numbers 561 or '298 new theorems'",
   all(re.search(r"\b561\b|\b298\b", d) is None for d in [proofs, round4, axtxt, trtxt]))
ck("norm-10 withdrawal on record: '+4 seconds on a ~90 second build' quoted only to be withdrawn ('no delta should be quoted')",
   "+4 seconds on a ~90 second build" in proofs and "no delta should be quoted" in proofs)
ck("toolchain pin agrees everywhere (leanprover/lean4:v4.32.0)",
   rd("lean-toolchain").strip() == "leanprover/lean4:v4.32.0"
   and "leanprover/lean4:v4.32.0" in trtxt and "leanprover/lean4:v4.32.0" in axtxt)

# ---------- 10. exact arithmetic: the shared algebra (fresh implementation) ----------
def red(c):  # reduce z^4 -> -(1+z+z^2+z^3), z^5 -> 1
    out = [0]*4
    for i, v in enumerate(c):
        e = i % 5
        if e < 4: out[e] += v
        else:
            for k in range(4): out[k] -= v
    return tuple(out)
def zmul(a, b):
    c = [0]*8
    for i in range(4):
        for j in range(4): c[i+j] += a[i]*b[j]
    return red(c)
zadd = lambda a, b: tuple(x+y for x, y in zip(a, b))
zneg = lambda a: tuple(-x for x in a)
zsub = lambda a, b: zadd(a, zneg(b))
one, z = (1,0,0,0), (0,1,0,0)
z2, z3 = zmul(z,z), zmul(zmul(z,z),z)
z4 = zmul(zmul(z,z), zmul(z,z))
phi, invPhi = zneg(zadd(z2,z3)), (-1,0,-1,-1)
ck("phi = (0,0,-1,-1), invPhi = (-1,0,-1,-1), phi*invPhi = 1 (fixed since round 1)",
   phi == (0,0,-1,-1) and zmul(phi, invPhi) == one)
r1, rt, rt2 = z2, zneg(z), zneg(z4)
ck("mirror root rt2 = -z^4 reduces to (1,1,1,1); r1 = rt^2",
   rt2 == (1,1,1,1) and zmul(rt,rt) == r1)
ck("Q_factors base: rt + rt2 = -invPhi and rt*rt2 = 1 (sum/product of the hexagon quadratic)",
   zadd(rt, rt2) == zneg(invPhi) and zmul(rt, rt2) == one)
ck("exactly-two branches distinct: rt != rt2", rt != rt2)

def sig2(a):  # zeta -> zeta^2 componentwise on the power basis, then reduce
    c = [0]*7
    c[0], c[2], c[4], c[6] = a[0], a[1], a[2], a[3]
    return red(c)
basis = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
closed = lambda a: (a[0]-a[2], a[3]-a[2], a[1]-a[2], -a[2])
ck("sigma2 closed form (a0-a2, a3-a2, a1-a2, -a2) exact on the basis (linear => exact everywhere)",
   all(sig2(e) == closed(e) for e in basis))
def conj_sub(a):  # z -> z^4 by substitution, independent derivation
    c = [0]*13
    for i, v in enumerate(a): c[4*i] += v
    return red(c)
ck("sigma2^2 = conj (z->z^4) on the basis; sigma2^4 = id",
   all(sig2(sig2(e)) == conj_sub(e) for e in basis)
   and all(sig2(sig2(sig2(sig2(e)))) == e for e in basis))
box = list(itertools.product((-1,0,1,2), repeat=4))
import random; random.seed(4)
pairs = [(random.choice(box), random.choice(box)) for _ in range(300)]
ck("sigma2 multiplicative on 300 exact pairs", all(sig2(zmul(a,b)) == zmul(sig2(a), sig2(b)) for a,b in pairs))
def norm(a):
    n = zmul(zmul(a, sig2(a)), zmul(sig2(sig2(a)), sig2(sig2(sig2(a)))))
    return n
ck("N lands in Z on 300 exact samples (coords 1-3 vanish)",
   all(norm(random.choice(box))[1:] == (0,0,0) for _ in range(300)))
ck("N multiplicative on 200 exact pairs", all(norm(zmul(a,b))[0] == norm(a)[0]*norm(b)[0] for a,b in pairs[:200]))
bad = [v for v in itertools.product((0,1), repeat=4) if v != (0,0,0,0) and norm(v)[0] % 2 == 0]
ck("2-adic decide: all 15 nonzero parity classes have N odd (16-case certificate)", not bad)

# eleven_splits control
ck("eleven_splits: N(z-3) = Phi5(3) = 121 = 11^2;  N(z-4) = Phi5(4) = 341 = 11*31",
   norm(zsub(z, (3,0,0,0)))[0] == 121 == 11**2
   and norm(zsub(z, (4,0,0,0)))[0] == 341 == 11*31
   and sum(3**k for k in range(5)) == 121 and sum(4**k for k in range(5)) == 341)

# 41-adic package, independently
roots = [x for x in range(1,41) if pow(x,5,41) == 1 and x != 1]
ck("fifth roots of unity mod 41 = {10,16,18,37}; Phi5 vanishes at each",
   sorted(roots) == [10,16,18,37] and all(sum(pow(x,k,41) for k in range(5)) % 41 == 0 for x in roots))
phv = sorted(set((-(pow(x,2,41)+pow(x,3,41))) % 41 for x in roots))
ck("phi evaluates to {7,35}; both satisfy x^2=x+1 mod 41", phv == [7,35]
   and all((v*v - v - 1) % 41 == 0 for v in phv))
ck("both nonsquares (Euler ^20 = -1) AND direct: x^2 = c*y^2 mod 41 has only (0,0)",
   all(pow(v,20,41) == 40 for v in phv)
   and all(not [(x,y) for x in range(41) for y in range(41)
                if (x,y) != (0,0) and (x*x - v*y*y) % 41 == 0] for v in phv))
V = [[pow(x,j,41) for j in range(4)] for x in sorted(roots)]
def det(m):
    if len(m) == 1: return m[0][0]
    return sum((-1)**j * m[0][j] * det([r[:j]+r[j+1:] for r in m[1:]]) for j in range(len(m)))
ck("Vandermonde det of the four places = 24 mod 41, a unit", det(V) % 41 == 24)

# Zp pentagon worlds (phi^2 = phi + 1 on integer pairs)
pmul = lambda a, b: (a[0]*b[0] + a[1]*b[1], a[0]*b[1] + a[1]*b[0] + a[1]*b[1])
padd = lambda a, b: (a[0]+b[0], a[1]+b[1])
iP, mP = (-1,1), (0,-1)          # 1/phi and -phi as Zp pairs
ck("Zp: invPhi=(-1,1) satisfies p^2+p=1; -phi=(0,-1) satisfies it too; both worlds real",
   padd(pmul(iP,iP), iP) == (1,0) and padd(pmul(mP,mP), mP) == (1,0))
ck("pentagon quadratic sum/product: (1/phi) + (-phi) = -1, (1/phi)*(-phi) = -1; roots distinct",
   padd(iP,mP) == (-1,0) and pmul(iP,mP) == (-1,0) and iP != mP)
ck("Yang-Lee tuple (p,q,r,s)=(-phi,-phi,1,phi) meets the three forced relations: s=-p, p^2+p=1, qr=p",
   (0,1) == tuple(-x for x in mP) and padd(pmul(mP,mP), mP) == (1,0) and pmul(mP,(1,0)) == mP)
# KK layer: t*b = 1 with b = (0, invPhi)
kmul = lambda A, B: (zadd(zmul(A[0],B[0]), zmul(phi, zmul(A[1],B[1]))),
                     zadd(zmul(A[0],B[1]), zmul(A[1],B[0])))
t, bK = ((0,0,0,0), one), ((0,0,0,0), invPhi)
ck("KK: t^2 = phi and t*b = 1 (b = invPhi*t)",
   kmul(t,t) == (phi,(0,0,0,0)) and kmul(t,bK) == (one,(0,0,0,0)))

print()
print("r5_ledger_checks: %s" % ("ALL CHECKS PASS" if fails == 0 else "%d FAILURE(S) -- each FAIL line above is a real discrepancy" % fails))
raise SystemExit(fails)
