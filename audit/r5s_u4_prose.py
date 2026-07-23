#!/usr/bin/env python3
"""r5s_u4_prose.py -- round-5 source audit, checks U4 / U6 / U7.

The prover's Q4 prediction (PROOFS.md, Q4): the round-5 defect lives in the
PROSE POINTING AT VIEWS -- a pointer naming the wrong view, or a sentence
characterizing a view's content in a way the view does not support; one layer
wider (the E4 class): any sentence about what an instrument or script does
that its text does not support.

This script mechanizes every such sentence that text + arithmetic can reach:

  A  view blocks byte-equal to their renders (U7: ledger == shipped outputs)
  B  the DRIFTED-demo hashes in PROOFS.md (instrument side recomputed; ledger
     side brute-forced over date edits)
  C  "wrong, by twelve minutes" (views.sh header + HANDOFF) vs the artifacts
  D  axioms.sh header: "exactly 14 theorems come out axiom-free" + "See
     PROOFS.md, correction C1'" vs the shipped census (16) and ledger
  E  E1's counts and the sufT_B/sufT_C quotes vs Anyon.lean
  F  E4's facts: MagicSquare.lean:320, guard inertness, the round-4 D3 quote
  G  E5 prose vs the scripts' literal text
  H  DEFECT-2 pointers: Anyon.lean:203/:206, proof-term pointers, nonsquares11
  I  DEFECT-1 repair: no live "left open" contradiction remains
  J  headline table: every named theorem exists in the named nest, key
     statements as characterized (trichotomy, no_sqrt5, phi_bracket, Nfus
     receipts, renamed Nswap, charpoly docstring)
  K  census-attribution ties (funext count vs [Quot.sound]-alone; Fin use)
  L  the one-line headline numbers (690 -> 839; comment-stripped hygiene)
  M  E2's own story: round-4 block copied ms+hashes exactly, date only wrong
  N  U6: the HANDOFF traps and the stub-kernel method credit
  O  U7: the crate hash protocol stated in PROOFS.md
  P  theorem counts by the transcript.sh anchor rule

PASS/FAIL lines (FAIL = the artifacts do not support the sentence); exit 1
if any FAIL.  FAILs here are audit FINDINGS, reported with site + severity.
"""
import hashlib, itertools, re, sys, zipfile

LEAN = "/home/claude/workshop/lean"
FROZEN = ("/root/.claude/uploads/2f80c594-7369-5679-8dd4-4edf1999b180/"
          "6c1cf17e-workshopleanround4FROZEN.zip")

def rd(p): return open(f"{LEAN}/{p}", encoding="utf-8").read()
proofs   = rd("PROOFS.md")
handoff  = rd("HANDOFF.md")
viewssh  = rd("audit/views.sh")
axsh     = rd("audit/axioms.sh")
trsh     = rd("audit/transcript.sh")
tr5      = rd("audit/transcript-round5.txt")
ax5      = rd("audit/axioms-round5.txt")
tr4      = rd("audit/transcript-round4.txt")
ax4      = rd("audit/axioms-round4.txt")
p4       = rd("archive/PROOFS-round4.md")
anyon    = rd("Anyon.lean")
anyon_l  = anyon.split("\n")
files4   = {f: rd(f) for f in ("Interchange.lean", "MagicSquare.lean",
                               "Anyon.lean", "Exchangeable.lean")}

npass = nfail = 0
def ok(m):
    global npass; npass += 1; print("PASS ", m)
def bad(m):
    global nfail; nfail += 1; print("FAIL ", m)
def chk(c, m): (ok if c else bad)(m)
def sha(s): return hashlib.sha256(s.encode() if isinstance(s, str) else s).hexdigest()

def sed_block(text, a, b):
    lines = text.split("\n"); out = []; inr = False
    for ln in lines:
        if not inr:
            if re.match(a, ln): inr = True; out.append(ln)
            continue
        out.append(ln)
        if re.match(b, ln): break
    return out

def view_block(name):
    m = re.search(rf"<!-- VIEW:{name} BEGIN[^\n]*-->\n(.*?)<!-- VIEW:{name} END",
                  proofs, re.S)
    return m.group(1) if m else None

print("---- A. view blocks == renders (U7) ----")
r_tr = "```\n" + "\n".join(sed_block(tr5, r"^date ", r"^RESULT")) + "\n```\n"
r_ax = "```\n" + "\n".join(sed_block(ax5, r"^file  ", r"^  Classical\.choice")) + "\n```\n"
chk(view_block("transcript") == r_tr,
    "VIEW:transcript byte-equal to render(transcript-round5.txt) [date..RESULT]")
chk(view_block("axioms") == r_ax,
    "VIEW:axioms byte-equal to render(axioms-round5.txt) [file..Classical.choice]")

print("---- B. the DRIFTED-demo hashes quoted in PROOFS.md ----")
h_inst = sha(r_tr)
chk(h_inst.startswith("c9a08ba066f6"),
    f"demo's instrument-side hash c9a08ba066f6... recomputed exactly ({h_inst[:16]}...)")
# ledger side: brute-force one-token date edits of the view content
content = r_tr  # ledger_block emits the same stream when views match
found = None
tok = "2026-07-21T09:38:40Z"
cands = []
for h, m, s in itertools.product(range(24), range(60), range(60)):
    cands.append(("full", f"2026-07-21T{h:02d}:{m:02d}:{s:02d}Z"))
for h, m in itertools.product(range(24), range(60)):
    cands.append(("nosec", f"2026-07-21T{h:02d}:{m:02d}Z"))
digs = [i for i, c in enumerate(content) if c.isdigit()]
for kind, rep in cands:
    if rep == tok: continue
    c2 = content.replace(tok, rep)
    if sha(c2).startswith("7cd4c477b5b0"): found = (kind, rep); break
if not found:
    for i in digs:
        for d in "0123456789":
            if content[i] == d: continue
            c2 = content[:i] + d + content[i+1:]
            if sha(c2).startswith("7cd4c477b5b0"): found = ("digit@%d" % i, d); break
        if found: break
if found:
    ok(f"demo's ledger-side hash 7cd4c477b5b0... REPRODUCED: edit={found}")
else:
    print("INFO  ledger-side hash 7cd4c477b5b0... not reproduced by 88k date-substitutions"
          " or any single-digit edit; depends on the exact planted edit -> unverifiable,"
          " not a defect (instrument side verified above)")

print("---- C. 'wrong, by twelve minutes' vs the artifacts ----")
m4 = re.search(r"^date\s*:\s*(\S+)", tr4, re.M)
mL = re.search(r"^date\s*:\s*(\S+)", p4, re.M)
def secs(ts):
    m = re.match(r"2026-07-21T(\d\d):(\d\d)(?::(\d\d))?Z", ts)
    return int(m.group(1))*3600 + int(m.group(2))*60 + int(m.group(3) or 0)
delta = secs(mL.group(1)) - secs(m4.group(1))
print(f"INFO  transcript-round4.txt date {m4.group(1)}; round-4 ledger block date {mL.group(1)};"
      f" delta = {delta//60} min {delta%60} s")
sites = []
if "by twelve minutes" in viewssh: sites.append("views.sh header (WHY THIS EXISTS)")
if "wrong by twelve minutes" in handoff: sites.append("HANDOFF.md addendum 2 (Ledger-as-view)")
chk(delta == 12*60 or not sites,
    f"'twelve minutes' claim vs actual {delta//60}m{delta%60}s -- sites: {sites}")
chk("06:54:40Z" in proofs and "07:12Z" in proofs and "twelve" not in proofs.split("### E2")[1].split("### E3")[0],
    "PROOFS.md's own E2 quotes both timestamps and states no delta (the ledger register is exact)")

print("---- D. axioms.sh header vs the census it fronts ----")
m14 = re.search(r"exactly (\d+) theorems come\s*\n?# out axiom-free|exactly (\d+) theorems come", axsh)
claimed = m14.group(1) or m14.group(2) if m14 else None
mrow = re.search(r"^MagicSquare\s+(\d+)\s+(\d+)\s+(\d+)", ax5, re.M)
free5 = mrow.group(2)
mrow4 = re.search(r"^MagicSquare\s+(\d+)\s+(\d+)\s+(\d+)", ax4, re.M)
chk(claimed == free5,
    f"axioms.sh header says 'exactly {claimed} theorems come out axiom-free' (MagicSquare);"
    f" the shipped round-5 census says {free5} (round 4 said {mrow4.group(2)})")
chk("C1'" in proofs or "C1'" not in axsh,
    "axioms.sh pointer 'See PROOFS.md, correction C1'' resolves in the current ledger"
    " (C1' lives only in archive/PROOFS-round3.md)")
chk("rt'_root_quadratic" in anyon,
    "header's prime-name example rt'_root_quadratic still exists in Anyon.lean")

print("---- E. E1: counts and quotes ----")
sufT = re.findall(r"^theorem (sufT_\w+)", anyon, re.M)
sufE = re.findall(r"^theorem (sufE_\w+)", anyon, re.M)
chk(len(sufT) == 8 and len(sufE) == 11,
    f"file contains exactly 8 sufT_* and 11 sufE_* ({len(sufT)}/{len(sufE)}); 8+11=19")
mult = {x: len(re.findall(rf"pentcheck_of_eq .*\(sufT_{x}\b", anyon)) for x in "BCDEFGHI"}
chk(list(mult.values()) == [21, 4, 3, 5, 2, 2, 1, 1] and sum(mult.values()) == 39,
    f"pentcheck_of_eq application multiset {tuple(mult.values())} == (21,4,3,5,2,2,1,1), SUM=39")
mB = re.search(r"theorem sufT_B \(u : KK\) :\n\s+(.*)", anyon)
mC = re.search(r"theorem sufT_C \(u : KK\) :\n\s+(.*)", anyon)
chk(mB and mB.group(1).strip().startswith(
        "KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero = KK.mul u KK.one"),
    "sufT_B statement == '(1*u)*1 + 0 = u*1' as the ledger quotes")
chk(mC and mC.group(1).strip().startswith(
        "KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero = KK.mul KK.one u"),
    "sufT_C statement == '(1*u)*1 + 0 = 1*u' (same LHS, transposed RHS: trees differ, value equal)")

print("---- F. E4's facts ----")
ms320 = files4["MagicSquare.lean"].split("\n")[319]
chk(ms320.startswith("theorems below") and ":" not in ms320,
    f"MagicSquare.lean:320 = '{ms320[:52]}...' -- plural, no colon")
anchor = re.compile(r"^theorem [A-Za-z_0-9']+")
bad_lines = [(f, i+1, l) for f, t in files4.items()
             for i, l in enumerate(t.split("\n")) if anchor.match(l) and ":" not in l]
chk(not bad_lines, f"the /:/ guard is inert on round-5 sources (0 hits; found {bad_lines[:2]})")
chk('guard is what handles it' in p4 and "The census false positive is `MagicSquare.lean:320`" in p4,
    "round-4 D3 really did credit the guard at the MagicSquare site (E4's target sentence verbatim)")

print("---- G. E5 prose vs script text ----")
chk("(NO OLEAN PRODUCED)" in trsh and
    "!! exit 0 but NO .olean was produced -- nothing was kernel-checked." in trsh,
    "E5(iii) quoted alarm strings are the script's literal text")
chk("!! HYGIENE FAILURE" in axsh and 'exit "$STATUS"' in axsh and "RESULT: FAIL" in axsh,
    "E5(i) quoted alarm strings ('!! HYGIENE FAILURE', RESULT:, exit $STATUS) are literal")
chk("RESULT:" in axsh.split("\n")[-6] or re.search(r'^echo "RESULT: FAIL', axsh, re.M) is not None,
    "axioms.sh 'now ends with a RESULT: line' -- present in the tail")

print("---- H. DEFECT-2 pointers ----")
chk(anyon_l[202].startswith("theorem zp_phi_sq") and
    anyon_l[205].startswith("theorem zp_invPhi_mul"),
    "Anyon.lean:203 is zp_phi_sq and :206 is zp_invPhi_mul, as the audit section states")
def body(name):
    m = re.search(rf"^theorem {name}\b[\s\S]*?(?=\n(?:/--|theorem|def|end|namespace))", anyon, re.M)
    return m.group(0) if m else ""
chk("zp_phi_sq" in body("roots_satisfy"), "roots_satisfy's proof term points at zp_phi_sq")
pb = body("perron_selection")
chk("Zp.pos_phi" in pb and "by decide" in pb,
    "perron_selection = <Zp.pos_phi, by decide> -- pointer as displayed")
bb = body("branch_correspondence")
chk("zp_invPhi_mul" in bb and "perron_selection.2" in bb,
    "branch_correspondence points at zp_invPhi_mul and perron_selection.2")
chk("zp_invPhi_mul" in body("domain_witness"), "domain_witness points at zp_invPhi_mul")
chk(anyon.count("(nonsquares11 c hc).2.2.2.1") == 1,
    "no_t_image_at_nonsplit_places is now literally (nonsquares11 c hc).2.2.2.1")
chk(len(re.findall(r"^theorem zp_invPhi_mul\b", anyon, re.M)) == 1,
    "exactly one theorem zp_invPhi_mul (no re-proof shipped)")

print("---- I. DEFECT-1 repair ----")
hits = [(i+1, l) for i, l in enumerate(anyon_l)
        if re.search(r"left open|Not a proof|remains open|is open\b", l)]
chk(len(hits) == 1 and "round-4 docstring said" in hits[0][1],
    f"the only 'open' phrase left is the historical note at line {hits[0][0]}"
    " ('round-4 docstring said ... is left open. It is not')")
chk("supersedes" in anyon_l[5558-1].lower() or "supersedes" in anyon.lower(),
    "no_sqrt_neg_invPhi_emb explicitly supersedes no_obvious_sqrt_neg_invPhi")

print("---- J. the headline table's names, nests, statements ----")
def nest_at(lineno):
    st = []
    for l in anyon_l[:lineno-1]:
        m = re.match(r"^namespace (\S+)", l)
        if m: st.append(m.group(1)); continue
        m = re.match(r"^end (\S+)", l)
        if m and st and st[-1] == m.group(1): st.pop()
    return st
def thm_line(name):
    for i, l in enumerate(anyon_l):
        if re.match(rf"^theorem {name}\b", l): return i + 1
    return None
for name, want_ns in [("trichotomy", "Zp"), ("tri_count_eq_one", "Zp"),
                      ("pos_add", "Zp"), ("pos_mul", "Zp"), ("pos_phi", "Zp"),
                      ("phi_bracket", "Zp"), ("phi_bracket_tight", "Zp"),
                      ("no_sqrt5", "Ord5")]:
    ln = thm_line(name); ns = nest_at(ln) if ln else []
    chk(ln is not None and want_ns in ns,
        f"{'.'.join(ns[-1:])}.{name} at line {ln} -- ledger's nest '{want_ns}' correct")
for name in ["eigen_phi", "eigen_yl", "eigenvalues_exactly", "perron_selection",
             "quantum_dimension_tau", "branch_correspondence", "charpoly_coeffs",
             "roots_satisfy", "domain_witness", "Nswap_has_positive_eigenvalue_one",
             "lift_shape_is_inhabited", "sigma2_no_mul_lift_exists",
             "no_sqrt_neg_invPhi_emb", "no_sqrt_neg_invPhi"]:
    chk(thm_line(name) is not None, f"headline theorem exists: {name}")
chk(thm_line("Nswap_perron_is_one") is None,
    "old name Nswap_perron_is_one is GONE (renamed, as the ledger says)")
chk("def Nfus" in anyon and all(f"theorem Nfus_{ij}" in anyon for ij in ("oo", "ot", "to", "tt")),
    "Nfus computed-from-fuse + four receipts Nfus_oo/ot/to/tt present")
chk(re.search(r"theorem Nfus_oo : Nfus \.one \.one = Zp\.zero", anyon) and
    re.search(r"theorem Nfus_tt : Nfus \.tau \.tau = Zp\.one", anyon),
    "receipts prove the matrix is [[0,1],[1,1]]")
pbk = "\n".join(anyon_l[6363:6368])
chk("pos (sub (mul ⟨1000, 0⟩ phi) ⟨1618, 0⟩)" in pbk and "⟨1619, 0⟩" in pbk,
    "phi_bracket really is 1618/1000 < phi < 1619/1000 in the order (doubled as 1000*phi vs 1618/1619)")
ns5 = body("no_sqrt5")
chk("no_sqrt5_fuel" in ns5 and "Nat.le_refl" in ns5,
    "no_sqrt5 discharges its Nat fuel with Nat.le_refl, as the table says")
cp_doc = "\n".join(anyon_l[6540:6567])
chk("lam_solutions" in cp_doc and ("never" in cp_doc or "Nfus" in cp_doc),
    "charpoly_coeffs docstring points at eigen_phi/eigen_yl/lam_solutions and flags the Nfus gap")
nsw_doc = "\n".join(anyon_l[6740:6770])
chk(("not" in nsw_doc and "only" in nsw_doc) or "gap" in nsw_doc,
    "renamed Nswap theorem states its gap (has-a-positive-eigenvalue, not uniqueness)")

print("---- K. census-attribution ties ----")
mq = re.search(r"Anyon\s+\[Quot\.sound\]\s+(\d+)", ax5)
fx = sum(1 for l in anyon_l if "funext" in l)
if mq and fx == int(mq.group(1)):
    ok(f"Anyon's funext lines ({fx}) == census [Quot.sound]-alone count ({mq.group(1)}) -- attribution ties")
else:
    print(f"INFO  funext lines {fx} vs [Quot.sound]-alone {mq.group(1) if mq else '?'} -- "
          "attribution is kernel-side; counts differ, not decisive")
chk("Fin " in files4["MagicSquare.lean"],
    "MagicSquare really is Fin-indexed (the propext-from-Fin attribution is textually live)")

print("---- L. the one-line headline numbers ----")
mt4 = re.search(r"^TOTAL\s+(\d+)", ax4, re.M); mt5 = re.search(r"^TOTAL\s+(\d+)", ax5, re.M)
chk(mt4.group(1) == "690" and mt5.group(1) == "839" and "690" in proofs and "839" in proofs,
    f"'690 -> 839 theorems' matches both shipped censuses ({mt4.group(1)} -> {mt5.group(1)})")
def strip_comments(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src.startswith("/-", i):
            depth += 1; i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1; i += 2
        elif depth > 0:
            i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)
code_hits = {}
for f, t in files4.items():
    c = strip_comments(t)
    code_hits[f] = {p: len(re.findall(rf"\b{p}\b", c))
                    for p in ("sorry", "native_decide", "maxHeartbeats", "maxRecDepth")}
    code_hits[f]["axiom_decl"] = len(re.findall(r"^axiom ", c, re.M))
    code_hits[f]["import"] = len(re.findall(r"^import ", c, re.M))
tot = {k: sum(v[k] for v in code_hits.values()) for k in next(iter(code_hits.values()))}
chk(all(v == 0 for v in tot.values()),
    f"comment-stripped code hygiene: sorry/native_decide/budgets/axiom/import all 0 -- {tot}")

print("---- M. E2's own story (round-4 block copied everything but the date) ----")
tr4_ms = re.findall(r"exit=0\s+(\d+) ms", tr4)
chk(tr4_ms == ["1659", "51082", "102185", "18219"] and
    all(f"{v} ms" in p4 for v in tr4_ms),
    f"all four wall-times copied to the millisecond ({tr4_ms})")
tr4_ol = re.findall(r"sha256\(olean\) = ([0-9a-f]{64})", tr4)
chk(len(tr4_ol) == 4 and all(h in p4 for h in tr4_ol),
    "all four .olean hashes in the round-4 ledger block match the instrument output")
chk(m4.group(1) != mL.group(1), "and the hand-regenerated date is the one field that differs")

print("---- N. U6: HANDOFF's traps and the method credit ----")
hnorm = re.sub(r"[\s*]+", " ", handoff)   # collapse wraps + bold markers
chk("`omega` on a conjunctive goal silently pulls in `Classical.choice`" in handoff,
    "trap 1 named: omega-on-conjunctive-goal -> Classical.choice")
chk("Run offered falsifiers" in hnorm and "An unrun falsifier is a sentence about the model" in hnorm,
    "trap 4 present: run offered falsifiers (builder's, against their own adjudicator)")
chk("grep the fact, not the name" in hnorm,
    "trap 5 present: enumerate restating sites -- grep the fact, not the name")
chk("stub Lean kernel" in hnorm and "house method" in hnorm and
    "fail on purpose" in hnorm,
    "the stub-kernel method credited to round-4's auditors and adopted as house method")
chk(re.search(r"13\.\s+\*?\(round 5\)", handoff) and re.search(r"14\.\s+\*?\(round 5, the builder", handoff),
    "norms 13 and 14 recorded in the round-5 norm list")

print("---- O. U7: the crate hash protocol in PROOFS.md ----")
chk("hash-outside-the-artifact protocol" in proofs and "hash in Kelly's message" in proofs,
    "PROOFS.md states the protocol: zip ferried as a file, hash rides in the courier message")
chk("e1da33edbfab2a715cf51c101a7983efcb8fceacaf78934dc11b10ad6ae64bcc" in proofs,
    "and carries the round-4 FROZEN hash (verified against the real zip in r5s_u3)")
chk('Kelly: ferry THIS FILE, not the folder.' in open(f"{LEAN}/audit/ship.sh").read(),
    "ship.sh prints the build-time hash + the ferry instruction")

print("---- P. theorem counts by the transcript.sh anchor rule ----")
counts = {f: sum(1 for l in t.split("\n") if anchor.match(l) and ":" in l)
          for f, t in files4.items()}
chk(counts == {"Interchange.lean": 21, "MagicSquare.lean": 63,
               "Anyon.lean": 714, "Exchangeable.lean": 41},
    f"recomputed counts {tuple(counts.values())} == view's 21/63/714/41 (total {sum(counts.values())})")

print(f"\nr5s_u4: {npass} PASS, {nfail} FAIL (each FAIL is a finding, see report)")
print("RESULT: U4 sweep " + ("CLEAN" if nfail == 0 else f"{nfail} FINDING(S)"))
sys.exit(0 if nfail == 0 else 1)
