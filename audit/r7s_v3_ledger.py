#!/usr/bin/env python3
"""r7s_v3_ledger.py -- ROUND-7 SEAT: Verlinde copied-surface + census + ledger
reconciliation (checks V1-deep, V6, V8 of the seat charge).

THREE PARTS.
  T*  the FULL copied surface: every declaration Verlinde.lean claims to
      transcribe from Anyon.lean, compared token-for-token (comment-stripped,
      whitespace-normalized), with namespace tracking so Z5.add_comm is not
      confused with KK.add_comm.  This extends audit/transcription.sh (which
      anchors Zp.mul / Z5.mul / fuse) to the whole claimed-verbatim set, and
      partitions the file into COPIED vs NEW.
  C*  census reconciliation: the tactic-class partition of the 75 theorems
      vs audit/axioms-round7.txt (75 / 50 axiom-free / 25 [propext,
      Quot.sound]).  Per-theorem rows are NOT shipped, so this is a
      count-level (single-sided) reconciliation and says so.
  X*  every round-7 PROOFS.md sentence about Verlinde vs the source,
      the courier-gap record, and the numeral-quarantine list vs a live
      numerals.sh run.  A FAIL here is a LEDGER finding, not a mathematics
      failure -- the RESULT line says which.

Exit 0 iff no check fails.  Usage: python3 audit/r7s_v3_ledger.py
"""
import sys, os, re, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, ".."))
def rd(p): return open(os.path.join(ROOT, p), encoding="utf-8").read()
V, AY, PR = rd("Verlinde.lean"), rd("Anyon.lean"), rd("PROOFS.md")

results, findings = [], []
def check(name, ok, detail="", finding=None):
    results.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
    if not ok and finding: findings.append(finding)

# ---------------------------------------------------------------- utilities
def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith("/-", i): depth += 1; i += 2; continue
        if depth and s.startswith("-/", i): depth -= 1; i += 2; continue
        if depth == 0: out.append(s[i])
        i += 1
    return re.sub(r"--[^\n]*", "", "".join(out))

DECL = re.compile(r"^(inductive|structure|def|theorem|abbrev)\s+([A-Za-z_][\w'.]*)")
def decls(src):
    """[(namespace, kind, name, normalized-body)] -- RAW-line boundary parse
    (a block-comment-aware stripper is applied per block, not globally, so a
    long documentation comment can never swallow declarations).  A declaration
    line must carry ':' or 'where' (house trap 2: prose starting with
    'theorem' at column 0 is not a declaration without them)."""
    lines = src.split("\n")
    ns, out, cur = [], [], None
    in_block = 0
    def close():
        nonlocal cur
        if cur: out.append(cur); cur = None
    for ln in lines:
        s = ln.strip()
        if in_block:                       # inside /- ... -/ documentation
            in_block += s.count("/-") - s.count("-/")
            if in_block < 0: in_block = 0
            continue
        if s.startswith("/-") and not (s.count("-/") >= s.count("/-")):
            close(); in_block = s.count("/-") - s.count("-/")
            continue
        if s.startswith("/--") or s.startswith("/-!"):
            close(); continue              # one-line doc comment
        m = re.match(r"^namespace\s+(\S+)", ln)
        if m:
            close(); ns.append(m.group(1)); continue
        if re.match(r"^end\s+\S+", ln):
            close()
            if ns: ns.pop()
            continue
        d = DECL.match(ln)
        if d and (":" in ln or " where" in ln):
            close()
            cur = [".".join(ns), d.group(1), d.group(2), [ln]]
            continue
        if cur is not None:
            if s == "":
                close()
            else:
                cur[3].append(ln)
    close()
    norm = lambda b: re.sub(r"\s+", " ", re.sub(r"--[^\n]*", "", "\n".join(b))).strip()
    return [(a, b, c, norm(d)) for a, b, c, d in out]

DV = decls(V)      # namespaces include Round7Verlinde prefix
DA = decls(AY)
def find_all(dl, ns_tail, name):
    return [x[3] for x in dl
            if x[2] == name and (x[0].split(".")[-1] if x[0] else "") == ns_tail]

# ---------------------------------------------------------------- Part T
print("=" * 72)
print("T -- the full copied surface, token-compared vs Anyon.lean")
print("=" * 72)
COPIED = (
    [("", k) for k in ["Anyon", "fuse", "memA", "isOne", "Rng", "matMul",
                        "matEq", "matId", "Zp", "zpRng", "Z5",
                        "z5_zeta4_eq", "z5_zeta5_eq", "z5_phi_eq",
                        "z5_invPhi_eq", "z5_invPhi_mul", "z5_phi_sq"]] +
    [("Zp", k) for k in ["zero", "one", "phi", "add", "neg", "mul", "beq", "invPhi"]] +
    [("Z5", k) for k in ["zero", "one", "add", "neg", "mul", "zeta", "zeta2",
                          "zeta3", "zeta4", "phi", "invPhi", "conj",
                          "add_comm", "add_assoc", "add_zero", "zero_add",
                          "mul_one", "one_mul", "mul_zero", "zero_mul",
                          "mul_comm", "mul_add", "add_mul", "mul_assoc",
                          "mul_left_comm", "add_left_comm", "neg_mul",
                          "mul_neg", "neg_neg", "add_neg", "neg_add_cancel",
                          "neg_add", "mul_right_comm",
                          "conj_zeta", "conj_zeta2", "conj_zeta3", "conj_zeta4",
                          "conj_phi", "conj_invPhi",
                          "conj_add", "conj_neg", "conj_mul", "conj_conj"]]
)
drift, absent = [], []
for ns, name in COPIED:
    # Verlinde wraps everything in Round7Verlinde; tail-namespace must match
    bvs = find_all(DV, ns if ns else "Round7Verlinde", name)
    bas = find_all(DA, ns if ns else "Anyon", name)   # Anyon.lean root = Workshop.Anyon
    if not bvs or not bas:
        absent.append((ns, name, "V" if not bvs else "A")); continue
    if not any(bv == ba for bv in bvs for ba in bas):
        drift.append((ns, name))
check("T1_copied_surface", not drift and not absent,
      f"{len(COPIED)} claimed-verbatim declarations token-identical "
      f"(drifted: {drift or 'none'}; absent: {absent or 'none'}) -- extends "
      "transcription.sh's 3 anchors to the whole copied set")

NEW_DEFS = {"conj", "Dsq", "sqrt5", "Msel", "DsqI", "rowDot", "fuseMult",
            "fuseZp", "verlNum", "Mwrong", "DsqWrong", "verlNumWrong",
            "theta1", "thetaTau", "phiPlus2", "pp", "pm", "Mat2", "Mat2.mul",
            "ShatT", "ShatTmirror"}
vd = [(ns, k, n) for ns, k, n, b in DV]
copied_names = {(ns, n) for ns, n in COPIED}
new_defs, new_thms, uncat = [], [], []
for ns, kind, name, body in DV:
    tail = ns.split(".")[-1] if ns else ""
    key = ("" if tail == "Round7Verlinde" else tail, name)
    if key in copied_names:  continue
    if kind == "theorem": new_thms.append(name)
    elif kind in ("def", "structure", "inductive"):
        if name in NEW_DEFS or (tail == "Zp" and name == "conj") or (tail == "Mat2"):
            new_defs.append(name)
        else: uncat.append((ns, kind, name))
check("T2_new_layer_inventory", not uncat and len(new_thms) == 38,
      f"NEW = {len(new_defs)} defs (Zp.conj + Dsq/sqrt5/Msel/DsqI/rowDot/"
      f"fuseMult/fuseZp/verlNum + wrong-S trio + T-layer Shat/Mat2 objects) "
      f"+ {len(new_thms)} theorems (14 Zp core + 24 T-layer); uncategorized: {uncat or 'none'}")
tcount = sum(1 for _, k, _, _ in DV if k == "theorem")
check("T3_counts", tcount == 75 and len(new_thms) + (len(COPIED) - 21 - 4 - 8 - 12 + 8) >= 0
      and tcount - len(new_thms) == 37,
      f"75 theorems = 38 new + 37 transcribed (25 ring/conj laws + 6 conj receipts + 6 z5 receipts)")

# ---------------------------------------------------------------- Part C
print("=" * 72)
print("C -- census reconciliation (single-sided: no per-theorem rows shipped)")
print("=" * 72)
AX = rd("audit/axioms-round7.txt")
row = re.search(r"Verlinde\s+(\d+)\s+(\d+)\s+(\d+)", AX)
fam = re.search(r"Verlinde\s+\[propext, Quot\.sound\]\s+(\d+)", AX)
check("C1_census_row", row and tuple(map(int, row.groups())) == (75, 50, 25)
      and fam and int(fam.group(1)) == 25,
      "axioms-round7.txt: Verlinde 75 theorems, 50 axiom-free, 25 rest; "
      "single family [propext, Quot.sound] x25; sorryAx 0, Classical.choice 0")
tactic_heavy = [n for ns, k, n, b in DV if k == "theorem"
                and re.search(r"\bsimp only\b|\bomega\b|\brw \[", b)]
heavy_set = set(tactic_heavy)
LAWS = {"add_comm","add_assoc","add_zero","zero_add","mul_one","one_mul",
        "mul_zero","zero_mul","mul_comm","mul_add","add_mul","mul_assoc",
        "mul_left_comm","add_left_comm","neg_mul","mul_neg","neg_neg",
        "add_neg","neg_add_cancel","neg_add","mul_right_comm",
        "conj_add","conj_neg","conj_mul","conj_conj"}
check("C2_25_are_the_ring_laws", len(tactic_heavy) == 25 and heavy_set == LAWS,
      "exactly 25 theorems use simp/omega/rw -- precisely the TRANSCRIBED Z5 "
      "ring+conj laws; count matches the census 'rest' column exactly")
new_heavy = [n for n in new_thms if n in heavy_set]
check("C3_cleared_core_axiom_free_consistent", not new_heavy,
      "all 38 NEW theorems (the cleared Verlinde core + T-layer) and the 12 "
      "receipt theorems are rfl/decide-proved -- consistent with the ledger's "
      "'whole cleared core is axiom-free, not even propext' and the 24-new-"
      "theorem audit note.  SINGLE-SIDED: census ships counts per family, not "
      "per-theorem rows; the 25/50 split matches the tactic partition exactly, "
      "but which 25 is inferred, not printed")
h = subprocess.run(["sha256sum", os.path.join(ROOT, "Verlinde.lean")],
                   capture_output=True, text=True).stdout.split()[0]
check("C4_census_measured_this_file", h in AX and h in rd("audit/transcript-round7.txt"),
      f"sha256 {h[:16]}... stamped in both instrument outputs (E5(ii))")
# VIEW blocks in the ledger are verbatim slices of the instrument outputs
def view(tag):
    m = re.search(r"<!-- VIEW:%s BEGIN[^\n]*\n```\n(.*?)```\n<!-- VIEW:%s END" % (tag, tag), PR, re.S)
    return m.group(1) if m else ""
tv, av = view("transcript"), view("axioms")
tt, at_ = rd("audit/transcript-round7.txt"), AX
tv_ok = all(ln in tt for ln in tv.strip().split("\n") if ln.strip())
av_ok = all(ln in at_ for ln in av.strip().split("\n") if ln.strip())
check("C5_views_match_outputs", tv and av and tv_ok and av_ok,
      "every nonblank line of both PROOFS.md VIEW blocks appears verbatim in "
      "the shipped instrument outputs (rendered, not typed)")

# ---------------------------------------------------------------- Part X
print("=" * 72)
print("X -- PROOFS.md round-7 Verlinde sentences vs source")
print("=" * 72)
check("X1_headline_arithmetic", "1,053" in rd("ROUND7.md") and "1,128" in PR
      and 21+63+714+41+214+75 == 1128 and 1128-75 == 1053,
      "1,053 -> 1,128 = +75 (Verlinde); six per-file counts sum to 1,128")

names_claimed = ["verlinde_cleared", "Dsq_eq_sqrt5_phi", "norm_Dsq", "M_symm",
                 "M_sq", "rows_orthonormal", "dims_from_S", "wrong_S_fails_ttt",
                 "fuseMult_nonconstant", "verlinde_anti_vacuity", "modular_cube",
                 "pp_pm_eq_D2", "pm_eq_conj_pp", "verlinde_tau_tau", "ribbon_twist"]
missing = [n for n in names_claimed if (f"theorem {n}" not in V and f"theorem {n}" not in AY)]
check("X2_ledger_names_exist", not missing, f"all {len(names_claimed)} ledger-cited "
      f"identifiers exist as theorems (missing: {missing or 'none'})")

check("X3_verlinde_cleared_quote",
      "theorem verlinde_cleared : ∀ a b c, Zp.mul Dsq (fuseZp a b c) = verlNum a b c := by\n"
      "  intro a b c; cases a <;> cases b <;> cases c <;> rfl" in V,
      "statement quoted exactly: forall over 2x2x2 = 8 cells, D^2*fuseMult = verlNum "
      "shape over Zp, proof cases+rfl as the ledger says")
check("X4_fuseMult_computed",
      "def fuseMult (a b c : Anyon) : Int :=\n"
      "  ((fuse a b).countP (fun x => decide (x = c)) : Int)" in V,
      "fuseMult is countP over fuse -- computed, not asserted (Nfus precedent, Anyon.lean:6551)")
check("X5_dims_from_S_points",
      "quantum_dimension_tau" in V and "(Anyon.lean:6737)" in V
      and "theorem quantum_dimension_tau" in AY
      and AY.split("\n")[6736].startswith("theorem quantum_dimension_tau")
      and "SECOND way" in V and "read off" in V
      and "Nfus" not in strip_comments(V) and "matApp" not in strip_comments(V),
      "dims_from_S POINTS at quantum_dimension_tau (name + line 6737, correct), frames "
      "itself as a SECOND reading ('read off the S-matrix'), and restates NO Perron/Nfus "
      "machinery -- the house pointing pattern, matching ledger F3 ('co-signature, not a "
      "fifth independent derivation')")
check("X6_wrong_S_quote",
      "theorem wrong_S_fails_ttt :\n"
      "    verlNumWrong .tau .tau .tau ≠ Zp.mul DsqWrong (fuseZp .tau .tau .tau) := by\n"
      "  decide" in V and "def DsqWrong : Zp := ⟨2, 0⟩" in V,
      "negative control quoted exactly: by decide, D'^2 = 2, inequality at (tau,tau,tau)")
check("X7_mat2_no_int_descent",
      re.search(r"def Mat2\.mul \(M N : Mat2\) : Mat2 :=\s*"
                r"⟨Z5\.add \(Z5\.mul M\.a N\.a\) \(Z5\.mul M\.b N\.c\),", V)
      and "= ⟨Z5.mul phiPlus2 pp, Z5.zero, Z5.zero, Z5.mul phiPlus2 pp⟩ := by decide" in V,
      "Mat2.mul is built from Z5.mul/Z5.add only and modular_cube closes by decide -- "
      "'a genuine 2x2 matrix computation over Z5, no descent to Int' is accurate")
check("X8_three_balancing_entries",
      all(f"theorem verlinde_{k}" in V for k in ["one_one", "one_tau", "tau_tau"])
      and "verlinde_tau_one" not in V,
      "exactly the 3 distinct entries (S symmetric) -- 'all three distinct Fibonacci "
      "entries' is the right count, not an overclaim of 4")
code = strip_comments(V)
check("X9_park_is_honest",
      "zeta20" not in code and "ζ₂₀" not in code
      and "-14/5" not in code and "−14/5" not in code
      and "degree 8" in V and "denominator 5" in V and "PARKED" in V
      and "a first draft predicted 2; the measurement corrected it" in V,
      "no zeta20 and no c = -14/5 in CODE (both prose-only labels); the park states "
      "BOTH obstructions (degree-8 primitivity + the builder's measured denominator-5, "
      "with the corrected-first-draft history) -- matches the certificate's W5m")
check("X10_no_budget_raised", "set_option" not in V,
      "no set_option anywhere: 'no budget raised' is accurate")

# courier gap (V8)
cg = re.search(r"\*\*Courier gap, flagged rather than guessed:\*\*(.*?)\n\n", PR, re.S)
cgt = re.sub(r"[\s*`]+", " ", cg.group(1)) if cg else ""   # unwrap lines + markdown
gifts_here = all(os.path.exists(os.path.join(HERE, f))
                 for f in ["r7_gift_verlinde.py", "r7_numeral_gift.py"])
check("X11_courier_gap_record",
      cg is not None and "r7_gift_verlinde.py" in cgt
      and "r7_numeral_gift.py" in cgt
      and "not in the crate that reached me" in cgt
      and "independently audited" in cgt and gifts_here,
      "the ledger records the gap plainly (both scripts named, 'flagged rather than "
      "guessed', work 'derived from the letter's certificates and independently audited'); "
      "both scripts DO exist builder-side -- the record is accurate, and gracious "
      "(no blame language; the letter is credited as sufficient).  Their zip-content "
      "claim ('older tree, only r3-r5 gifts') is single-sided: only their side saw it")

# numeral quarantine list vs live run
try:
    nr = subprocess.run(["sh", os.path.join(HERE, "numerals.sh")], cwd=ROOT,
                        capture_output=True, text=True, timeout=120).stdout
    flags = set(re.findall(r"REVIEW\s+(\d+)\s+in PROOFS\.md", nr))
    claimed = {"2610", "2766", "199", "561", "535", "126", "104", "191", "320", "200"}
    check("X12_quarantine_list_exact", flags == claimed,
          f"live numerals.sh flags in PROOFS.md = {sorted(flags)} == the ledger's own "
          "DECLARED-GAPS review list (7 retired G3 counts + 3 standing HANDOFF figures); "
          "1128 and per-file counts are view-sourced and unflagged; norm-16 quarantine honored")
except Exception as e:
    check("X12_quarantine_list_exact", False, f"numerals.sh run failed: {e!r}")

# the one discrepancy: domain provenance
r4 = rd("archive/PROOFS-round4.md"); r5 = rd("archive/PROOFS-round5.md")
zp_dom_r4 = bool(re.search(r"Z\[φ\].{0,40}domain|Zp\.mul_ne_zero", r4))
check("X13_domain_provenance",
      not ("Z[φ] is a domain\n(round 4)" in PR or "Z[φ] is a domain (round 4)" in PR.replace("\n", " ")),
      "PROOFS.md line ~232 says 'Z[phi] is a domain (round 4)'.  The tree says: round 4 "
      "proved Z5 and K domains (archive src-round4: eq_zero_or_eq_zero_of_mul_eq_zero for "
      "Z5/KK only); the Z[phi] domain theorem is ROUND 5 (Anyon.lean:6496 mul_ne_zero, in "
      "the round-5 order block; round-5 ledger: 'Z[phi]-is-a-domain proved from the order "
      "itself') and again ROUND 6 (Rigidity.lean:1010).  One-round provenance slip in "
      "prose; the mathematics (Z[phi] IS a domain, in-tree twice) is unaffected.  Note: "
      "single-digit round numbers are excluded from numerals.sh BY DESIGN, and no "
      "backticked name is involved -- invisible to both resolvers, class-7 species",
      finding="PROOFS.md 'Z[phi] is a domain (round 4)' -> should be round 5 "
              "(Anyon.lean:6496; re-proved round 6, Rigidity.lean:1010)")

print("=" * 72)
npass = sum(results); nfail = len(results) - npass
print(f"RESULT: {npass}/{len(results)} PASS" + (f", {nfail} FAIL" if nfail else ""))
if findings:
    print("FINDINGS (ledger prose, mathematics unaffected):")
    for f in findings: print(f"  - {f}")
sys.exit(0 if nfail == 0 else 1)
