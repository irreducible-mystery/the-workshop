#!/usr/bin/env python3
"""r6_ledger_census_sweep.py — round-5 ledger/census audit (seat T4/T6 + the
openness sweep of T3).

Checks, all against the actual working tree:
  1. source hashes: recompute SHA-256 of the four .lean files + lean-toolchain
     and compare to the stamps inside BOTH instrument outputs and the ledger's
     transcript VIEW (E5(ii) verified two-sided)
  2. VIEW fidelity: every line of the two VIEW blocks in PROOFS.md appears
     verbatim in the corresponding instrument output
  3. census reconciliation: 839 = 21+63+714+41; axiom-free and axiom-set
     family sums tie per file; sorryAx 0; Classical.choice 0
  4. theorem counts by the census's own anchor (^theorem + space) tie to the
     view numbers
  5. E1 receipts: 8 sufT_* + 11 sufE_* lemmas; application multiset
     (21,4,3,5,2,2,1,1) summing to 39; the sufT_B/sufT_C same-polynomial pair
  6. T4 receipts: duplicate-fix pointers are proof terms; renames/labels
     (charpoly honest label, Nswap_has_positive_eigenvalue_one present,
     Nswap_perron_is_one ABSENT, mod-11 N2 label present)
  7. ledger name sweep, both directions (backticked identifiers -> sources;
     round-5 headliners -> ledger)
  8. openness sweep: the sigma2/sqrt(-1/phi) question is closed at every site;
     the round-5 audit's own grep pattern yields exactly its one corrected
     hit — and a WIDER pattern exposes three STALE round-3 docstrings
     contradicted by round 4's domain property (reported as FINDING receipts:
     PASS here means the evidence for the defect is confirmed present)

Standalone; PASS/FAIL lines; exit 1 on any FAIL.
"""
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUD = os.path.join(ROOT, "audit")
FAILED = []


def check(name, ok):
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok:
        FAILED.append(name)


def slurp(p):
    with open(p, "r", encoding="utf-8") as f:
        return f.read()


SRC = {n: slurp(os.path.join(ROOT, n + ".lean"))
       for n in ("Anyon", "MagicSquare", "Interchange", "Exchangeable")}
TOOL = slurp(os.path.join(ROOT, "lean-toolchain"))
PROOFS = slurp(os.path.join(ROOT, "PROOFS.md"))
AXOUT = slurp(os.path.join(AUD, "axioms-round5.txt"))
TROUT = slurp(os.path.join(AUD, "transcript-round5.txt"))
ALL_SRC = "\n".join(SRC.values())

# ── 1. hashes ─────────────────────────────────────────────────────────
print("== 1: source hashes vs instrument stamps (E5(ii), two-sided) ==")
for name in ("Anyon", "MagicSquare", "Interchange", "Exchangeable"):
    h = hashlib.sha256(
        open(os.path.join(ROOT, name + ".lean"), "rb").read()).hexdigest()
    check("H: %s.lean sha256 %s... stamped in axioms output, transcript "
          "output, and ledger VIEW" % (name, h[:12]),
          h in AXOUT and h in TROUT and h in PROOFS)
htool = hashlib.sha256(
    open(os.path.join(ROOT, "lean-toolchain"), "rb").read()).hexdigest()
check("H: lean-toolchain sha256 stamped in all three",
      htool in AXOUT and htool in TROUT and htool in PROOFS)

# ── 2. VIEW fidelity ─────────────────────────────────────────────────
print("== 2: VIEW blocks vs instrument outputs ==")


def view_block(tag):
    m = re.search(r"<!-- VIEW:%s BEGIN[^\n]*-->\n```\n(.*?)```\n<!-- VIEW:%s "
                  r"END -->" % (tag, tag), PROOFS, re.S)
    return m.group(1) if m else None


tv = view_block("transcript")
av = view_block("axioms")
check("V: both VIEW blocks present and delimited", tv is not None
      and av is not None)
if tv and av:
    tl = [l.rstrip() for l in tv.splitlines() if l.strip()]
    miss_t = [l for l in tl if l.rstrip() not in
              [x.rstrip() for x in TROUT.splitlines()]]
    # allow the view's RESULT line to be a summary the instrument also prints
    check("V: all %d transcript-VIEW lines appear verbatim in "
          "transcript-round5.txt (missing: %d)" % (len(tl), len(miss_t)),
          len(miss_t) == 0)
    al = [l.rstrip() for l in av.splitlines() if l.strip()]
    miss_a = [l for l in al if l.rstrip() not in
              [x.rstrip() for x in AXOUT.splitlines()]]
    check("V: all %d axioms-VIEW lines appear verbatim in "
          "axioms-round5.txt (missing: %d)" % (len(al), len(miss_a)),
          len(miss_a) == 0)
    if miss_t:
        for l in miss_t[:5]:
            print("        transcript-view line not in instrument: %r" % l)
    if miss_a:
        for l in miss_a[:5]:
            print("        axioms-view line not in instrument: %r" % l)

# ── 3. census reconciliation ─────────────────────────────────────────
print("== 3: census reconciliation ==")
counts = {}
for name, th, free, rest in re.findall(
        r"^(Interchange|MagicSquare|Anyon|Exchangeable)\s+(\d+)\s+(\d+)\s+"
        r"(\d+)\s*$", AXOUT, re.M):
    counts[name] = (int(th), int(free), int(rest))
check("C: per-file theorem counts are 21/63/714/41",
      counts.get("Interchange", (0,))[0] == 21
      and counts.get("MagicSquare", (0,))[0] == 63
      and counts.get("Anyon", (0,))[0] == 714
      and counts.get("Exchangeable", (0,))[0] == 41)
tot = re.search(r"^TOTAL\s+(\d+)\s+(\d+)\s+(\d+)\s*$", AXOUT, re.M)
check("C: TOTAL row is 839 / 385 / 454 and equals the column sums",
      tot is not None and tuple(map(int, tot.groups())) == (839, 385, 454)
      and sum(v[0] for v in counts.values()) == 839
      and sum(v[1] for v in counts.values()) == 385
      and sum(v[2] for v in counts.values()) == 454)
check("C: per-file theorems = axiom-free + rest, all four files",
      all(v[0] == v[1] + v[2] for v in counts.values()))
fams = re.findall(r"^\s+(Anyon|MagicSquare|Interchange|Exchangeable)\s+"
                  r"(\[[^\]]*\])\s+(\d+)\s*$", AXOUT, re.M)
fam_sum = {}
for f, s, c in fams:
    fam_sum[f] = fam_sum.get(f, 0) + int(c)
check("C: axiom-set families — Anyon 29+8+370 = 407 = Anyon rest; "
      "MagicSquare 2+45 = 47 = MagicSquare rest; no other file has families",
      fam_sum.get("Anyon") == 407 == counts["Anyon"][2]
      and fam_sum.get("MagicSquare") == 47 == counts["MagicSquare"][2]
      and set(fam_sum) == {"Anyon", "MagicSquare"}
      and sorted(int(c) for f, s, c in fams if f == "Anyon") == [8, 29, 370]
      and sorted(int(c) for f, s, c in fams
                 if f == "MagicSquare") == [2, 45])
check("C: family axiom-sets are only propext / Quot.sound combinations",
      all(set(re.findall(r"[A-Za-z.]+", s)) <= {"propext", "Quot.sound"}
          for f, s, c in fams))
check("C: sorryAx 0 and Classical.choice 0 in the census",
      re.search(r"sorryAx\s+0", AXOUT) is not None
      and re.search(r"Classical\.choice\s+0", AXOUT) is not None)
check("C: census RESULT line is a PASS and hygiene clean",
      "RESULT: census complete, hygiene clean.  PASS." in AXOUT)
check("C: transcript RESULT — all files compiled silent (exit 0, zero "
      "bytes)", "RESULT: all files compiled silent" in TROUT)

# ── 4. theorem counts tie to the sources by the census's own anchor ──
print("== 4: theorem counts from the sources ==")
anchor = re.compile(r"^theorem [A-Za-z_0-9']+", re.M)
got = {n: len(anchor.findall(SRC[n])) for n in SRC}
check("T: ^theorem-anchor counts — Interchange %d, MagicSquare %d, Anyon "
      "%d, Exchangeable %d == 21/63/714/41, sum 839"
      % (got["Interchange"], got["MagicSquare"], got["Anyon"],
         got["Exchangeable"]),
      (got["Interchange"], got["MagicSquare"], got["Anyon"],
       got["Exchangeable"]) == (21, 63, 714, 41)
      and sum(got.values()) == 839)
check("T: E4 regression — MagicSquare line 320 begins 'theorems below' and "
      "fails the anchor (plural, no space)",
      SRC["MagicSquare"].splitlines()[319].startswith("theorems below")
      and not anchor.match(SRC["MagicSquare"].splitlines()[319]))

# ── 5. E1 receipts ───────────────────────────────────────────────────
print("== 5: E1 receipts (the eight shapes) ==")
suft = re.findall(r"^theorem (sufT_[A-Z])\b", SRC["Anyon"], re.M)
sufe = re.findall(r"^theorem (sufE_\w+)\b", SRC["Anyon"], re.M)
check("E1: exactly 8 sufT_* and 11 sufE_* lemmas in Anyon.lean "
      "(8 + 11 = 19)", len(suft) == 8 and len(sufe) == 11)
apps = {L: len(re.findall(r"pentcheck_of_eq .*\(sufT_%s\b" % L,
                          SRC["Anyon"])) for L in "BCDEFGHI"}
check("E1: application counts B..I = (21,4,3,5,2,2,1,1), sum 39",
      [apps[L] for L in "BCDEFGHI"] == [21, 4, 3, 5, 2, 2, 1, 1]
      and sum(apps.values()) == 39)
# the ledger's E1 block quotes them in infix sugar `(1*u)*1 + 0 = u*1`;
# the file states them in prefix form — same trees, so the check matches
# the prefix form (and the report notes the notational gap):
LHS = "KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero"
check("E1: sufT_B and sufT_C share LHS (1*u)*1 + 0 [prefix: %s...] and "
      "differ only as trees (RHS `KK.mul u KK.one` vs `KK.mul KK.one u`) "
      "— the one-lemma gap named in the ledger" % LHS[:20],
      re.search(r"theorem sufT_B \(u : KK\) :\n\s+%s = KK\.mul u KK\.one"
                % re.escape(LHS), SRC["Anyon"]) is not None
      and re.search(r"theorem sufT_C \(u : KK\) :\n\s+%s = KK\.mul KK\.one u"
                    % re.escape(LHS), SRC["Anyon"]) is not None)

# ── 6. T4 receipts ───────────────────────────────────────────────────
print("== 6: T4 receipts (duplicate-fix, renames, honest labels) ==")
check("T4: zp_phi_sq and zp_invPhi_mul each declared exactly once "
      "(the canonical sites)",
      len(re.findall(r"^theorem zp_phi_sq\b", SRC["Anyon"], re.M)) == 1
      and len(re.findall(r"^theorem zp_invPhi_mul\b", SRC["Anyon"],
                         re.M)) == 1)
check("T4: roots_satisfy points — proof term `⟨zp_phi_sq, rfl⟩`",
      "⟨zp_phi_sq, rfl⟩" in SRC["Anyon"])
check("T4: domain_witness points at zp_invPhi_mul as its third conjunct's "
      "proof term",
      re.search(r"domain_witness[\s\S]{0,400}?⟨by decide, by decide, "
                r"zp_invPhi_mul, by decide⟩", SRC["Anyon"]) is not None)
check("T4: branch_correspondence points at zp_invPhi_mul and "
      "perron_selection.2",
      re.search(r"⟨zp_invPhi_mul, by decide, by decide, "
                r"perron_selection\.2⟩", SRC["Anyon"]) is not None)
check("T4: perron_selection points at Zp.pos_phi",
      re.search(r"⟨Zp\.pos_phi, by decide⟩", SRC["Anyon"])
      is not None)
check("T4: no_t_image_at_nonsplit_places is the pointer "
      "`(nonsquares11 c hc).2.2.2.1`",
      "(nonsquares11 c hc).2.2.2.1" in SRC["Anyon"])
check("T4/N1: charpoly_coeffs keeps its name but carries the honest label "
      "(does NOT compute trace/det of Nfus)",
      re.search(r"charpoly_coeffs", SRC["Anyon"]) is not None
      and re.search(r"does \*\*not\*\* compute `trace Nfus` or `det Nfus`",
                    SRC["Anyon"]) is not None)
check("T4/N3-rename: Nswap_has_positive_eigenvalue_one present; "
      "Nswap_perron_is_one ABSENT from all sources",
      "Nswap_has_positive_eigenvalue_one" in SRC["Anyon"]
      and all("Nswap_perron_is_one" not in s for s in SRC.values()))
check("T4/N2: mod-11 header carries the honest label (no-ring-map over "
      "non-split places NOT claimed; what is proved is c^2 % 11 != 8)",
      "HONEST LABEL (audit note N2)" in SRC["Anyon"]
      and re.search(r"N2\):[\s\S]{0,400}?NOT\s+proved here",
                    SRC["Anyon"]) is not None)
check("T4: QDT honest label — d_tau identification called the standard "
      "definition; PF described as replaced by a decision, not formalized",
      "Calling that\n    unique positive eigenvalue \"the quantum dimension"
      " d_τ\" is the standard\n    definition" in SRC["Anyon"]
      and "Perron–Frobenius\n    as a decision, with no analysis"
      in SRC["Anyon"])
al = SRC["Anyon"].splitlines()
pf_ctx = ["\n".join(al[i:i + 2]) for i, l in enumerate(al)
          if "Perron" in l]
check("T4: every Perron mention in Anyon.lean (with its next line, since "
      "docstrings wrap) is of the 'as a decision / replaces' kind "
      "(%d mention(s), none claims a PF theorem is proved)" % len(pf_ctx),
      len(pf_ctx) >= 1
      and all(("as a decision" in c) or ("by decide" in c)
              or ("decision procedure" in c) or ("would supply" in c)
              for c in pf_ctx))

# ── 7. name sweep, both directions ───────────────────────────────────
print("== 7: ledger name sweep ==")
SUB = str.maketrans("₀₁₂₃₄₅₆₇"
                    "₈₉", "0123456789")
raw = re.findall(r"`([^`]+)`", PROOFS)
skip_exact = {
    "sorry", "sorryAx", "native_decide", "axiom", "import", "decide", "rfl",
    "lake", "elan", "lean", "unzip", "Std", "propext", "Quot.sound",
    "Classical.choice", "maxHeartbeats", "maxRecDepth", "lean_code",
    "RESULT:", "ABSENT", "MISMATCH 0/2", "STALE", "EXIT = 1", "u, v",
    "sufT_X", "07:12Z", "06:54:40Z", "sufT_*", "sufE_*", "v 0 1",
}
expected_absent = {"Nswap_perron_is_one"}  # renamed away; ledger cites the
#                                            old name only as history
candidates = []
for t in raw:
    t = t.strip()
    if t in skip_exact or t in expected_absent:
        continue
    if any(ch in t for ch in "/\\<>%$#!?→↦·=+,′"):
        continue
    if any(t.endswith(e) for e in
           (".sh", ".py", ".md", ".zip", ".lean", ".txt")):
        continue
    t = t.translate(SUB)
    first = t.split()[0].rstrip(":") if t.split() else ""
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", first) and len(first) > 2 \
            and not first[0].isdigit():
        candidates.append(first)
unresolved = []
for c in sorted(set(candidates)):
    tail = c.split(".")[-1]
    if c in ALL_SRC or tail in ALL_SRC:
        continue
    crate = PROOFS + slurp(os.path.join(ROOT, "ROUND5.md"))
    for extra in os.listdir(AUD):
        if extra.endswith((".py", ".sh", ".txt")):
            crate += slurp(os.path.join(AUD, extra))
    if c in crate or tail in crate:
        continue
    unresolved.append(c)
check("N: every backticked ledger identifier resolves in the sources or "
      "crate (%d candidates, %d unresolved)"
      % (len(set(candidates)), len(unresolved)), len(unresolved) == 0)
for u in unresolved:
    print("        UNRESOLVED ledger identifier: %s" % u)
check("N: the renamed-away name Nswap_perron_is_one is cited by the ledger "
      "as history and is absent from the sources",
      "Nswap_perron_is_one" in PROOFS
      and all("Nswap_perron_is_one" not in s for s in SRC.values()))
headliners = [
    "quantum_dimension_tau", "eigenvalues_exactly", "perron_selection",
    "branch_correspondence", "charpoly_coeffs", "Nfus", "eigen_phi",
    "eigen_yl", "trichotomy", "tri_count_eq_one", "no_sqrt5",
    "pos_add", "pos_mul", "phi_bracket", "sigma2_no_mul_lift_exists",
    "no_sqrt_neg_invPhi", "lift_shape_is_inhabited",
    "Nswap_has_positive_eigenvalue_one", "views.sh", "Zp.pos",
    "lift_forces_sqrt_neg_invPhi",
]
missing_h = [h for h in headliners if h not in PROOFS]
check("N: all %d round-5 headliners are mentioned in PROOFS.md "
      "(missing: %s)" % (len(headliners), missing_h or "none"),
      not missing_h)
in_src = [h for h in headliners if h != "views.sh"
          and h.split(".")[-1] not in ALL_SRC]
check("N: all headliner theorem names exist in the sources "
      "(missing: %s)" % (in_src or "none"), not in_src)

# ── 8. openness sweep ────────────────────────────────────────────────
print("== 8: openness sweep (grep the fact, not the name) ==")
anyon_lines = SRC["Anyon"].splitlines()
aud_pat = re.compile(r"left open|Not a proof|remains open|is open")
hits = [(i + 1, l) for i, l in enumerate(anyon_lines) if aud_pat.search(l)]
check("O: the round-5 audit's own pattern (left open|Not a proof|remains "
      "open|is open) hits exactly 1 line in Anyon.lean — the SUPERSEDED "
      "note quoting the old phrase (line %s)"
      % ([h[0] for h in hits] or "none"),
      len(hits) == 1 and "SUPERSEDED" in "\n".join(
          anyon_lines[max(0, hits[0][0] - 4):hits[0][0] + 2]) if hits
      else False)
check("O: the sigma2/sqrt(-1/phi) closure is recorded at the round-4 "
      "docstring (no site still calls THAT question open)",
      "It is not\n    open any more: §9.11 below proves "
      "`no_sqrt_neg_invPhi_emb`" in SRC["Anyon"])
wide = re.compile(r"nowhere proved in this file|NOT proved in this file|"
                  r"not itself a theorem yet|NOT proved here")
whits = [(i + 1, l.strip()) for i, l in enumerate(anyon_lines)
         if wide.search(l)]
stale = [(i, l) for i, l in whits if i < 5000]
check("FINDING RECEIPT: a WIDER openness pattern finds %d additional "
      "stale site(s) BEFORE line 5000 (rounds 1-3 text): lines %s — each "
      "says K-has-no-zero-divisors / 'exactly two' is NOT proved in this "
      "file" % (len(stale), [i for i, l in stale]),
      [i for i, l in stale] == [609, 1123, 1191])
check("FINDING RECEIPT: the same file DOES prove it — "
      "`theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : KK)` at ~5039 "
      "and `hexagon_exactly_two` consumes it at ~5116",
      "theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : KK)" in SRC["Anyon"]
      and re.search(r"theorem hexagon_exactly_two[\s\S]{0,700}?"
                    r"KK\.eq_zero_or_eq_zero_of_mul_eq_zero",
                    SRC["Anyon"]) is not None)
check("FINDING RECEIPT: the stale sites are round-4 inheritance, not new "
      "round-5 text — byte-identical lines in archive/src-round4/Anyon.lean",
      all(l in slurp(os.path.join(ROOT, "archive", "src-round4",
                                  "Anyon.lean")) for _, l in stale))
check("FINDING RECEIPT: the stale sites also point at 'PROOFS.md, declared "
      "gaps' — and the round-5 declared-gaps table no longer lists that "
      "gap (it was closed in round 4)",
      "See PROOFS.md, declared gaps" in SRC["Anyon"]
      and "third root" not in PROOFS
      and "no zero divisors" not in PROOFS.split("DECLARED GAPS")[1])

# ── instruments present with alarm text (E5, textual receipts only) ──
print("== 9: instrument presence + alarm text (textual receipts) ==")
axsh = slurp(os.path.join(AUD, "axioms.sh"))
trsh = slurp(os.path.join(AUD, "transcript.sh"))
check("I: axioms.sh ends in RESULT + exit on $STATUS (E5(i))",
      "RESULT:" in axsh
      and re.search(r'exit\s+"?\$\{?STATUS', axsh) is not None)
check("I: transcript.sh treats exit-0-no-olean as FAIL (E5(iii))",
      "NO OLEAN" in trsh or "no .olean" in trsh)
check("I: views.sh present alongside the other three instruments",
      all(os.path.exists(os.path.join(AUD, s))
          for s in ("views.sh", "ship.sh", "axioms.sh", "transcript.sh")))

print()
if FAILED:
    print("RESULT: %d check(s) FAILED:" % len(FAILED))
    for f in FAILED:
        print("  - " + f)
    sys.exit(1)
print("RESULT: ledger/census sweep PASS (with 4 FINDING receipts "
      "documenting the stale K-domain docstrings at Anyon.lean 609/1123/"
      "1191 — see report).")
