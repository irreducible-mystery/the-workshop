#!/usr/bin/env python3
"""r6_s3_shapes.py — ROUND-5 SEAT: round-4 source audit, check S3 (= E1).

E1, from the source at last.  ROUND5.md's open question: PROOFS-round4 says
the 39 trivial live pentagon instances "collapse to eight generic shapes
(multiplicities 21,4,3,5,2,2,1,1)"; the builder's auditor could only produce
7 shapes {21,4,4,4,4,1,1} (free-ring polynomial pairs) or 11
{17,4,4,3,2,2,2,2,1,1,1} (entry-abstracted trees) and asked for the criterion.

This script parses §7.5 of archive/src-round4/Anyon.lean and settles it:
  * counts the sufT_* lemmas (expect 8: B..I) and sufE_* (expect 11);
  * checks sufT_B / sufT_C have the exact quoted statements —
    (1*u)*1 + 0 = u*1  versus  = 1*u: SAME LHS, tree-distinct RHS, equal as
    K elements;
  * counts USE SITES of each sufT lemma across the 50 suffP instances
    (expect 21,4,3,5,2,2,1,1 summing to 39) and each sufE (once each, 11);
  * splits each sufT's uses into constant-slot vs entry-slot instantiations,
    reconstructing the auditor's 11-class multiset AND exhibiting the merges
    21=17+4, 3=1+2, 5=3+2 — so the "8 shapes" ARE the in-file lemma
    bookkeeping, criterion: same generic lemma statement with slots u,v
    instantiable by ARBITRARY terms (constants allowed), not entry-only
    abstraction;
  * confirms the file structure forces literal equations (pentcheck_of_eq).

Standalone; PASS/FAIL lines; exit = #FAIL.
"""
import re, sys
from collections import Counter

SRC = "/home/claude/workshop/lean/archive/src-round4/Anyon.lean"
text = open(SRC, encoding="utf-8").read()

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

# ── the eight sufT and eleven sufE lemmas ────────────────────────────────
sufT = re.findall(r"^theorem (sufT_\w+)", text, re.M)
sufE = re.findall(r"^theorem (sufE_\d+)", text, re.M)
check("S3:sufT-count", sufT == [f"sufT_{c}" for c in "BCDEFGHI"],
      f"eight generic shapes, B..I: {sufT}")
check("S3:sufE-count", sufE == [f"sufE_{i}" for i in range(1, 12)],
      f"eleven essential residuals: {len(sufE)}")

# exact statements of sufT_B and sufT_C, as the prover quoted them
mB = re.search(r"theorem sufT_B \(u : KK\) :(.*?):= by", text, re.S)
mC = re.search(r"theorem sufT_C \(u : KK\) :(.*?):= by", text, re.S)
sB, sC = norm(mB.group(1)), norm(mC.group(1))
lhs = "KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero"
check("S3:sufT_B-stmt", sB == f"{lhs} = KK.mul u KK.one",
      "(1*u)*1 + 0 = u*1   — verbatim")
check("S3:sufT_C-stmt", sC == f"{lhs} = KK.mul KK.one u",
      "(1*u)*1 + 0 = 1*u   — verbatim")
check("S3:B-C-same-LHS-distinct-RHS",
      sB.split(" = KK.mul")[0] == sC.split(" = KK.mul")[0] and sB != sC,
      "same LHS tree; RHS trees u*1 vs 1*u — distinct as trees, equal as K "
      "elements (mul_comm); pentcheck_of_eq needs the LITERAL tree, so they "
      "cannot be merged in the file even though they are one polynomial")

# ── parse the fifty suffP instances and their cited lemma ────────────────
suffP = {}
for m in re.finditer(
        r"^theorem suffP_(\d\d) \(p q r s : KK\)([^\n]*(?:\n[^\n]*?)*?)"
        r"pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ \((suf[TE]_\w+) ([^)]*)\)",
        text, re.M):
    idx, hyp_txt, lemma, args = m.group(1), m.group(2), m.group(3), m.group(4)
    suffP[int(idx)] = (lemma, norm(args), "h4" in hyp_txt or "hg" in hyp_txt or "hs" in hyp_txt)
check("S3:suffP-all-50-parsed", sorted(suffP) == list(range(1, 51)),
      f"parsed {len(suffP)} instance lemmas suffP_01..suffP_50")

use = Counter(l for l, _, _ in suffP.values() if l.startswith("sufT"))
expected = {"sufT_B": 21, "sufT_C": 4, "sufT_D": 3, "sufT_E": 5,
            "sufT_F": 2, "sufT_G": 2, "sufT_H": 1, "sufT_I": 1}
check("S3:multiplicities-21-4-3-5-2-2-1-1", dict(use) == expected,
      f"use-site counts {dict(use)}; sum {sum(use.values())} = 39")
check("S3:multiplicities-sum-39", sum(use.values()) == 39)
useE = Counter(l for l, _, _ in suffP.values() if l.startswith("sufE"))
check("S3:sufE-once-each", all(v == 1 for v in useE.values()) and len(useE) == 11,
      "each essential residual used exactly once; 39 + 11 = 50")

hyp_set = {i for i, (_, _, h) in suffP.items() if h}
check("S3:hypothesis-carrying-set",
      hyp_set == {38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 50},
      f"exactly the eleven of pentagon_nontrivial_instances, in the types: {sorted(hyp_set)}")
check("S3:hyp-iff-sufE",
      all((l.startswith("sufE")) == (i in hyp_set) for i, (l, _, _) in suffP.items()),
      "an instance takes a relation hypothesis IFF it cites a sufE lemma")

# docstring multiplicity claims vs computed
doc_claims = dict(re.findall(r"/-- Shape (\w), (\d+) instances?", text))
check("S3:docstring-counts-match",
      all(use[f"sufT_{k}"] == int(v) for k, v in doc_claims.items()) and len(doc_claims) == 8,
      f"docstring claims {doc_claims} all match use-site counts")

# ── E1 RESOLUTION: constant-slot vs entry-slot split ─────────────────────
CONST = {"KK.one", "KK.zero"}
split = {}
for i, (l, args, _) in suffP.items():
    if not l.startswith("sufT"):
        continue
    toks = args.split()
    kind = "const" if all(t in CONST for t in toks) else "entry"
    split.setdefault(l, Counter())[kind] += 1
b_at_one = sum(1 for i, (l, a, _) in suffP.items() if l == "sufT_B" and a == "KK.one")
check("S3:B-17-at-u-eq-1", b_at_one == 17,
      "sufT_B: 17 uses at u = 1 (docstring: '21 instances (17 of them at u = 1)') "
      f"+ {use['sufT_B'] - b_at_one} entry uses (p,q,r,s)")

refined = []
for l in sorted(split):
    for kind in ("const", "entry"):
        if split[l][kind]:
            refined.append(split[l][kind])
refined_multiset = sorted(refined, reverse=True)
check("S3:E1:11-class-refinement",
      refined_multiset == [17, 4, 4, 3, 2, 2, 2, 2, 1, 1, 1],
      f"constant/entry split of the 8 lemmas gives {refined_multiset} — EXACTLY "
      "the builder-auditor's entry-abstracted multiset {17,4,4,3,2,2,2,2,1,1,1}")
merges = {l: split[l]["const"] + split[l]["entry"] for l in split}
check("S3:E1:merges-produce-the-8",
      merges["sufT_B"] == 17 + 4 == 21 and merges["sufT_D"] == 1 + 2 == 3
      and merges["sufT_E"] == 3 + 2 == 5,
      "21 = 17+4 (B: const⊕entry), 3 = 1+2 (D), 5 = 3+2 (E) — the auditor's "
      "'no merge of those families can produce a 5 or a 3' is REFUTED from "
      "source: the file's 8 shapes are exactly merges of the 11 entry-"
      "abstracted classes, merging a constant-instantiated class into the "
      "generic lemma that subsumes it")
print("      E1 CRITERION (named, from the file): two residuals share a shape "
      "iff both are substitution instances of one generic lemma statement "
      "sufT_X u v — slots instantiable by ANY K-term, constants included; "
      "(LHS,RHS) trees are compared literally (defeq on concrete labels), so "
      "B and C stay distinct while u:=1 folds into B.  It is in-file lemma "
      "bookkeeping, exactly the hypothesis E1 offered.")

# NOTE on the crediting freedom (why no canonical clustering reproduces it):
allconst_B = [i for i, (l, a, _) in suffP.items() if l == "sufT_B" and a == "KK.one"]
check("S3:E1:crediting-freedom-note", len(allconst_B) == 17,
      "at u := 1, sufT_B and sufT_C give the SAME fully-concrete equation, so "
      "crediting the 17 constant instances to B (not C) is a covering CHOICE; "
      "the multiset {21,4,...} is bookkeeping of the chosen cover, not a "
      "canonical partition — which is why no clustering criterion alone "
      "reproduces it and why the ledger sentence should carry its criterion")

# ── the structure that forces literal equations ──────────────────────────
m = re.search(r"theorem pentcheck_of_eq(.*?):= by", text, re.S)
stmt = norm(m.group(1))
check("S3:pentcheck_of_eq-needs-literal-equation",
      "(h : sumOver kRng (fun u => KK.mul (KK.mul (Fs kRng F a b c y x u) (Fs kRng F a u dd t y v)) (Fs kRng F b c dd v u w)) (fuse b c) = KK.mul (Fs kRng F x c dd t y w) (Fs kRng F a b w t x v))" in stmt,
      "the bridge demands the instance's LHS = RHS as a K equation; the "
      "elaborator's defeq reduction at concrete labels is what makes a sufT "
      "statement (with its exact trees) dischargeable — expression-tree "
      "identity up to slot instantiation is FORCED by this interface")
check("S3:decide_eq_true-bridge", "decide_eq_true h" in text,
      "decide is produced, never reduced — the round-3 blocker's solvent")

# suffQ bullet counts tie to the live-instance census, charge by charge
bullets = []
for m in re.finditer(r"theorem suffQ_(\d\d) \(p q r s : KK\)(.*?)(?=^theorem|\Z)",
                     text, re.M | re.S):
    bullets.append(len(re.findall(r"·\s*exact suffP_", m.group(2))))
check("S3:suffQ-bullets", bullets == [1,1,1,2,1,2,2,5,1,2,2,5,2,5,5,13]
      and sum(bullets) == 50,
      f"16 total charges, bullets {bullets} sum to 50 = pentagon_live_instances")
check("S3:assembly", "exact suffQ_15 p q r s h4 hg hs" in text and
      text.count("exact suffQ_") == 16,
      "pentagon_sufficiency dispatches all 16 charges; only (τ,τ,τ,τ) "
      "consumes the three relations")

n_fail = sum(1 for _, ok in results if not ok)
print(f"\nS3 RESULT: {len(results) - n_fail}/{len(results)} PASS, {n_fail} FAIL")
sys.exit(min(n_fail, 120))
