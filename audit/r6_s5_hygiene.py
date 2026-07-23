#!/usr/bin/env python3
"""r6_s5_hygiene.py — ROUND-5 SEAT: round-4 source audit, check S5.

Hygiene on archive/src-round4/Anyon.lean, comment-aware:
  * no sorry / native_decide / axiom / partial / import / unsafe / opaque /
    set_option in CODE (comments stripped by a nesting-aware stripper;
    every comment-only mention is listed);
  * the retraction and honest-label passages the round-4 round reported:
      - roots_sum_and_product's HONEST LABEL block,
      - cancel_of_inv's one-sided-inverse note,
      - no_obvious_sqrt_neg_invPhi saying the general question is LEFT OPEN
        in the ROUND-4 state (round 5 claims to have changed it — verified
        changed in the round-5 tree, and absent-of-change verified here);
  * NEW: stale honest labels — three round-3 "not proved in this file"
    passages that round 4 made FALSE by proving the domain property and
    Q_factors in the SAME file, and did not update (checked against both
    the round-4 archive and the round-5 tree).

Standalone; PASS/FAIL lines; exit = #FAIL.  FAIL marks a defect.
"""
import re, sys

SRC4 = "/home/claude/workshop/lean/archive/src-round4/Anyon.lean"
SRC5 = "/home/claude/workshop/lean/Anyon.lean"
src4 = open(SRC4, encoding="utf-8").read()
src5 = open(SRC5, encoding="utf-8").read()

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def strip_comments(t):
    """remove nested /- ... -/ blocks and -- line comments."""
    out, i, n, depth = [], 0, len(t), 0
    while i < n:
        if t.startswith("/-", i):
            depth += 1; i += 2
        elif depth and t.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            out.append("\n" if t[i] == "\n" else " "); i += 1
        elif t.startswith("--", i):
            j = t.find("\n", i); i = n if j < 0 else j
        else:
            out.append(t[i]); i += 1
    return "".join(out)

code4 = strip_comments(src4)
code_lines = code4.splitlines()

FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"\bnative_decide\b", "native_decide"),
    (r"^\s*axiom\b", "axiom"),
    (r"\bpartial\s+def\b", "partial def"),
    (r"^\s*import\b", "import"),
    (r"\bunsafe\b", "unsafe"),
    (r"^\s*opaque\b", "opaque"),
    (r"^\s*set_option\b", "set_option"),
    (r"@\[extern", "@[extern"),
    (r"implemented_by", "implemented_by"),
    (r"\bmacro\b", "macro"),
    (r"^\s*#eval\b", "#eval"),
]
for pat, nm in FORBIDDEN:
    hits = [i + 1 for i, l in enumerate(code_lines) if re.search(pat, l)]
    check(f"S5:code-free-of:{nm}", not hits,
          f"lines {hits}" if hits else "0 occurrences in comment-stripped code")

# where do the words appear at all? (must be comments only)
for word in ("sorry", "native_decide", "axiom", "partial", "import"):
    all_hits = [i + 1 for i, l in enumerate(src4.splitlines())
                if re.search(r"\b%s" % word, l)]
    code_hits = [i + 1 for i, l in enumerate(code_lines)
                 if re.search(r"\b%s" % word, l)]
    check(f"S5:mentions-only-in-comments:{word}", not code_hits,
          f"raw mentions at lines {all_hits[:8]}{'…' if len(all_hits) > 8 else ''} "
          "are all inside comments" if all_hits else "no mentions anywhere")

# tactic inventory (informational; asserts the file's own claims)
inv = {t: len(re.findall(r"\b%s\b" % t, code4)) for t in
       ("decide", "omega", "simp", "rfl", "calc", "induction")}
print(f"      tactic inventory (code only): {inv}")
check("S5:zero-imports-property", "\nimport" not in code4 and not code4.startswith("import"),
      "the file has zero imports (the load-bearing round-1 property)")
check("S5:single-namespace-shape",
      code4.count("namespace Workshop.Anyon") == 1 and
      src4.rstrip().endswith("end Workshop.Anyon"),
      "one top-level namespace, closed at EOF")

# ── the honest-label passages, verbatim in the round-4 state ─────────────
n4 = re.sub(r"\s+", " ", src4)
check("S5:label:cancel_of_inv-one-sided",
      "**left** inverse" in n4 and
      "The hypothesis is one-sided, so the theorem is *stronger* than that advertised" in n4,
      "round-3 correction present: docstring says LEFT inverse, one-sided")
check("S5:label:roots_sum_and_product-honest-label",
      "HONEST LABEL, tightened in round 3" in src4 and
      "was self-undercutting and is withdrawn" in src4,
      "the round-3 tightened label rides in the round-4 file")
check("S5:label:no_obvious_sqrt-left-open-in-round4",
      "that is left open, and stated as such" in src4 and
      "Not a proof that no square root" in src4,
      "ROUND-4 state DOES say the general √(−1/φ) question is left open — "
      "confirmed against the file round 5 claims to have changed")
check("S5:label:no-total-sqrt-theorem-in-round4",
      "no_sqrt_neg_invPhi" not in src4.replace("no_obvious_sqrt_neg_invPhi", ""),
      "and indeed round 4 has NO total no_sqrt_neg_invPhi theorem")
check("S5:label:round5-closed-it",
      "no_sqrt_neg_invPhi_emb" in src5 and
      'round-4 docstring said the general question "is left open".  It is not' in src5,
      "round-5 tree adds no_sqrt_neg_invPhi(_emb) and rewrites the docstring "
      "to point at it — the ROUND5.md queue item (b), landed")

# ── NEW FINDINGS: stale honest labels inside the round-4 file ────────────
# Round 4 proved K-domain (§12) and Q_factors in THIS file, but three
# round-3 passages upstream still assert the opposite in the present tense.
stale = [
    ("K being a domain is nowhere proved in this file",
     "§ 'The quadratic the hexagon forces' retraction block (~line 609)"),
    ("divisors, which is NOT proved in this file",
     "hexagon_forces_quadratic docstring (~line 1123)"),
    ("and it is NOT proved here.  See PROOFS.md, declared gaps",
     "roots_sum_and_product docstring (~line 1190)"),
    ("is **not asserted by any\n      declaration in this file**",
     "roots_sum_and_product docstring bullet 2 (~line 1184) — Q_factors NOW asserts it"),
]
for frag, where in stale:
    in4 = frag in src4
    in5 = frag in src5
    proved_in_same_file = ("theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : KK)" in src4
                           and "theorem Q_factors" in src4)
    check(f"S5:STALE-LABEL:{where.split('(')[0].strip()[:46]}",
          not (in4 and proved_in_same_file),
          f"present in round-4 file={in4}, still in round-5 tree={in5}; "
          "contradicted by §12 (K IS AN INTEGRAL DOMAIN) and Q_factors in the "
          "SAME file — a round-3 honest label made false by round 4's own "
          "sections and not updated ('grep the fact, not the name')")

# the flip side: §12 and the payoff do exist in the round-4 file
check("S5:domain-theorem-present",
      "theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : KK) (h : mul a b = zero)" in src4)
check("S5:Q_factors-present", "theorem Q_factors (s : KK)" in src4)

# _root_ census episode: the fix the ledger describes is in the file
check("S5:no-root-declarations",
      "_root_." not in strip_comments(src4),
      "no _root_.-reaching declarations remain in code (the census-INCOMPLETE "
      "episode's fix: KK.z5_eq_of_sub_eq_zero declared in-namespace)")
check("S5:root-episode-documented",
      "reported itself INCOMPLETE" in src4 and "KK.z5_eq_of_sub_eq_zero" in src4,
      "the episode is documented at the declaration that replaced it")

n_fail = sum(1 for _, ok in results if not ok)
print(f"\nS5 RESULT: {len(results) - n_fail}/{len(results)} PASS, {n_fail} FAIL "
      f"(each FAIL is a stale-label finding, not a soundness defect)")
sys.exit(min(n_fail, 120))
