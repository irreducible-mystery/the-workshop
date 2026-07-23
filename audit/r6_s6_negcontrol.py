#!/usr/bin/env python3
"""r6_s6_negcontrol.py — ROUND-5 SEAT: round-4 source audit, check S6.

Negative control for the seat itself: pick two round-4 ledger sentences and
TRY to construct a reading under which the cited statements do NOT support
them.  Report either the failed attempt (good) or the gap (better).

Sentence A (PROOFS-round4.md, headline section):
  "Both branches are realized in both cases, so neither dichotomy is a
   disguised uniqueness: `hexagon_both_branches_realized` and
   `pentagon_both_worlds_realized`, with the two values proved distinct."
  ATTACK: read 'realized' as 'the named theorems prove the two values
  satisfy the coherence equation'.  Then check what the named theorems say.

Sentence B (PROOFS-round4.md, headline):
  "`hexagon_exactly_two` — for *any* r1, r_tau in K, if the hexagon holds
   then r_tau = rt or rt', and r1 = rt^2."
  ATTACK: read 'the hexagon' associator-generically (any F), the way the
  pentagon headline's 'any associator' reads.  Then check the statement.

FAIL lines mark gaps found (attack succeeded); PASS marks robust sentences.
Exit = #gaps.
"""
import re, sys

SRC = "/home/claude/workshop/lean/archive/src-round4/Anyon.lean"
LED = "/home/claude/workshop/lean/archive/PROOFS-round4.md"
text = open(SRC, encoding="utf-8").read()
led = open(LED, encoding="utf-8").read()

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

def stmt_of(name):
    m = re.search(r"^theorem %s\b(.*?):=" % re.escape(name), text, re.M | re.S)
    return norm(m.group(1)) if m else None

# ── Sentence A ───────────────────────────────────────────────────────────
check("S6:A:ledger-sentence-present",
      "hexagon_both_branches_realized" in led and
      "pentagon_both_worlds_realized" in led and
      "Both branches are realized in both cases" in norm(led))

sA1 = stmt_of("hexagon_both_branches_realized")
sA2 = stmt_of("pentagon_both_worlds_realized")
print(f"      hexagon_both_branches_realized : {sA1}")
print(f"      pentagon_both_worlds_realized  : {sA2}")

# The attack: under the natural reading, 'realized' should mean the values
# SATISFY the equation.  Do the cited statements contain any coherence check?
a1_has_content = "hexagonCheck" in (sA1 or "")
a2_has_content = "pentagonCheck" in (sA2 or "")
check("S6:A:attack-on-cited-support", a1_has_content and a2_has_content,
      "GAP (attack succeeds at the citation level): both cited theorems are "
      "coherence-free.  hexagon_both_branches_realized asserts the two values "
      "satisfy the DICHOTOMY'S CONCLUSION (Or.inl rfl / Or.inr rfl — true of "
      "any two elements) plus distinctness; pentagon_both_worlds_realized's "
      "positive conjuncts are literal reflexivity (invPhi = invPhi, "
      "-phi = -phi) plus distinctness.  'Realized' in the satisfaction sense "
      "is proved ELSEWHERE: golden/mirror_satisfies_hexagon (and inside "
      "hexagon_exactly_two_sharp), golden_satisfies_pentagon / "
      "alt_root_satisfies_pentagon / yang_lee_satisfies_pentagon — but the "
      "pentagon sharp form never absorbed them (see r6_s1)")

# the repair exists for the hexagon (sharp form) but not the pentagon
sharp_hex = stmt_of("hexagon_exactly_two_sharp") or ""
sharp_pent = stmt_of("pentagon_exactly_two_sharp") or ""
check("S6:A:hexagon-sharp-absorbs-realization",
      sharp_hex.count("hexagonCheck") == 3,
      "hexagon_exactly_two_sharp DOES carry both satisfaction facts (3 "
      "hexagonCheck occurrences: hypothesis + 2 realizations)")
check("S6:A:pentagon-sharp-absorbs-realization",
      sharp_pent.count("pentagonCheck") >= 2,
      "GAP: pentagon_exactly_two_sharp carries only the dichotomy hypothesis "
      f"({sharp_pent.count('pentagonCheck')} pentagonCheck occurrence) — "
      "dichotomy + distinctness, NO realization conjunct, contra both its "
      "docstring and the ledger's 'in a single statement each'")

# ── Sentence B ───────────────────────────────────────────────────────────
sB = stmt_of("hexagon_exactly_two")
check("S6:B:ledger-sentence-present", "for *any* `r₁, r_τ` in K" in led)
# the adversarial reading needs an F-generic hexagon uniqueness; is there one?
hex_uniq_names = ["hexagon_exactly_two", "hexagon_exactly_two_sharp",
                  "hexagon_uniqueness", "hexagon_forces_quadratic",
                  "hexagon_forces_r1_eq_rt_sq", "hexagon_forces_rt_unit"]
all_fsymm = all("hexagonCheck kRng Fsymm" in (stmt_of(n) or "")
                for n in hex_uniq_names)
# is there ANY theorem whose statement runs hexagonCheck over a quantified F?
f_generic_hex = False
for m in re.finditer(r"^theorem (\w+)", text, re.M):
    seg = text[m.start():m.start() + 2500]
    iz = seg.find(":=")
    st = norm(seg[:iz]) if iz > 0 else norm(seg)
    if re.search(r"hexagonCheck kRng F\b", st) and "F : Anyon → Anyon → KK" in st:
        f_generic_hex = True
        break
check("S6:B:attack-fails-statement-is-explicit", all_fsymm,
      "ATTACK FAILS (good): every hexagon-uniqueness statement writes "
      "`hexagonCheck kRng Fsymm r1 rt` — the associator is pinned to Fsymm "
      "IN THE STATEMENT, so the adversarial 'any F' reading is refuted by "
      "the visible text, not by charity.  SCOPE NOTE, worth carrying: the "
      "pentagon side IS associator-generic (Fg p q r s, all four entries "
      "quantified); the hexagon side quantifies braidings only, with the "
      "associator fixed — 'exactly two ways to braid the world' is exact "
      "relative to the symmetric gauge, with §8's gauge transport "
      "(FratK_of_Fsymm, hexagonCheck_conj) carrying it to the other gauge; "
      f"an F-generic hexagon uniqueness theorem exists: {bool(f_generic_hex)}")
check("S6:B:ledger-states-the-F-dependence",
      "hexagonCheck kRng Fsymm" in (sB or ""),
      "the theorem the ledger names says Fsymm explicitly; the ledger "
      "sentence elides it but does not contradict it")

# one bonus probe: the ledger folds eleven_splits2's content under
# eleven_splits' name ("eleven_splits: N(ζ−3) = 121 = 11² ... and
# N(ζ−4) = 341 = 11·31") — the 341 lives in a different theorem.
e1 = stmt_of("eleven_splits") or ""
e2 = stmt_of("eleven_splits2") or ""
check("S6:bonus:eleven_splits-name-folding",
      "341" not in e1 and "341" in e2 and "341" in led,
      "minor binding note: the ledger sentence attributes both norms to "
      "`eleven_splits`; N(ζ−4)=341 is `eleven_splits2` — the fact is proved, "
      "the name binding is loose (predicted round-5 defect class: the verb, "
      "not the noun)")

gaps = sum(1 for _, ok in results if not ok)
print(f"\nS6 RESULT: {len(results) - gaps}/{len(results)} PASS, {gaps} GAP(S) FOUND "
      "(a FAIL here is a successful negative control — a gap, the better outcome)")
sys.exit(min(gaps, 120))
