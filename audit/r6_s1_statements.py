#!/usr/bin/env python3
"""r6_s1_statements.py — ROUND-5 SEAT: round-4 source audit, check S1.

Statement reconciliation for the round-4 headliners, READ AT LAST from
archive/src-round4/Anyon.lean (the file whose mathematics was verified blind
in round 4).  For each headliner named in archive/PROOFS-round4.md, this
script extracts the declaration's elaborated statement text from the source
and asserts the exact quantifiers / hypotheses / conclusion the ledger
sentence requires.  Matching is on whitespace-normalized source text.

Standalone; PASS/FAIL lines; exit code = number of FAILs.
"""
import re, sys

SRC4 = "/home/claude/workshop/lean/archive/src-round4/Anyon.lean"
SRC5 = "/home/claude/workshop/lean/Anyon.lean"
LEDGER4 = "/home/claude/workshop/lean/archive/PROOFS-round4.md"
HANDOFF = "/home/claude/workshop/lean/HANDOFF.md"

src4 = open(SRC4, encoding="utf-8").read()
src5 = open(SRC5, encoding="utf-8").read()
led4 = open(LEDGER4, encoding="utf-8").read()
handoff = open(HANDOFF, encoding="utf-8").read()

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

# Extract declaration text: from 'theorem NAME' to the start of the next
# top-level declaration or doc/section comment.  Returns (stmt, proof) split
# at the first top-level ':=' (adequate for this file: statements carry no ':=').
DECL_RE = re.compile(r"^(theorem|def|structure|namespace|end)\s", re.M)
def decl(source, name, after=0):
    m = None
    for kw in ("theorem", "def", "structure"):
        m = re.search(r"^%s %s\b" % (kw, re.escape(name)), source[after:], re.M)
        if m:
            break
    if not m:
        return None
    start = after + m.start()
    nxt = DECL_RE.search(source, start + 8)
    end = nxt.start() if nxt else len(source)
    body = source[start:end]
    # cut trailing doc/section comments off the proof so they cannot leak
    for marker in ("/-!", "/--"):
        cut = body.find(marker)
        if cut > 0:
            body = body[:cut]
    iz = body.find(":=")
    stmt = body[:iz] if iz >= 0 else body
    proof = body[iz:] if iz >= 0 else ""
    return norm(stmt), norm(proof), start

def has(name, key, where=None, detail=""):
    """statement of `name` (in src4) contains normalized fragment `key`."""
    d = decl(src4, name)
    if d is None:
        check(f"S1:{name}:exists", False, "declaration NOT FOUND in src-round4")
        return None
    stmt, proof, _ = d
    ok = norm(key) in stmt
    check(f"S1:{name}:{where or 'stmt'}", ok,
          detail or (f"needs «{norm(key)[:70]}…»" if not ok else "matches"))
    return (stmt, proof)

# ─────────────────────────────────────────────────────────────────────────
# 1. hexagon_exactly_two — ledger: "for *any* r1, r_tau in K, if the hexagon
#    holds then r_tau = rt or rt', and r1 = rt^2".  Hypothesis must be the
#    full guarded forall (64 tuples, 15 live per hexagon_live_instances).
d = decl(src4, "hexagon_exactly_two")
if d:
    stmt = d[0]
    check("S1:hexagon_exactly_two:binder", "(r1 rt : KK)" in stmt, "arbitrary r1 rt over K")
    check("S1:hexagon_exactly_two:hyp",
          "(h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true)" in stmt,
          "hypothesis = ALL 64 tuples of hexagonCheck (F fixed to Fsymm)")
    check("S1:hexagon_exactly_two:concl",
          stmt.endswith("(rt = KK.rt ∨ rt = rt') ∧ r1 = KK.mul rt rt"),
          "dichotomy AND r1 = rt^2 in the conclusion")
else:
    check("S1:hexagon_exactly_two:exists", False)

# pin the guarded forall: live-instance counts are theorems in the same file
check("S1:guard-pin:hexagon_live=15",
      "theorem hexagon_live_instances : countHexValid = 15 := rfl" in src4)
check("S1:guard-pin:pentagon_live=50",
      "theorem pentagon_live_instances : countPentValid = 50 := rfl" in src4)
check("S1:guard-pin:pentagon_nontrivial=11",
      re.search(r"theorem pentagon_nontrivial_instances\s*:", src4) is not None
      and "= 11" in decl(src4, "pentagon_nontrivial_instances")[0])

# ─────────────────────────────────────────────────────────────────────────
# 2. pentagon_exactly_two_worlds — ledger: "for *any* associator over K
#    satisfying the pentagon, p = 1/phi or p = -phi".  'any associator' is
#    Fg p q r s with all four entries universally quantified.
d = decl(src4, "pentagon_exactly_two_worlds")
if d:
    stmt = d[0]
    check("S1:pentagon_exactly_two_worlds:binder", "(p q r s : KK)" in stmt,
          "all four entries quantified = any 2x2 associator")
    check("S1:pentagon_exactly_two_worlds:hyp",
          "pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true" in stmt
          and "∀ a b c dd x y t w v" in stmt,
          "hypothesis = ALL 512 tuples")
    check("S1:pentagon_exactly_two_worlds:concl",
          stmt.endswith("p = KK.invPhi ∨ p = KK.neg (KK.emb Z5.phi)"),
          "p = 1/phi or p = -phi")
# Fg really is the generic associator (four independent entries):
fg = decl(src4, "Fg")
check("S1:Fg-generic", fg is not None and
      "| .one, .one => p" in fg[0]+fg[1] and "| .one, .tau => q" in fg[0]+fg[1] and
      "| .tau, .one => r" in fg[0]+fg[1] and "| .tau, .tau => s" in fg[0]+fg[1],
      "Fg p q r s has the four entries as the four matrix slots")

# ─────────────────────────────────────────────────────────────────────────
# 3. THE SHARP FORMS.  Ledger: "hexagon_exactly_two_sharp and
#    pentagon_exactly_two_sharp now carry the dichotomy, the distinctness,
#    and both-branches-realized in a single statement each."
d = decl(src4, "hexagon_exactly_two_sharp")
if d:
    stmt, proof, _ = d
    dich = "(∀ r1 rt : KK, (∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) → (rt = KK.rt ∨ rt = rt') ∧ r1 = KK.mul rt rt)"
    check("S1:hexagon_sharp:dichotomy", norm(dich) in stmt)
    check("S1:hexagon_sharp:distinctness", "KK.beq KK.rt rt' = false" in stmt)
    check("S1:hexagon_sharp:realized-golden",
          "(∀ a b c d e z, hexagonCheck kRng Fsymm KK.r1 KK.rt a b c d e z = true)" in stmt,
          "golden branch realized INSIDE the statement")
    check("S1:hexagon_sharp:realized-mirror",
          "(∀ a b c d e z, hexagonCheck kRng Fsymm r1' rt' a b c d e z = true)" in stmt,
          "mirror branch realized INSIDE the statement")
    check("S1:hexagon_sharp:one-term",
          "⟨hexagon_exactly_two, rfl, golden_satisfies_hexagon, mirror_satisfies_hexagon⟩" in proof,
          "single anonymous-constructor term, 4 components")

d = decl(src4, "pentagon_exactly_two_sharp")
if d:
    stmt, proof, _ = d
    check("S1:pentagon_sharp:dichotomy",
          "p = KK.invPhi ∨ p = KK.neg (KK.emb Z5.phi)" in stmt and
          "∀ p q r s : KK" in stmt)
    check("S1:pentagon_sharp:distinctness",
          "KK.beq KK.invPhi (KK.neg (KK.emb Z5.phi)) = false" in stmt)
    # THE LEDGER SENTENCE REQUIRES a both-realized conjunct.  A realization
    # conjunct would put a SECOND pentagonCheck (at concrete data) into the
    # statement, as the hexagon sharp form does with hexagonCheck (3 of them).
    realized = stmt.count("pentagonCheck") >= 2
    check("S1:pentagon_sharp:realized-conjunct-PRESENT", realized,
          ("" if realized else
           "LEDGER MISMATCH: statement = dichotomy ∧ distinctness ONLY "
           f"(pentagonCheck occurs {stmt.count('pentagonCheck')}x, all in the "
           "dichotomy hypothesis); proof term is the 2-component "
           "⟨pentagon_exactly_two_worlds, rfl⟩; realization exists elsewhere "
           "(golden_satisfies_pentagon / alt_root_satisfies_pentagon / "
           "yang_lee_satisfies_pentagon) but NOT in this statement"))
    check("S1:pentagon_sharp:docstring-overclaim",
          "both realized" not in src4[max(0,d[2]-400):d[2]],
          "the /-- docstring above the theorem also says 'dichotomy, distinctness, and both realized'"
          if "both realized" in src4[max(0,d[2]-400):d[2]] else "")
    # round-5 state: unchanged?
    d5 = decl(src5, "pentagon_exactly_two_sharp")
    check("S1:pentagon_sharp:still-2-conjunct-in-round5",
          d5 is not None and "⟨pentagon_exactly_two_worlds, rfl⟩" in d5[1],
          "finding persists in the round-5 tree (not silently fixed)")

# The theorems the round-4 ledger CITES for 'both realized' are vacuous apart
# from distinctness (their positive conjuncts are reflexivity / Or-of-rfl):
d = decl(src4, "hexagon_both_branches_realized")
if d:
    check("S1:hexagon_both_branches_realized:vacuous-support",
          "hexagonCheck" not in d[0] and "(KK.rt = KK.rt ∨ KK.rt = rt')" in d[0],
          "statement asserts rt/rt' satisfy the DICHOTOMY CONCLUSION (trivially true "
          "for any two elements), not that they satisfy the hexagon")
d = decl(src4, "pentagon_both_worlds_realized")
if d:
    check("S1:pentagon_both_worlds_realized:vacuous-support",
          "pentagonCheck" not in d[0] and "KK.invPhi = KK.invPhi" in d[0],
          "first two conjuncts are literal reflexivity; only distinctness has content")
# ...while the real realization theorems do exist under other names:
check("S1:realization-exists-elsewhere:hexagon",
      decl(src4, "golden_satisfies_hexagon") is not None and
      decl(src4, "mirror_satisfies_hexagon") is not None)
check("S1:realization-exists-elsewhere:pentagon",
      decl(src4, "alt_root_satisfies_pentagon") is not None and
      "yang_lee_satisfies_pentagon" in src4 and
      decl(src4, "golden_satisfies_pentagon") is not None)

# ─────────────────────────────────────────────────────────────────────────
# 4. Q_factors — ledger: "(s − r_tau)(s − r_tau') = s² + (1/phi)s + 1, for every s"
d = decl(src4, "Q_factors")
if d:
    stmt = d[0]
    check("S1:Q_factors:binder", "(s : KK)" in stmt, "for every s in K")
    check("S1:Q_factors:lhs",
          "KK.mul (KK.add s (KK.neg KK.rt)) (KK.add s (KK.neg rt'))" in stmt)
    check("S1:Q_factors:rhs",
          "KK.add (KK.add (KK.mul s s) (KK.mul KK.invPhi s)) KK.one" in stmt)
    check("S1:Q_factors:from-sum-and-product",
          "hsum : KK.add KK.rt rt' = KK.neg KK.invPhi := rfl" in d[1]
          and "hprod : KK.mul KK.rt rt' = KK.one := rfl" in d[1],
          "proved from exactly the sum and the product, as the ledger says")

# 5. sub_eq_zero_iff — "a − b = 0 ↔ a = b, from the additive laws alone"
d = decl(src4, "sub_eq_zero_iff")
if d:
    stmt, proof, _ = d
    check("S1:sub_eq_zero_iff:stmt",
          "(a b : KK)" in stmt and "KK.add a (KK.neg b) = KK.zero ↔ a = b" in stmt)
    mults = re.findall(r"KK\.(mul|one_mul|mul_one|mul_add|add_mul)", proof)
    check("S1:sub_eq_zero_iff:additive-only", not mults,
          f"proof uses only additive laws (no KK.mul*: {mults})")

# 6. exactly_two_of_domain — ledger ASSEMBLY table row; grep the name.
present4 = re.search(r"^theorem exactly_two_of_domain\b", src4, re.M)
present5 = re.search(r"^theorem exactly_two_of_domain\b", src5, re.M)
in_ledger = "exactly_two_of_domain" in led4
in_handoff = "exactly_two_of_domain" in handoff
check("S1:exactly_two_of_domain:exists-in-src4", present4 is not None,
      "LEDGER TABLE ROW WITH NO DECLARATION: named in PROOFS-round4.md "
      f"({in_ledger}) and HANDOFF.md ({in_handoff}) but absent from src-round4 "
      "AND from the round-5 tree "
      f"(round5 present={present5 is not None}) — D1 species (the exact defect "
      "class the builder pledged to grep for); content subsumed by "
      "hexagon_exactly_two, which applies the domain theorem directly")

# 7. pentagon_iff — pentagon ⟺ the three relations
d = decl(src4, "pentagon_iff")
if d:
    stmt = d[0]
    check("S1:pentagon_iff:stmt",
          "(∀ a b c dd x y t w v, pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true) ↔ (KK.mul q r = p ∧ KK.add (KK.mul p p) p = KK.one ∧ s = KK.neg p)"
          in stmt and "(p q r s : KK)" in stmt)

# 8. pentagon_sufficiency — three relations ⟹ all 512 tuples
d = decl(src4, "pentagon_sufficiency")
if d:
    stmt = d[0]
    check("S1:pentagon_sufficiency:stmt",
          "(h4 : KK.mul q r = p)" in stmt and
          "(hg : KK.add (KK.mul p p) p = KK.one)" in stmt and
          "(hs : s = KK.neg p)" in stmt and
          "∀ a b c dd x y t w v, pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true" in stmt)

# 9. no_gauge_golden_to_yang_lee — "no invertible diagonal gauge relates them"
d = decl(src4, "no_gauge_golden_to_yang_lee")
if d:
    stmt = d[0]
    check("S1:no_gauge:binder", "(l linv : Anyon → KK)" in stmt,
          "gauge quantified as arbitrary function of the labels")
    check("S1:no_gauge:vacuum-invertibility",
          "(hu : KK.mul (linv .one) (l .one) = KK.one)" in stmt,
          "inverse required ONLY at the vacuum (weaker hypothesis = stronger theorem)")
    check("S1:no_gauge:intertwiner",
          "∀ x y, KK.mul (l x) (Fsymm x y) = KK.mul (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi)) KK.one (KK.emb Z5.phi) x y) (l y)" in stmt,
          "l(x)·Fsymm(x,y) = F_YL(x,y)·l(y): the diagonal-gauge relation")
    check("S1:no_gauge:concl-False", stmt.rstrip().endswith(": False"),
          "conclusion is False — an impossibility theorem")
    check("S1:no_gauge:mechanism",
          "KK.add KK.invPhi (KK.emb Z5.phi)" in d[1],
          "the proof pivots on 1/phi + phi = 0 being forced, as the ledger says")

# 10. pentagonCheck_hom — natural along ANY hom of the hand-rolled rings
d = decl(src4, "pentagonCheck_hom")
if d:
    stmt = d[0]
    check("S1:pentagonCheck_hom:generic",
          "{R S : Type} {KR : Rng R} {KS : Rng S}" in stmt and "(H : RngHom KR KS)" in stmt,
          "quantified over ANY two rings and ANY RngHom")
    check("S1:pentagonCheck_hom:equal-Booleans",
          "pentagonCheck KS (fun i j => H.map (F i j)) a b c dd x y t w v = pentagonCheck KR F a b c dd x y t w v" in stmt,
          "same Boolean on EVERY tuple, valid or not")
    st = decl(src4, "RngHom")
    check("S1:pentagonCheck_hom:RngHom-carries-beq",
          st is not None and "map_beq" in (st[0] + st[1]),
          "NOTE: RngHom includes map_beq (beq-reflection = injectivity); "
          "'any ring map' in the ledger means any hom of the hand-rolled "
          "structures, which carry beq as data — declared in the file")

# 11. eleven_splits (+ its second witness)
d = decl(src4, "eleven_splits")
if d:
    stmt = d[0]
    check("S1:eleven_splits:stmt",
          "normZ ⟨-3,1,0,0⟩ = 121" in stmt and "% 11 = 0" in stmt and
          "((-3 : Int) % 11 ≠ 0 ∨ (1 : Int) % 11 ≠ 0)" in stmt,
          "N(ζ−3)=121, 11 | N, and ζ−3 has a coordinate not divisible by 11")
d = decl(src4, "eleven_splits2")
check("S1:eleven_splits2:stmt",
      d is not None and "normZ ⟨-4,1,0,0⟩ = 341" in d[0],
      "N(ζ−4)=341 lives in eleven_splits2 (ledger folds both under one name)")

# 12. the zero-divisor contrast pair
d = decl(src4, "square_extension_has_zero_divisors")
if d:
    stmt = d[0]
    check("S1:square_ext_zero_div:stmt",
          "mulFour ⟨⟨2,0,0,0⟩, Z5.one⟩ ⟨⟨2,0,0,0⟩, Z5.neg Z5.one⟩ = KK.zero" in stmt and
          stmt.count("= false") == 2,
          "(2+u)(2−u)=0 with BOTH factors nonzero, in the t²=4 model")
    mf = decl(src4, "mulFour")
    check("S1:mulFour-is-KKmul-with-4",
          mf is not None and "⟨4,0,0,0⟩" in (mf[0]+mf[1]) and "Z5.mul u.x v.x" in (mf[0]+mf[1]),
          "same carrier and multiplication shape, phi replaced by 4")
d = decl(src4, "golden_extension_no_such_zero_divisor")
if d:
    check("S1:golden_ext_no_zero_div:stmt",
          "KK.beq (KK.mul ⟨⟨2,0,0,0⟩, Z5.one⟩ ⟨⟨2,0,0,0⟩, Z5.neg Z5.one⟩) KK.zero = false" in d[0],
          "the SAME pair has nonzero product in the real K (t²=phi)")

# 13. the domain chain statements
d = decl(src4, "eq_zero_or_eq_zero_of_mul_eq_zero")   # first hit = Z5 (line ~2802)
if d:
    check("S1:Z5.domain:stmt",
          "(a b : Z5)" in d[0] and "(h : mul a b = zero)" in d[0] and
          "a = zero ∨ b = zero" in d[0])
d = decl(src4, "not_square")
if d:
    check("S1:Z5.not_square:stmt",
          "∀ x y : Z5, mul x x = mul phi (mul y y) → x = zero ∧ y = zero" in d[0],
          "phi-not-a-square in solution form (w²=phi would give x=w,y=1 nonzero)")
d = decl(src4, "ntz_mul")
if d:
    check("S1:KK.ntz_mul:stmt",
          "ntz (mul u v) = Z5.mul (ntz u) (ntz v)" in d[0])
d = decl(src4, "ntz_eq_zero_iff")
if d:
    check("S1:KK.ntz_eq_zero_iff:stmt",
          "ntz u = Z5.zero ↔ u = zero" in d[0])
    check("S1:KK.ntz_eq_zero_iff:spends-not_square",
          "Z5.not_square" in d[1], "the iff's forward direction spends §11")
# KK-level domain: second occurrence of the name
first = decl(src4, "eq_zero_or_eq_zero_of_mul_eq_zero")
d2 = decl(src4, "eq_zero_or_eq_zero_of_mul_eq_zero", after=first[2] + 10)
if d2:
    check("S1:KK.domain:stmt",
          "(a b : KK)" in d2[0] and "a = zero ∨ b = zero" in d2[0])
    check("S1:KK.domain:spends-both-descents",
          "ntz_mul" in d2[1] and "Z5.eq_zero_or_eq_zero_of_mul_eq_zero" in d2[1]
          and "ntz_eq_zero_iff" in d2[1],
          "pushes down via the t-norm, spends Z5-domain and phi-not-square")

n_fail = sum(1 for _, ok in results if not ok)
print(f"\nS1 RESULT: {len(results) - n_fail}/{len(results)} PASS, {n_fail} FAIL")
sys.exit(min(n_fail, 120))
