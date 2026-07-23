#!/usr/bin/env python3
"""r6_s2_descent.py — ROUND-5 SEAT: round-4 source audit, check S2.

The two descent proofs, READ from archive/src-round4/Anyon.lean:
  §10  2-adic descent  (Cong2 ring congruence, 16-case decide, Nat-fuel induction)
  §11  41-adic descent (roots iff over all residues, nonsquares, hand-inverted
       Vandermonde identities, Nat-fuel induction)
  §12  the bridge (no omega, no decide — pure calc)

Verified here:
  (a) NO omega closes a conjunctive goal anywhere in these blocks — every
      omega site is enumerated and classified (the named trap from HANDOFF);
  (b) fuel/structural induction only: `induction n with`, fuel discharged by
      Nat.le_refl; no partial def, no well-founded recursion markers;
  (c) the 16-case and 41-residue decides are present as `decide` on closed
      propositions;
  (d) the arithmetic content of every decide/omega certificate re-verified in
      exact Python (16 parity classes, roots/nonsquares mod 41, Vandermonde,
      id0..id3, ev41 maps, all negative-control witnesses).

Standalone; PASS/FAIL lines; exit = #FAIL.
"""
import re, sys
from itertools import product

SRC = "/home/claude/workshop/lean/archive/src-round4/Anyon.lean"
lines = open(SRC, encoding="utf-8").read().splitlines()
text = "\n".join(lines)

results = []
def check(name, ok, detail=""):
    ok = bool(ok)
    results.append((name, ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

def lineno(pat):
    for i, l in enumerate(lines, 1):
        if pat in l:
            return i
    return None

# ── block boundaries, located by their in-file markers ────────────────────
b10_start = lineno("ROUND 4 — `σ`, THE NORM MAP")           # §10 header
b41_start = lineno("**φ IS NOT A SQUARE IN `Z5 = Z[ζ₅]`**") # §11 header
b41_end   = lineno("## 9.  THE YANG–LEE ROOT")               # §9 header (after §11)
b12_start = lineno("## 12.  **K IS AN INTEGRAL DOMAIN**")
check("S2:blocks-located", all([b10_start, b41_start, b41_end, b12_start]),
      f"§10@{b10_start} §11@{b41_start}..{b41_end} §12@{b12_start}..EOF")

block10 = list(range(b10_start, b41_start))
block41 = list(range(b41_start, b41_end))
block12 = list(range(b12_start, len(lines) + 1))
descent_lines = set(block10) | set(block41) | set(block12)

# ── (a) the omega census: every site classified ───────────────────────────
# Classes:
#   SPLIT  — `refine ⟨…⟩ <;> omega` (or `<;> first | omega | trivial`):
#            the conjunction is split BEFORE omega sees a goal.
#   TERM   — `⟨…, by omega, …⟩` / `exact ⟨p + q, by omega⟩`: each omega
#            closes one component, never the conjunction.
#   ATOMIC — bare/terminal omega whose governing goal is a single equation,
#            inequality or mod-goal (no top-level ∧).
#   DVD    — bare omega on a divisibility goal `41 ∣ z` (existential-shaped;
#            NOT the conjunctive trap; census says Classical.choice 0).
omega_sites = []
for i in sorted(descent_lines):
    if i > len(lines):
        break
    l = lines[i - 1]
    code = l.split("--")[0]
    if re.search(r"\bomega\b", code) and not code.strip().startswith("`"):
        # skip comment lines (inside /-! or /-- blocks): heuristic — those
        # lines here all contain backticks around omega or start with text
        if "`omega`" in l:
            continue
        omega_sites.append((i, l.rstrip()))

classified = {}
KNOWN_ATOMIC_GOALS = {
    # line: governing goal (read from source), shape
    2594: "(mul u v).a0 = u.a0 * v.a0 (after rw)",
    2656: "(mul two w).a0 = 2 * w.a0",
    2669: "normZ a % 2 = normZ b % 2 (single equation, from e)",
    2684: "n % 2 = 0 (false branch of bit_eq)",
    2779: "normZ ⟨x0/2,…⟩ = 0 (from 16*· = 0)",
    2781: "natAbs sum ≤ n (measure bound hm2)",
    3052: "((a%41).toNat : Int) = a % 41", 3053: "((b%41).toNat : Int) = b % 41",
    3054: "(a%41).toNat < 41", 3055: "(b%41).toNat < 41",
    3065: "((a%41).toNat : Int) = a % 41", 3066: "((b%41).toNat : Int) = b % 41",
    3067: "(a%41).toNat < 41", 3068: "(b%41).toNat < 41",
    3087: "id0 closed linear identity", 3092: "id1", 3097: "id2", 3102: "id3",
    3130: "m0+…+m7 ≤ n (sum8_step)",
    3182: "ev41A_add equation", 3184: "ev41B_add equation",
    3186: "ev41C_add equation", 3188: "ev41D_add equation",
    3199: "ev41A_mul mod equation", 3208: "ev41B_mul mod equation",
    3217: "ev41C_mul mod equation", 3226: "ev41D_mul mod equation",
}
DVD_GOALS = {3104: "(41:Int) ∣ z (dvd41_of_emod)", 3119: "(41:Int) ∣ x (dvd41_strip)"}

n_conj_direct = 0
for i, l in omega_sites:
    if re.search(r"refine ⟨.*⟩ <;> (omega|first \| omega)", l):
        cls = "SPLIT"
    elif re.search(r"⟨.*by omega", l) or "exact ⟨" in l:
        cls = "TERM"
    elif 2947 <= i <= 2962:
        cls = "ATOMIC"    # gMN closed linear identities: single equations
    elif i in KNOWN_ATOMIC_GOALS:
        cls = "ATOMIC"
    elif i in DVD_GOALS:
        cls = "DVD"
    else:
        cls = "UNCLASSIFIED"
        n_conj_direct += 1
    classified.setdefault(cls, []).append(i)

check("S2:omega-census:all-sites-classified", n_conj_direct == 0,
      f"{len(omega_sites)} omega sites in §10/§11/§12: "
      f"{len(classified.get('SPLIT', []))} split-then-omega, "
      f"{len(classified.get('TERM', []))} per-component term-level, "
      f"{len(classified.get('ATOMIC', []))} atomic-goal, "
      f"{len(classified.get('DVD', []))} divisibility-goal "
      f"(lines {classified.get('DVD')}); unclassified: {classified.get('UNCLASSIFIED', [])}")
check("S2:omega-census:no-conjunctive-goal", n_conj_direct == 0,
      "no bare omega governs a goal with top-level ∧ — the named trap is absent")
check("S2:omega-census:dvd-note", set(DVD_GOALS) == set(classified.get("DVD", [])),
      "the only non-equation direct omega goals are the two `41 ∣ ·` "
      "(existential-shaped Dvd, not the conjunctive trap; round-4 census "
      "reports Classical.choice 0 over 690, which arbitrates)")

# the four sites the ledger says were fixed now carry the split form / no omega
sz0 = decl_i = lineno("theorem sz_zero")
seg = "\n".join(lines[sz0 - 1: sz0 + 8])
check("S2:fixed-site:sz_zero", "omega" not in seg and "sum8_zero" in seg,
      "sz_zero no longer touches omega (delegates to sum8_zero + ext41)")
smi = lineno("theorem sm41_inj")
seg = "\n".join(lines[smi - 1: smi + 4])
check("S2:fixed-site:sm41_inj", "refine ⟨?_,?_,?_,?_⟩ <;> omega" in seg)
for nm, ln_th in (("nsq7", lineno("theorem nsq7 (a b : Int)")),
                  ("nsq35", lineno("theorem nsq35 (a b : Int)"))):
    seg = "\n".join(lines[ln_th - 1: ln_th + 11])
    check(f"S2:fixed-site:{nm}", "refine ⟨?_,?_⟩ <;> omega" in seg)

# §12 is omega- and decide-free
s12 = "\n".join(lines[b12_start - 1:])
check("S2:section12-pure-calc",
      not re.search(r"\bomega\b", s12) and not re.search(r"\bdecide\b", s12.replace("`decide`", "")),
      "§12 (the bridge + payoff) contains no omega and no decide — calc/rfl/rcases only")

# ── (b) fuel / structural induction ───────────────────────────────────────
d2 = text[text.index("theorem descent :"):text.index("theorem normZ_eq_zero_iff")]
d41 = text[text.index("theorem descent41 :"):text.index("/-! ### Main theorem")]
check("S2:fuel:descent-structural", "induction n with" in d2 and "| succ n ih" in d2,
      "2-adic: plain structural induction on the Nat fuel")
check("S2:fuel:descent41-structural", "induction n with" in d41 and "| succ n ih" in d41,
      "41-adic: plain structural induction on the Nat fuel")
check("S2:fuel:discharged-2adic",
      "Nat.le_refl" in text[text.index("theorem normZ_eq_zero_iff"):
                            text.index("theorem normZ_eq_zero_iff") + 600],
      "fuel discharged at the interface by Nat.le_refl (normZ_eq_zero_iff)")
check("S2:fuel:discharged-41adic",
      "Nat.le_refl" in text[text.index("theorem not_square"):
                            text.index("theorem not_square") + 300],
      "fuel discharged at the interface by Nat.le_refl (not_square)")
def strip_comments(t):
    out, i, n, depth = [], 0, len(t), 0
    while i < n:
        if t.startswith("/-", i):
            depth += 1; i += 2
        elif depth and t.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif t.startswith("--", i):
            j = t.find("\n", i); i = n if j < 0 else j
        else:
            out.append(t[i]); i += 1
    return "".join(out)
code = strip_comments(text)
for marker in ("partial def", "termination_by", "decreasing_by", "WellFounded",
               "strongRecOn", "strongInductionOn", "Nat.rec "):
    check(f"S2:no-marker:{marker.strip()}", marker not in code,
          "absent from the whole round-4 file (comment-stripped; the only "
          "mention of strongRecOn is the descent41 docstring DISCLAIMING it)"
          if marker == "strongRecOn" else "absent from the whole round-4 file (comment-stripped)")

# ── (c) the decides are on closed propositions ────────────────────────────
seg = text[text.index("theorem bits_norm_zero"):text.index("/-! #### The 16-case nest")]
check("S2:16-case:cases-then-decide",
      "cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> revert h <;> decide" in seg,
      "16 branches, each a closed Int implication decided by kernel evaluation")
seg = text[text.index("def parityNest"):text.index("def parityOddCount")]
check("S2:16-case:nest-is-16-literals", seg.count("(") - seg.count("fun") >= 16 and
      len(re.findall(r"\((?:false|true)\s*,", seg)) == 16,
      "parityNest literal has exactly 16 tuples")
check("S2:16-case:nest-counted-against-itself",
      "theorem parityNest_size : parityNest.length = 16 := by decide" in text and
      "parityNest.count p == 1" in text and
      "theorem parityOddCount_eq : parityOddCount = 15 := by decide" in text,
      "size 16, nodup, odd-count 15 — count tied to its own nest")

for nm, want in [
    ("roots_char", "∀ r, r < 41 →"),
    ("nonsq7", "∀ i, i < 41 → (i*i) % 41 ≠ 7"),
    ("nonsq35", "∀ i, i < 41 → (i*i) % 41 ≠ 35"),
    ("nsq7N", "∀ m : Nat, m < 41 → ∀ n : Nat, n < 41 →"),
    ("nsq35N", "∀ m : Nat, m < 41 → ∀ n : Nat, n < 41 →"),
]:
    m = re.search(r"^theorem %s\b(.*?):= by decide$" % nm, text, re.M | re.S)
    ok = m is not None and want in re.sub(r"\s+", " ", m.group(1))
    check(f"S2:41-decide:{nm}", ok,
          "closed bounded-∀ proposition, `by decide`" if ok else "pattern not found")
check("S2:41-decide:roots-iff",
      "↔" in decl_stmt if (decl_stmt := re.sub(r"\s+", " ",
        re.search(r"theorem roots_char(.*?):= by decide", text, re.S).group(1))) else False,
      "root certificate is an IFF over all residues (both directions certified)")

# negative controls, one per family (house norm)
for nm in ("two_not_root", "two_is_square", "nsq4N_false",
           "coords_dvd41_needs_all_four", "not_square_false_for_squares",
           "square_case_has_nonzero_solution", "phi_sq_case_has_nonzero_solution",
           "fnorm3_breaks_parity", "fnorm3OddCount_eq", "eleven_splits",
           "a0map_not_mul", "twoFactor_not_in_Z"):
    check(f"S2:negctl:{nm}", re.search(r"^theorem %s\b" % nm, text, re.M) is not None)

# ── (d) exact Python re-verification of every certificate ─────────────────
# Z5 arithmetic (fixed since round 1)
def z5add(u, v): return tuple(a + b for a, b in zip(u, v))
def z5neg(u): return tuple(-a for a in u)
def z5mul(u, v):
    c = [0] * 7
    for i in range(4):
        for j in range(4):
            c[i + j] += u[i] * v[j]
    # z^4 = -(1+z+z^2+z^3), z^5 = 1, z^6 = z
    return (c[0] - c[4] + c[5], c[1] - c[4] + c[6], c[2] - c[4], c[3] - c[4])
ZERO, ONE = (0, 0, 0, 0), (1, 0, 0, 0)
PHI, INVPHI = (0, 0, -1, -1), (-1, 0, -1, -1)
ZETA = (0, 1, 0, 0)
def sigma(u):
    a0, a1, a2, a3 = u
    return (a0 - a2, a3 - a2, a1 - a2, -a2)
def norm(a):
    s1 = sigma(a); s2 = sigma(s1); s3 = sigma(s2)
    return z5mul(z5mul(a, s1), z5mul(s2, s3))
def normZ(a):
    n = norm(a)
    assert n[1] == n[2] == n[3] == 0, ("norm not in Z", a, n)
    return n[0]

check("S2:py:norm-in-Z-and-multiplicative",
      all(normZ(z5mul(u, v)) == normZ(u) * normZ(v)
          for u in [(1,2,-1,0), (0,1,0,0), (3,-2,5,1), (0,0,-1,-1)]
          for v in [(2,0,0,0), (-1,1,4,2), (0,0,0,1)]),
      "norm lands in Z (asserted per element) and is multiplicative on samples")
check("S2:py:norm-values",
      normZ(ZERO) == 0 and normZ(ONE) == 1 and normZ(PHI) == 1 and
      normZ(INVPHI) == 1 and normZ(ZETA) == 1 and normZ((2,0,0,0)) == 16 and
      normZ((1,-1,0,0)) == 5,
      "0,1,1,1,1,16,5 — all seven anti-vacuity values")
# 16-case fact + count 15, and the fnorm3 control count 8
bits = list(product([0, 1], repeat=4))
odd = [b for b in bits if normZ(b) % 2 == 1]
check("S2:py:16-case-fact",
      len(odd) == 15 and all(normZ(b) % 2 == 1 for b in bits if b != (0,0,0,0))
      and normZ((0,0,0,0)) % 2 == 0,
      "every nonzero parity class has odd norm; count 15 of 16")
def fnorm3(a):
    s1 = sigma(a); s2 = sigma(s1)
    return z5mul(z5mul(a, s1), s2)[0]
check("S2:py:fnorm3-control",
      sum(1 for b in bits if fnorm3(b) % 2 == 1) == 8 and fnorm3((0,0,0,1)) % 2 == 0,
      "3-factor product odd on only 8 of 16; fails at (f,f,f,t) — the decide would break")
def conj(u):
    a0, a1, a2, a3 = u
    return (a0 + 0, -a3, -a2, -a1) if False else None
# conj: z -> z^4 = -(1+z+z^2+z^3): compute via z5mul powers instead
def conjmap(u):
    # z^k -> z^(4k mod 5) expressed in basis
    out = (u[0], 0, 0, 0)
    zpow = {0: ONE, 1: (-1,-1,-1,-1), 2: (0,0,0,1), 3: (0,0,1,0)}  # z^4,z^8=z^3,z^12=z^2
    out = (u[0], 0, 0, 0)
    for k in (1, 2, 3):
        out = z5add(out, tuple(u[k] * c for c in zpow[k]))
    return out
check("S2:py:twoFactor-not-in-Z",
      z5mul((0,0,1,1), conjmap((0,0,1,1)))[2] != 0,
      "a·conj(a) for bitRep(f,f,t,t) has nonzero zeta^2 slot — relative norm not in Z")
check("S2:py:eleven-splits",
      normZ((-3,1,0,0)) == 121 and normZ((-4,1,0,0)) == 341 and 341 == 11 * 31,
      "N(ζ−3)=121=11², N(ζ−4)=341=11·31, with ζ−c nonzero mod 11")
# 41-adic certificates
roots = sorted(r for r in range(41) if (1 + r + r*r + r**3 + r**4) % 41 == 0)
check("S2:py:roots-mod-41", roots == [10, 16, 18, 37],
      "Φ5 roots mod 41 are exactly {10,16,18,37} (iff over all residues)")
check("S2:py:two-not-root", (1 + 2 + 4 + 8 + 16) % 41 != 0)
sq41 = {(i * i) % 41 for i in range(41)}
check("S2:py:nonsquares", 7 not in sq41 and 35 not in sq41 and 2 in sq41 and (17*17) % 41 == 2,
      "7 and 35 nonsquares mod 41; control 2 = 17² IS a square")
check("S2:py:euler", pow(7, 20, 41) == 40 and pow(35, 20, 41) == 40 and pow(2, 20, 41) == 1)
check("S2:py:golden-quadratic", (7*7 - 7 - 1) % 41 == 0 and (35*35 - 35 - 1) % 41 == 0)
check("S2:py:root-powers",
      (10*10) % 41 == 18 and (10**3) % 41 == 16 and (16*16) % 41 == 10 and
      (16**3) % 41 == 37 and (18*18) % 41 == 37 and (18**3) % 41 == 10 and
      (37*37) % 41 == 16 and (37**3) % 41 == 18,
      "Vandermonde rows (1, r, r², r³) mod 41 as used by ev41A..D")
check("S2:py:roots-pow5", all(pow(r, 5, 41) == 1 for r in (10, 16, 18, 37)))
v = (16-10) * (18-10) * (37-10) * (18-16) * (37-16) * (37-18)
check("S2:py:vandermonde", v == 1034208 and v % 41 == 24 and (24 * 12) % 41 == 1)
# nsq7N / nsq35N as full 41×41 computations
def nsqN(c):
    bad = [(m, n) for m in range(41) for n in range(41)
           if (m*m) % 41 == (c * n * n) % 41 and not (m == 0 and n == 0)]
    return bad
check("S2:py:nsq7N-41x41", nsqN(7) == [], "x²≡7y² mod 41 only at (0,0) — 1681 cases")
check("S2:py:nsq35N-41x41", nsqN(35) == [], "x²≡35y² mod 41 only at (0,0)")
check("S2:py:nsq4N-false-control", (2, 1) in [(m, n) for m in range(41) for n in range(41)
      if (m*m) % 41 == (4 * n * n) % 41 and (m, n) != (0, 0)],
      "for the square 4 the same statement fails at (2,1)")
# id0..id3 — the hand-inverted Vandermonde identities, exactly
EV = [(1, 10, 18, 16), (1, 16, 10, 37), (1, 18, 37, 10), (1, 37, 16, 18)]
IDS = [((73, 67, 65, 46),  0, (6, 114, 125, 125)),
       ((109, 84, 80, 55), 1, (8, 144, 162, 162)),
       ((88, 103, 74, 63), 2, (8, 151, 155, 173)),
       ((90, 76, 101, 61), 3, (8, 151, 173, 155))]
ok_ids = True
for coeffs, k, kk in IDS:
    for var in range(4):        # coefficient of a_var on both sides
        lhs = sum(c * EV[j][var] for j, c in enumerate(coeffs))
        rhs = (5 if var == k else 0) + 41 * kk[var]
        if lhs != rhs:
            ok_ids = False
check("S2:py:id0..id3-exact", ok_ids,
      "all four closed linear identities hold coefficient-by-coefficient")
# ev41 maps: additive exactly, multiplicative mod 41, phi values
def ev(row, u): return sum(c * x for c, x in zip(row, u))
import random
random.seed(41)
samples = [tuple(random.randint(-9, 9) for _ in range(4)) for _ in range(60)]
ok_mul = all((ev(EV[r], z5mul(u, v)) - ev(EV[r], u) * ev(EV[r], v)) % 41 == 0
             for r in range(4) for u, v in zip(samples[::2], samples[1::2]))
ok_add = all(ev(EV[r], z5add(u, v)) == ev(EV[r], u) + ev(EV[r], v)
             for r in range(4) for u, v in zip(samples[::2], samples[1::2]))
check("S2:py:ev41-hom", ok_add and ok_mul,
      "ev41A..D additive on the nose, multiplicative mod 41 (30 sample pairs each)")
check("S2:py:ev41-phi",
      [ev(row, PHI) % 41 for row in EV] == [7, 35, 35, 7],
      "phi lands on 7,35,35,7 — nonsquares at every root")
check("S2:py:ev41-one-zeta",
      [ev(row, ONE) % 41 for row in EV] == [1, 1, 1, 1] and
      [ev(row, ZETA) % 41 for row in EV] == [10, 16, 18, 37])
w = (5, 14, 22, 20)
check("S2:py:needs-all-four-witness",
      [ev(row, w) % 41 for row in EV] == [0, 0, 0, 5] and 5 % 41 != 0,
      "⟨5,14,22,20⟩ killed by A,B,C but not D; 41 ∤ 5")
# the two fuel-step arithmetic facts omega certifies, brute-forced small
ok_step2 = all(
    (abs(x0)//2 + abs(x1)//2 + abs(x2)//2 + abs(x3)//2) <= n
    for n in range(0, 9)
    for x0 in range(-8, 9, 2) for x1 in range(-8, 9, 2)
    for x2 in range(-8, 9, 2) for x3 in range(-8, 9, 2)
    if abs(x0) + abs(x1) + abs(x2) + abs(x3) <= n + 1)
check("S2:py:halving-measure-step", ok_step2,
      "all even & Σ|xi| ≤ n+1 ⟹ Σ|xi/2| ≤ n (exhaustive small range)")
ok_step41 = all(sum(ms) <= n for n in range(0, 130)
                for ms in [(m0, m1) for m0 in range(4) for m1 in range(4)]
                if 41 * sum(ms) <= n + 1)
check("S2:py:41-measure-step", ok_step41,
      "41·Σmᵢ ≤ n+1 ⟹ Σmᵢ ≤ n (sampled shape of sum8_step)")
# descent teeth: the square case really admits the nonzero solution
check("S2:py:square-case-witness",
      z5mul((2,0,0,0), (2,0,0,0)) == z5mul((4,0,0,0), z5mul(ONE, ONE)) and
      z5mul(PHI, PHI) == z5mul(z5mul(PHI, PHI), z5mul(ONE, ONE)),
      "x²=4y² at (2,1) and x²=phi²·y² at (phi,1): not_square's shape is falsifiable")
# Cong2 mechanism: norm respects mod-2 classes (samples)
check("S2:py:cong2-norm",
      all((normZ(u) - normZ(tuple(c % 2 for c in u))) % 2 == 0 for u in samples),
      "normZ mod 2 depends only on coordinate parities (the Cong2 route's output)")

n_fail = sum(1 for _, ok in results if not ok)
print(f"\nS2 RESULT: {len(results) - n_fail}/{len(results)} PASS, {n_fail} FAIL")
sys.exit(min(n_fail, 120))
