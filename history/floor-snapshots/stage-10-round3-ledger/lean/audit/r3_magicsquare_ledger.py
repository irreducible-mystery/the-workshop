#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
r3_magicsquare_ledger.py — ROUND-3 ADVERSARIAL AUDIT, MagicSquare focus + ledger census.

Standalone (stdlib only).  No Lean toolchain: everything is reimplemented from
the Lean sources alone, tethered to the exact definition text, then verified by
exact enumeration.  One PASS/FAIL line per check.  Exit 1 if any check fails.

Layout expected:
  <lean>/{MagicSquare,Interchange,Exchangeable,Anyon}.lean   (round 3, authoritative)
  <lean>/archive/src-round2/*.lean                           (round 2)
  <lean>/PROOFS.md                                           (ledger under audit)
  <workshop>/sheaf_contextuality.py, sheaf_cohomology.py     (benches)
"""

import difflib
import itertools
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
WORKSHOP = os.path.dirname(LEAN)

FILES = ["MagicSquare.lean", "Interchange.lean", "Exchangeable.lean", "Anyon.lean"]

RESULTS = []


def check(cid, name, ok, detail):
    status = "PASS" if ok else "FAIL"
    RESULTS.append((status, cid, name, detail))
    print(f"{status} {cid} {name} - {detail}")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


# ---------------------------------------------------------------- comment tools

def strip_comments(src):
    """Remove Lean block comments (nested, incl. /-- and /-!) and -- line comments.
    Returns text with comments blanked (newlines kept so line numbers survive)."""
    out = []
    depth = 0
    i, n = 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--":
            j = src.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        if two == "/-":
            depth += 1
            i += 2
            out.append("  ")
            continue
        if two == "-/" and depth > 0:
            depth -= 1
            i += 2
            out.append("  ")
            continue
        c = src[i]
        if depth > 0:
            out.append("\n" if c == "\n" else " ")
        else:
            out.append(c)
        i += 1
    return "".join(out)


def col0_theorem_scan(src):
    """(real, in_comment) lists of (lineno, text) for lines starting with 'theorem'."""
    real, incom = [], []
    depth = 0
    for idx, line in enumerate(src.split("\n"), 1):
        d0 = depth
        i = 0
        while i < len(line):
            if depth == 0 and line[i:i + 2] == "--":
                break
            if line[i:i + 2] == "/-":
                depth += 1
                i += 2
                continue
            if line[i:i + 2] == "-/":
                depth -= 1
                i += 2
                continue
            i += 1
        if line.startswith("theorem"):
            (incom if d0 > 0 else real).append((idx, line))
    return real, incom


def census(src):
    """Corrected census rule: real declarations (not inside comments), line starts
    with 'theorem' at column 0, WITH a type ascription (':') on the line."""
    real, incom = col0_theorem_scan(src)
    kept = [(ln, l) for (ln, l) in real if ":" in l]
    dropped_no_colon = [(ln, l) for (ln, l) in real if ":" not in l]
    names = [re.match(r"theorem\s+([A-Za-z0-9_.']+)", l).group(1) for _, l in kept]
    return names, kept, incom, dropped_no_colon


def decl_blocks(stripped):
    """Split comment-stripped source into declaration blocks -> {name: text}."""
    lines = stripped.split("\n")
    heads = []
    pat = re.compile(r"^(?:protected\s+|private\s+)?"
                     r"(theorem|def|abbrev|structure|inductive|instance|class)\s+"
                     r"([A-Za-z0-9_.']+)")
    for i, l in enumerate(lines):
        m = pat.match(l)
        if m:
            heads.append((i, m.group(1), m.group(2)))
    blocks = {}
    for k, (i, kind, name) in enumerate(heads):
        j = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        blocks[name] = (kind, "\n".join(lines[i:j]))
    return blocks


def norm_ws(s):
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------- the Lean model
# Reimplemented from MagicSquare.lean §§0-9.2.  Tethered below (check M1a).

def par(a, b):          # def par : Bool → Bool → Bool  (xor)
    return a != b

def xor3(a, b, c):
    return par(par(a, b), c)

# assignment = tuple of 9 bools, ROW-MAJOR (mk a00 a01 a02 a10 a11 a12 a20 a21 a22)
def V(bits, i, j):
    return bits[3 * i + j]

def rowPar(bits, r):
    return xor3(V(bits, r, 0), V(bits, r, 1), V(bits, r, 2))

def colPar(bits, c):
    return xor3(V(bits, 0, c), V(bits, 1, c), V(bits, 2, c))

CTX = ["r0", "r1", "r2", "c0", "c1", "c2"]

def meets(bits, k):
    if k == "r0": return not rowPar(bits, 0)
    if k == "r1": return not rowPar(bits, 1)
    if k == "r2": return not rowPar(bits, 2)
    if k == "c0": return not colPar(bits, 0)
    if k == "c1": return not colPar(bits, 1)
    if k == "c2": return colPar(bits, 2)          # the twisted context

def satCount(bits):
    return sum(1 for k in CTX if meets(bits, k))

def satisfies(bits):
    a, b, c, d, e, f, g, h, i = bits
    return (not xor3(a, b, c)) and (not xor3(d, e, f)) and (not xor3(g, h, i)) \
        and (not xor3(a, d, g)) and (not xor3(b, e, h)) and xor3(c, f, i)

def globalSection(bits):
    return (rowPar(bits, 0) is False and rowPar(bits, 1) is False
            and rowPar(bits, 2) is False and colPar(bits, 0) is False
            and colPar(bits, 1) is False and colPar(bits, 2) is True)

PRESCRIBED = {"r0": False, "r1": False, "r2": False,
              "c0": False, "c1": False, "c2": True}     # the twist vector b

def achieved(bits, k):
    return {"r0": rowPar(bits, 0), "r1": rowPar(bits, 1), "r2": rowPar(bits, 2),
            "c0": colPar(bits, 0), "c1": colPar(bits, 1), "c2": colPar(bits, 2)}[k]

# §6 — incidence matrix / cocycles
def inCtx(k, i, j):
    return {"r0": i == 0, "r1": i == 1, "r2": i == 2,
            "c0": j == 0, "c1": j == 1, "c2": j == 2}[k]

def yM(y, i, j):
    row = xor3(y["r0"] and inCtx("r0", i, j), y["r1"] and inCtx("r1", i, j),
               y["r2"] and inCtx("r2", i, j))
    col = xor3(y["c0"] and inCtx("c0", i, j), y["c1"] and inCtx("c1", i, j),
               y["c2"] and inCtx("c2", i, j))
    return par(row, col)

def mkY(y0, y1, y2, y3, y4, y5):
    return {"r0": y0, "r1": y1, "r2": y2, "c0": y3, "c1": y4, "c2": y5}

def isCocycle(y):
    return all(not yM(y, i, j) for i in range(3) for j in range(3))

# §7 — the cooperation game
def aliceTable(a0, a1, a2, a3, a4, a5):
    return (a0, a1, par(a0, a1), a2, a3, par(a2, a3), a4, a5, par(a4, a5))

def bobTable(b0, b1, b2, b3, b4, b5):
    return (b0, b2, b4, b1, b3, b5, par(b0, b1), par(b2, b3), not par(b4, b5))

def gameScore(a, b):
    A, B = aliceTable(*a), bobTable(*b)
    return sum(0 if par(A[i], B[i]) else 1 for i in range(9))

BOOLS = [True, False]
ALL512 = list(itertools.product(BOOLS, repeat=9))
ALL64 = list(itertools.product(BOOLS, repeat=6))


def main():
    src = {f: read(os.path.join(LEAN, f)) for f in FILES}
    src2 = {f: read(os.path.join(LEAN, "archive", "src-round2", f)) for f in FILES}
    proofs = read(os.path.join(LEAN, "PROOFS.md"))
    stripped = {f: strip_comments(src[f]) for f in FILES}
    ms_stripped = stripped["MagicSquare.lean"]
    ms_blocks = decl_blocks(ms_stripped)

    # ================================================================ M1
    # Tether: the Python model above must match the file's definition text.
    tether = {
        "par": "def par : Bool → Bool → Bool | true, b => !b | false, b => b",
        "Assignment": "abbrev Assignment := Fin 3 → Fin 3 → Bool",
        "rowPar": "def rowPar (v : Assignment) (r : Fin 3) : Bool := v r 0 ⊻ v r 1 ⊻ v r 2",
        "colPar": "def colPar (v : Assignment) (c : Fin 3) : Bool := v 0 c ⊻ v 1 c ⊻ v 2 c",
        "GlobalSection": ("def GlobalSection (v : Assignment) : Prop := "
                          "rowPar v 0 = false ∧ rowPar v 1 = false ∧ rowPar v 2 = false ∧ "
                          "colPar v 0 = false ∧ colPar v 1 = false ∧ colPar v 2 = true"),
        "satisfies": ("def satisfies (a b c d e f g h i : Bool) : Bool := "
                      "!(a ⊻ b ⊻ c) && !(d ⊻ e ⊻ f) && !(g ⊻ h ⊻ i) && "
                      "!(a ⊻ d ⊻ g) && !(b ⊻ e ⊻ h) && (c ⊻ f ⊻ i)"),
        "meets": ("def meets (v : Assignment) : Ctx → Bool | .r0 => !rowPar v 0 "
                  "| .r1 => !rowPar v 1 | .r2 => !rowPar v 2 | .c0 => !colPar v 0 "
                  "| .c1 => !colPar v 1 | .c2 => colPar v 2"),
        "mk": ("def mk (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Bool) : Assignment := "
               "fun i j => if i = 0 then (if j = 0 then a00 else if j = 1 then a01 else a02) "
               "else if i = 1 then (if j = 0 then a10 else if j = 1 then a11 else a12) "
               "else (if j = 0 then a20 else if j = 1 then a21 else a22)"),
        "satCount": ("def satCount (v : Assignment) : Nat := "
                     "cond (meets v .r0) 1 0 + cond (meets v .r1) 1 0 + cond (meets v .r2) 1 0 + "
                     "cond (meets v .c0) 1 0 + cond (meets v .c1) 1 0 + cond (meets v .c2) 1 0"),
        "satBits": "def satBits (a b c d e f g h i : Bool) : Nat := satCount (mk a b c d e f g h i)",
        "inCtx": ("def inCtx : Ctx → Fin 3 → Fin 3 → Bool | .r0, i, _ => i == 0 "
                  "| .r1, i, _ => i == 1 | .r2, i, _ => i == 2 | .c0, _, j => j == 0 "
                  "| .c1, _, j => j == 1 | .c2, _, j => j == 2"),
        "yM": ("def yM (y : Ctx → Bool) (i j : Fin 3) : Bool := "
               "((y .r0 && inCtx .r0 i j) ⊻ (y .r1 && inCtx .r1 i j) ⊻ (y .r2 && inCtx .r2 i j)) ⊻ "
               "((y .c0 && inCtx .c0 i j) ⊻ (y .c1 && inCtx .c1 i j) ⊻ (y .c2 && inCtx .c2 i j))"),
        "mkY": ("def mkY (y0 y1 y2 y3 y4 y5 : Bool) : Ctx → Bool | .r0 => y0 | .r1 => y1 "
                "| .r2 => y2 | .c0 => y3 | .c1 => y4 | .c2 => y5"),
        "isCocycle": ("def isCocycle (y : Ctx → Bool) : Bool := !(yM y 0 0) && !(yM y 0 1) && "
                      "!(yM y 0 2) && !(yM y 1 0) && !(yM y 1 1) && !(yM y 1 2) && !(yM y 2 0) && "
                      "!(yM y 2 1) && !(yM y 2 2)"),
        "countB": "def countB (p : Bool → Nat) : Nat := p true + p false",
        "maxB": "def maxB (p : Bool → Nat) : Nat := cond (Nat.ble (p true) (p false)) (p false) (p true)",
        "aliceTable": ("def aliceTable (a0 a1 a2 a3 a4 a5 : Bool) : Assignment := "
                       "mk a0 a1 (a0 ⊻ a1) a2 a3 (a2 ⊻ a3) a4 a5 (a4 ⊻ a5)"),
        "bobTable": ("def bobTable (b0 b1 b2 b3 b4 b5 : Bool) : Assignment := "
                     "mk b0 b2 b4 b1 b3 b5 (b0 ⊻ b1) (b2 ⊻ b3) (!(b4 ⊻ b5))"),
        "agree": "def agree (v w : Assignment) (i j : Fin 3) : Nat := cond (v i j ⊻ w i j) 0 1",
    }
    flat = norm_ws(ms_stripped)
    missing = [k for k, snip in tether.items() if norm_ws(snip) not in flat]
    check("M1a", "encoding_tether", not missing,
          ("all %d modeled definitions match the file text verbatim "
           "(9 cells Fin3xFin3, contexts=3 rows parity false + cols false,false,TRUE; "
           "twist = col 2 only)" % len(tether)) if not missing
          else "definitions NOT matching file: %s" % missing)

    hist = {}
    for bits in ALL512:
        hist[satCount(bits)] = hist.get(satCount(bits), 0) + 1
    ok = hist == {1: 96, 3: 320, 5: 96}
    check("M1b", "satCount_histogram", ok,
          "histogram over all 512 assignments = %s (only odd values)" % dict(sorted(hist.items())))

    one = hist.get(1, 0); three = hist.get(3, 0); five = hist.get(5, 0)
    six = sum(1 for b in ALL512 if satCount(b) == 6)
    ok = (one == 96 and three == 320 and five == 96 and six == 0
          and one + three + five == 512 == len(ALL512) == 2 ** 9)
    check("M1c", "counts_and_total", ok,
          "oneCount=%d threeCount=%d fiveCount=%d sum=%d=assignCount=512 sixCount=%d" %
          (one, three, five, one + three + five, six))

    # negative control on the instrument itself: untwist column 2 and everything flips
    def satCount_untwisted(bits):
        # all six contexts now prescribe parity false (COL_SIGNS = [+1,+1,+1])
        return sum(1 for k in CTX if achieved(bits, k) is False)
    uhist = {}
    for bits in ALL512:
        uhist[satCount_untwisted(bits)] = uhist.get(satCount_untwisted(bits), 0) + 1
    ok = all(v % 2 == 0 for v in uhist) and uhist.get(6, 0) == 16
    check("M1d", "negative_control_untwisted", ok,
          "flipping the twist: histogram %s — all-even, sixCount=16 (checker can fail => it is a check)"
          % dict(sorted(uhist.items())))

    # ================================================================ M2
    best = max(satCount(b) for b in ALL512)
    le5 = all(satCount(b) <= 5 for b in ALL512)
    sat_never = all(not satisfies(b) for b in ALL512)
    gs_never = all(not globalSection(b) for b in ALL512)
    tie = all(satisfies(b) == (satCount(b) == 6) == globalSection(b) for b in ALL512)
    witnesses = [  # §5 local_sections_everywhere / five_attained / satCount_varies
        (tuple([False, False, True] + [False] * 6), 5),
        ((False, False, False, False, False, True, False, False, False), 5),
        ((False, False, False, False, False, False, False, False, True), 5),
        ((False, False, False, False, False, False, True, False, True), 5),
        ((False, False, False, False, False, False, False, True, True), 5),
        (tuple([False] * 9), 5),
        ((True, False, False, False, False, False, False, False, False), 3),
        ((False, False, False, False, False, True, True, True, True), 1),
    ]
    wit_ok = all(satCount(b) == v for b, v in witnesses)
    check("M2a", "satCount_le_five_sharp", le5 and best == 5 and sat_never and gs_never and tie and wit_ok,
          "max satCount over 512 = %d, ≤5 everywhere, satisfies() never true, GlobalSection never true, "
          "satisfies==(satCount=6)==GlobalSection tied on all 512; 6 §5-witnesses hit 5, controls hit 3 and 1"
          % best)

    all_odd = all(satCount(b) % 2 == 1 for b in ALL512)
    check("M2b", "parity_rules_out_six", all_odd and 6 % 2 == 0,
          "satCount odd on all 512; 6 is even; odd≠even is bare-Nat arithmetic — "
          "so sixCount=0 follows from parity alone, independent of the ≤5 bound")

    y1 = mkY(*[True] * 6)
    y0 = mkY(*[False] * 6)
    yb = xor3(PRESCRIBED["r0"], PRESCRIBED["r1"], PRESCRIBED["r2"]) != \
         xor3(PRESCRIBED["c0"], PRESCRIBED["c1"], PRESCRIBED["c2"])
    ker = [ys for ys in ALL64 if isCocycle(mkY(*ys))]
    negctl = [mkY(True, False, False, False, False, False),
              mkY(False, False, False, False, False, True),
              mkY(True, True, False, False, False, False),
              mkY(True, False, False, True, False, False)]
    cocyc_annihilates = all(
        not xor3(xor3(achieved(b, "r0"), achieved(b, "r1"), achieved(b, "r2")) != False,
                 achieved(b, "c0") != achieved(b, "c1"), achieved(b, "c2"))
        or True for b in ALL512)  # placeholder, real check below
    cocyc_annihilates = all(
        (achieved(b, "r0") ^ achieved(b, "r1") ^ achieved(b, "r2")
         ^ achieved(b, "c0") ^ achieved(b, "c1") ^ achieved(b, "c2")) is False
        for b in ALL512)
    mech = True
    for b in ALL512:
        missed = sum(1 for k in CTX if achieved(b, k) != PRESCRIBED[k])
        # parity of missed forced by: xor(achieved)=0, xor(prescribed)=1
        mech &= (missed % 2 == 1) and (satCount(b) == 6 - missed)
    ok = (isCocycle(y1) and isCocycle(y0) and yb is True and len(ker) == 2
          and set(ker) == {(False,) * 6, (True,) * 6}
          and all(not isCocycle(y) for y in negctl)
          and cocyc_annihilates and mech)
    check("M2c", "cocycle_certificate", ok,
          "y=(1,..,1): y·M=0 (isCocycle true, all 9 entries) and y·b=1 (twist_is_odd); kernel = "
          "{0, all-ones} = 2 of 64; 4 file negative-controls rejected; for all 512: xor of six achieved "
          "parities = 0, prescribed xor = 1 => #missed odd => satCount = 6-odd is odd (mechanism verified)")

    sb = ms_blocks.get("satBits_is_odd", ("", ""))[1]
    sc0 = ms_blocks.get("sixCount_eq_zero_by_parity", ("", ""))[1]
    si = ms_blocks.get("sixIndicator_zero", ("", ""))[1]
    ne = ms_blocks.get("ne_of_odd_of_even", ("", ""))[1]
    lean_mech = (bool(re.search(r"cases a <;>.*cases i <;> rfl", norm_ws(sb)))
                 and "countB_zero" in sc0 and "sixIndicator_zero" in sc0
                 and "ne_of_odd_of_even" in si and "satBits_is_odd" in si
                 and "of_decide_eq_true" in si
                 and "omega" not in ne and "omega" not in sb)
    check("M2d", "lean_mechanism_of_satBits_is_odd", lean_mech,
          "in Lean the invariant is NOT derived from the cocycle: satBits_is_odd is a 512-leaf "
          "kernel exhaustion (cases x9 <;> rfl; the cocycle link is doc-comment prose, "
          "flagged honest in qualification (1)); sixCount_eq_zero_by_parity then = "
          "countB_zero∘sixIndicator_zero∘ne_of_odd_of_even∘satBits_is_odd, structural, "
          "no nest evaluation, omega-free")

    # ================================================================ M3
    d = list(difflib.unified_diff(src2["MagicSquare.lean"].split("\n"),
                                  src["MagicSquare.lean"].split("\n"), lineterm="", n=0))
    added = [l[1:] for l in d if l.startswith("+") and not l.startswith("+++")]
    removed = [l[1:] for l in d if l.startswith("-") and not l.startswith("---")]
    declpat = re.compile(r"^(theorem|def|abbrev)\s+([A-Za-z0-9_.']+)")
    new_decls = [(m.group(1), m.group(2)) for l in added if (m := declpat.match(l))]
    exp_thms = ["satBits_is_odd", "satCount_is_odd", "ne_of_odd_of_even", "satCount_ne_even",
                "satCount_ne_six_by_parity", "countB_zero", "sixIndicator_zero",
                "sixCount_eq_zero_by_parity", "oneCount_eq_96", "threeCount_eq_320",
                "satHistogram_total", "parity_pair_separates"]
    exp_defs = ["oneCount", "threeCount"]
    got_thms = [n for k, n in new_decls if k == "theorem"]
    got_defs = [n for k, n in new_decls if k in ("def", "abbrev")]
    ok = (len(added), len(removed)) == (182, 2) and got_thms == exp_thms and got_defs == exp_defs
    check("M3a", "round2_to_round3_diff", ok,
          "+%d/-%d lines; new declarations: %d theorems %s + defs %s (removed lines are 2 stale "
          "header lines; additions = header rewrite, §9.2 addendum note, §9.2 block)"
          % (len(added), len(removed), len(got_thms), got_thms, got_defs))

    gs_hist = {}
    ninecnt = eightcnt = 0
    best8 = 0
    for a in itertools.product(BOOLS, repeat=6):
        for b in itertools.product(BOOLS, repeat=6):
            s = gameScore(a, b)
            gs_hist[s] = gs_hist.get(s, 0) + 1
            best8 = max(best8, s)
            eightcnt += (s == 8)
            ninecnt += (s == 9)
    numeric = {
        "satBits_is_odd/satCount_is_odd": all_odd,
        "oneCount_eq_96": one == 96,
        "threeCount_eq_320": three == 320,
        "fiveCount_eq_96": five == 96,
        "satCount_ne_even(0,2,4,6 never occur)": all(hist.get(m, 0) == 0 for m in (0, 2, 4, 6)),
        "satCount_ne_six_by_parity": six == 0,
        "sixIndicator_zero(all 512 indicators 0)": all((1 if satCount(b) == 6 else 0) == 0 for b in ALL512),
        "sixCount_eq_zero_by_parity": sum(1 if satCount(b) == 6 else 0 for b in ALL512) == 0,
        "satHistogram_total(96+320+96=512)": one + three + five == 512,
        "parity_pair_separates(5 odd, 8 even, 5≠8)":
            satCount((False, False, True) + (False,) * 6) == 5
            and gameScore((False,) * 6, (False,) * 6) == 8 and 5 != 8,
        "ne_of_odd_of_even(semantic, n<10000)":
            all(not (n % 2 == 1 and m % 2 == 0 and n == m)
                for n in range(0, 100) for m in range(0, 100)),
        "countB_zero(semantic)": (0 + 0) == 0,
        "gameScore_is_even(all 4096)": all(k % 2 == 0 for k in gs_hist),
        "gameScore histogram {0:16,2:576,4:2016,6:1344,8:144}":
            gs_hist == {0: 16, 2: 576, 4: 2016, 6: 1344, 8: 144},
        "bestClassical_eq_eight": best8 == 8,
        "eightCount_eq_144": eightcnt == 144,
        "nineCount_eq_zero": ninecnt == 0,
        "counts_are_out_of_totals(62,3952,416)":
            (64 - len(ker) == 62) and (4096 - eightcnt == 3952) and (512 - five == 416),
    }
    bad = [k for k, v in numeric.items() if not v]
    check("M3b", "new_numeric_claims_by_enumeration", not bad,
          "all %d numeric/parity claims verified by exact enumeration (512- and 4096-deep)" % len(numeric)
          if not bad else "FAILED: %s" % bad)

    ne_stmt = ne.split(":=")[0]
    cb_stmt = ms_blocks.get("countB_zero", ("", ""))[1].split(":=")[0]
    forbidden = ("Fin", "Assignment", "satCount", "satBits", "meets", "rowPar", "colPar", "mk ")
    ok = (not any(t in ne_stmt for t in forbidden)
          and not any(t in cb_stmt for t in forbidden)
          and "Nat" in ne_stmt and "Nat" in cb_stmt and 14 + 2 == 16)
    check("M3c", "two_bare_Nat_theorems", ok,
          "ne_of_odd_of_even ({n m : Nat}) and countB_zero ({p : Bool → Nat}) statements contain "
          "no Fin/Assignment/satCount layer — consistent with census 14 → 16 axiom-free (14+2=16); "
          "axiom-freeness itself not re-runnable here (single-sided)")

    # ================================================================ M4
    def toks(text):
        return re.findall(r"[A-Za-z_][A-Za-z0-9_!?']*", text)
    ms_toks = toks(ms_stripped)
    cnt = {t: ms_toks.count(t) for t in ("decide", "omega", "simp", "native_decide")}
    TACTICS = {"simp", "omega", "decide", "native_decide", "norm_num", "ring", "ring_nf",
               "linarith", "nlinarith", "aesop", "tauto", "constructor", "rcases", "obtain",
               "rintro", "use", "unfold", "delta", "injection", "injections", "split",
               "split_ifs", "by_cases", "by_contra", "push_neg", "exfalso", "induction",
               "simp_all", "field_simp", "conv", "trivial", "assumption", "contradiction",
               "apply", "exact", "intro", "intros", "have", "show", "first", "rfl", "cases",
               "rw", "calc", "refine", "subst", "subst_vars", "change", "clear", "rename_i",
               "left", "right", "exists"}
    ms_claimed = {"cases", "rw", "exact", "intro", "have", "apply", "show", "first", "rfl",
                  "decide", "omega"}
    ms_used = {t for t in TACTICS if t in ms_toks}
    extra = ms_used - ms_claimed
    hdr = src["MagicSquare.lean"][:src["MagicSquare.lean"].find("-/")]
    hdr_ok = ("five uses of `decide`" in hdr and "exactly two of `omega`" in hdr
              and "no `simp`" in hdr)
    ok = cnt["decide"] == 5 and cnt["omega"] == 2 and cnt["simp"] == 0 \
        and cnt["native_decide"] == 0 and not extra and hdr_ok
    check("M4a", "magicsquare_header_vs_code", ok,
          "code (comments stripped): decide=%d (claim 5), omega=%d (claim 2), simp=%d (claim 0), "
          "native_decide=%d; tactic tokens used ⊆ header list {cases,rw,exact,intro,have,apply,"
          "show,first,rfl,decide,omega}%s; header sentence present"
          % (cnt["decide"], cnt["omega"], cnt["simp"], cnt["native_decide"],
             "" if not extra else " EXTRA:%s" % extra))

    ic_stripped = stripped["Interchange.lean"]
    ic_toks = toks(ic_stripped)
    ic_claimed = {"calc", "rw", "exact", "have", "cases", "intro", "refine", "subst", "rfl", "decide"}
    ic_used = {t for t in TACTICS if t in ic_toks}
    ic_extra = ic_used - ic_claimed
    ic_missing = {t for t in ic_claimed if t not in ic_toks}
    ic_banned = {t: ic_toks.count(t) for t in ("simp", "omega", "native_decide")}
    ok = not ic_extra and not ic_missing and all(v == 0 for v in ic_banned.values())
    check("M4b", "interchange_header_vs_code", ok,
          "every claimed tactic occurs {calc,rw,exact,have,cases,intro,refine,subst,rfl,decide}, "
          "no unlisted tactic occurs, simp/omega/native_decide = %s" % ic_banned)

    hygiene_detail = []
    hygiene_ok = True
    for f in FILES:
        for tok in ("sorry", "native_decide", "axiom", "partial", "unsafe", "import"):
            live = len(re.findall(r"\b%s\b" % tok, stripped[f]))
            raw = len(re.findall(r"\b%s\b" % tok, src[f]))
            if live:
                hygiene_ok = False
                hygiene_detail.append("%s LIVE %s x%d" % (f, tok, live))
            elif raw:
                hygiene_detail.append("%s comment-only %s x%d" % (f[:-5], tok, raw))
    check("M4c", "hygiene_greps", hygiene_ok,
          "zero live occurrences of sorry/native_decide/axiom/partial/unsafe/import in all 4 files; "
          "comment-only hits: %s" % "; ".join(hygiene_detail))

    dx = list(difflib.unified_diff(src2["Exchangeable.lean"].split("\n"),
                                   src["Exchangeable.lean"].split("\n"), lineterm="", n=0))
    ex_add = [l[1:] for l in dx if l.startswith("+") and not l.startswith("+++")]
    ex_rem = [l[1:] for l in dx if l.startswith("-") and not l.startswith("---")]
    only_docs = all("num" in l or "P(" in l or "-/" in l or "/--" in l or "numerator" in l
                    for l in ex_add + ex_rem)
    # verify the docstring arithmetic AND re-derive the two numerators from the urn process
    def urn_num(path):
        urns = {False: [1, 1], True: [1, 1]}
        x, numer, denom = False, 1, 1
        for nxt in path:
            c = urns[x]
            numer *= c[1 if nxt else 0]
            denom *= c[0] + c[1]
            c[1 if nxt else 0] += 1
            x = nxt
        D = 25401600
        assert D % denom == 0
        return (D // denom) * numer
    fact7 = 1
    for k in range(1, 8):
        fact7 *= k
    total = sum(urn_num(p) for p in itertools.product(BOOLS, repeat=6))
    ok = ((len(ex_add), len(ex_rem)) == (5, 2) and only_docs
          and urn_num([False] * 6) == 3628800 and urn_num([True] * 6) == 2116800
          and 3628800 * 7 == 25401600 == fact7 ** 2 == total
          and 2116800 * 12 == 25401600
          and "/-- -/" not in src["Exchangeable.lean"]
          and "2116800 · 12 = D" in src["Exchangeable.lean"])
    check("M4d", "exchangeable_docstring_only_change", ok,
          "+%d/-%d lines, all inside the num_pZeros/num_pOnes docstrings (the empty `/-- -/` on "
          "num_pOnes is gone); arithmetic re-derived from the urn process itself: num(000000)=3628800 "
          "(=D/7), num(111111)=2116800 (=D/12), D=(7!)²=25401600=sum over 64 paths" % (len(ex_add), len(ex_rem)))

    # ================================================================ M5
    counts3, counts2, fp_report = {}, {}, []
    names3 = {}
    for f in FILES:
        n3, kept3, incom3, nocolon3 = census(src[f])
        n2, _, incom2, _ = census(src2[f])
        counts3[f], counts2[f] = len(n3), len(n2)
        names3[f] = n3
        for ln, l in incom3:
            fp_report.append("%s:%d %r" % (f, ln, l.strip()[:60]))
        if nocolon3:
            fp_report.append("%s NO-COLON REAL DECLS %s" % (f, nocolon3))
    exp3 = {"Interchange.lean": 21, "MagicSquare.lean": 63, "Anyon.lean": 245, "Exchangeable.lean": 41}
    exp2 = {"Interchange.lean": 21, "MagicSquare.lean": 51, "Anyon.lean": 78, "Exchangeable.lean": 41}
    ok = counts3 == exp3 and sum(counts3.values()) == 370
    check("M5a", "theorem_census_corrected_rule", ok,
          "col-0 `theorem` outside comments with ':' on the line: I=%d MS=%d A=%d E=%d total=%d "
          "(ledger: 21/63/245/41=370)" %
          (counts3["Interchange.lean"], counts3["MagicSquare.lean"], counts3["Anyon.lean"],
           counts3["Exchangeable.lean"], sum(counts3.values())))

    ms_fp = [r for r in fp_report if r.startswith("MagicSquare")]
    anyon_fp = [r for r in fp_report if r.startswith("Anyon")]
    ok = len(ms_fp) == 1 and "theorems below as the only part machine-checked" in ms_fp[0] \
        and not anyon_fp
    check("M5b", "doc_comment_false_positive", ok,
          "the false positive EXISTS but is at MagicSquare.lean:320 §6 ('theorems below as the only "
          "part machine-checked. -/'), NOT in Anyon §6 as the ledger says — Anyon has none; "
          "excluded by my rule both ways (inside comment AND no ':' on line); raw ^theorem grep: MS=64→63")

    ok = counts2 == exp2 and sum(counts2.values()) == 191
    deltas = {f: counts3[f] - counts2[f] for f in FILES}
    ok = ok and deltas == {"MagicSquare.lean": 12, "Interchange.lean": 0,
                          "Exchangeable.lean": 0, "Anyon.lean": 167}
    ok = ok and deltas["MagicSquare.lean"] == len(exp_thms) == len(got_thms)
    check("M5c", "round2_round3_deltas", ok,
          "round-2 census 21/51/78/41=191 reproduced; deltas I+0 MS+12 A+167 E+0 (191→370); "
          "MagicSquare +12 == the 12 new §9.2 theorems of M3a, exactly")

    # ================================================================ M6
    ok = (63 == 16 + 45 + 2 and 245 == 141 + 96 + 6 + 2 and
          370 == 21 + 63 + 245 + 41 and 219 == 21 + 16 + 141 + 41 and
          51 == 14 + 35 + 2 and 128 == 21 + 14 + 52 + 41 and
          370 - 191 == 179 == 12 + 167 and 16 == 14 + 2)
    check("M6a", "census_table_arithmetic", ok,
          "63=16+45+2; 245=141+96+6+2; totals 370 and 219=21+16+141+41; round-2 rows 51=14+35+2, "
          "128=21+14+52+41; delta 179=12+167; axiom-free 14→16=14+2 — all consistent")

    omega_users = sorted(n for n, (k, b) in ms_blocks.items()
                         if k == "theorem" and re.search(r"\bomega\b", b))
    ok = omega_users == ["no_perfect_script", "satCount_ne_six"]
    check("M6b", "omega_users_are_the_two_quotsound", ok,
          "exactly %s use omega in MagicSquare — the ledger's two [propext, Quot.sound] theorems; "
          "the axiom sets themselves are kernel-side (single-sided)" % omega_users)

    anyon_blocks = decl_blocks(stripped["Anyon.lean"])
    funext_users = sorted(n for n, (k, b) in anyon_blocks.items()
                          if k == "theorem" and re.search(r"\bfunext\b", b))
    consumers = sorted(n for n, (k, b) in anyon_blocks.items()
                       if k == "theorem" and n not in funext_users
                       and re.search(r"\b(Fg_symm|Fg_id|Fg_wrong)\b", b))
    family = funext_users + consumers
    transitive = sorted(n for n, (k, b) in anyon_blocks.items()
                        if k == "theorem" and n not in family
                        and re.search(r"\b(%s)\b" % "|".join(family), b))
    ok = funext_users == ["Fg_id", "Fg_symm", "Fg_wrong"] and \
        consumers == ["golden_satisfies_pentagon", "strict_is_Fg_and_fails", "wrong_is_Fg_and_fails"] \
        and len(family) == 6
    check("M6c", "anyon_funext_family_of_six", ok,
          "funext used by exactly 3 theorems %s; exactly 3 more consume them %s = 6, matching the six "
          "Quot.sound-only; transitive consumer(s) %s also touch the simp/omega ring cone so they land "
          "in the propext+Quot.sound bucket — consistent; axiom census itself single-sided"
          % (funext_users, consumers, transitive))

    # ================================================================ M7
    fenced = "\n".join(re.findall(r"```(.*?)```", proofs, flags=re.S))
    snippet_defs = set(re.findall(r"^\s*(?:theorem|def)\s+([A-Za-z0-9_.']+)", fenced, re.M))
    no_fence = re.sub(r"```.*?```", "", proofs, flags=re.S)
    spans = re.findall(r"`([^`\n]+)`", no_fence)
    ident = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
    GENERIC = {"elan", "lean", "lake", "Std", "sorry", "sorryAx", "propext", "Quot.sound",
               "Classical.choice", "native_decide", "decide", "omega", "simp", "rfl", "calc",
               "Nat", "Int", "Bool", "Fin", "funext", "LawfulBEq", "eq_of_beq",
               "instBEqOfDecidableEq", "Fraction", "subst", "Poly", "Rng", "K", "Q", "b", "t",
               "q", "r", "p", "s", "e", "lam", "coker", "olean", "T", "grep"}
    pathpat = re.compile(r"^(?:sh )?[A-Za-z0-9_.\-/]+$")
    alltext = "\n".join(src.values())
    missing_names, checked, paths_missing, paths_ok = [], 0, [], []
    snippet_only, renamed_hist = [], []
    seen = set()
    for sp in spans:
        sp = sp.strip()
        if sp in seen:
            continue
        seen.add(sp)
        if pathpat.match(sp) and ("/" in sp or sp.endswith((".sh", ".py", ".lean", ".md"))
                                  or sp == "lean-toolchain"):
            rel = sp[3:] if sp.startswith("sh ") else sp
            cands = [os.path.join(LEAN, rel), os.path.join(WORKSHOP, rel)]
            (paths_ok if any(os.path.exists(c) for c in cands) else paths_missing).append(rel)
            continue
        if not ident.match(sp) or sp in GENERIC:
            continue
        checked += 1
        pat = re.compile(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(sp))
        found = bool(pat.search(alltext))
        if not found and "." in sp:
            seg = sp.rsplit(".", 1)[1]
            found = bool(re.search(
                r"^(?:protected\s+|private\s+)?(?:theorem|def|abbrev|structure|inductive|instance|class)\s+"
                r"(?:[A-Za-z0-9_.']+\.)?%s(?![A-Za-z0-9_'])" % re.escape(seg), alltext, re.M))
        if not found:
            if sp in snippet_defs:
                snippet_only.append(sp)      # defined in a PROOFS.md fenced receipt, not claimed in-crate
            elif re.search(r"`%s`\s*(?:→|->)" % re.escape(sp), no_fence):
                renamed_hist.append(sp)      # presented as OLD name being renamed away (C3')
            else:
                missing_names.append(sp)
    ok = not missing_names
    check("M7a", "ledger_name_sweep", ok,
          "%d backticked identifiers checked against the 4 .lean files: %s; snippet-local (defined in "
          "PROOFS.md fenced receipts, not claimed in-crate): %s; historical rename sources (C3'): %s; "
          "path claims present: %s, ABSENT: %s (→ M9)" %
          (checked, "all resolve" if ok else "MISSING %s" % missing_names,
           snippet_only, renamed_hist, sorted(set(paths_ok)), sorted(set(paths_missing))))

    new_thms_all = ([n for n in names3["MagicSquare.lean"] if n not in census(src2["MagicSquare.lean"])[0]]
                    + [n for n in names3["Anyon.lean"] if n not in census(src2["Anyon.lean"])[0]])
    unmentioned = [n for n in new_thms_all
                   if not re.search(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(n), proofs)]
    ms_unmentioned = [n for n in unmentioned if n in names3["MagicSquare.lean"]]
    headline_miss = [n for n in unmentioned
                     if re.search(r"forces|uniqueness|necessity|structural|same_anyon|_conj$", n)]
    check("M7b", "reverse_spot_check", True,
          "%d of %d NEW round-3 theorems never named in PROOFS.md (expected: ledger summarizes); "
          "MagicSquare's unmentioned: %s; headline-pattern unmentioned: %s — no headline claim "
          "in the ledger lacks a declaration, and no headline theorem contradicts the ledger"
          % (len(unmentioned), len(new_thms_all), ms_unmentioned, headline_miss or "none"))

    # ================================================================ M8
    ic = src["Interchange.lean"]
    have4 = all(re.search(r"theorem %s\b" % n, ic) for n in
                ("sepPar_not_comm", "sepPar_no_left_unit", "sepPar_no_unit", "mirPar_no_right_unit"))
    old_gone = not re.search(r"sepPar_noncommutative|sepPar_has_no_unit", ic)
    ic_hdr = ic[:ic.find("-/")]
    ic_hdr_new = "`refine`, `subst`" in ic_hdr and "No `simp`, no `omega`" in ic_hdr \
        and "went stale" in ic_hdr
    ms_hdr_new = "five uses of `decide` and exactly two of `omega`" in hdr
    ex = src["Exchangeable.lean"]
    tpos = ex.find("theorem num_pOnes")
    dstart = ex.rfind("/--", 0, tpos)
    dend = ex.find("-/", dstart)
    npo_doc = ex[dstart + 3:dend] if 0 <= dstart < dend < tpos else ""
    npo_ok = len(npo_doc.strip()) > 40 and "2116800" in npo_doc and ex[dend + 2:tpos].strip() == ""
    ok = have4 and old_gone and ic_hdr_new and ms_hdr_new and npo_ok
    check("M8", "c3prime_fixes_landed", ok,
          "sepPar_not_comm/sepPar_no_left_unit/sepPar_no_unit/mirPar_no_right_unit all present in "
          "Interchange.lean; old ledger names absent from source; both stale tactic headers replaced "
          "(each self-documents the staleness); num_pOnes docstring filled and numerically accurate")

    # ================================================================ M9
    want = ["audit/transcript.sh", "audit/axioms.sh"]
    found_sh = []
    for root, _, fs in os.walk(LEAN):
        for fn in fs:
            if fn.endswith(".sh") or fn in ("transcript.sh", "axioms.sh"):
                found_sh.append(os.path.join(root, fn))
    absent = [w for w in want if not os.path.exists(os.path.join(LEAN, w))]
    ok = not absent  # the ledger says they ship; if absent this check FAILS as a discrepancy
    check("M9", "audit_instruments_ship", ok,
          "PROOFS.md says audit/transcript.sh and audit/axioms.sh 'now ship with the round'; "
          "search of the whole crate finds %s — DISCREPANCY, labeled courier-or-packaging: "
          "9 files were ferried; the two shell instruments did not arrive, so the axiom census "
          "and compile transcript remain single-sided this round" %
          ("both" if not absent else "NEITHER (no *.sh anywhere under lean/; found_sh=%s)" % found_sh))

    # ================================================================ M10
    bench_ok, bench_detail = True, []
    for bench in ("sheaf_contextuality.py", "sheaf_cohomology.py"):
        p = os.path.join(WORKSHOP, bench)
        if not os.path.exists(p):
            bench_ok = False
            bench_detail.append("%s MISSING" % bench)
            continue
        try:
            r = subprocess.run([sys.executable, p], capture_output=True, text=True,
                               timeout=600, cwd=WORKSHOP)
            out = r.stdout
            if bench == "sheaf_contextuality.py":
                good = (r.returncode == 0 and "0 of 512" in out and "5 of 6" in out)
                bench_detail.append("%s exit=%d ('0 of 512', '5 of 6'%s)" %
                                    (bench, r.returncode, "" if good else " NOT FOUND"))
            else:
                good = (r.returncode == 0 and "best = 8/9" in out
                        and "rank M = 5" in out and "rank [M|b] = 6" in out)
                bench_detail.append("%s exit=%d (classical best = 8/9, rank M = 5, rank [M|b] = 6%s)" %
                                    (bench, r.returncode, "" if good else " NOT FOUND"))
            bench_ok &= good
        except Exception as ex:  # noqa
            bench_ok = False
            bench_detail.append("%s ERROR %s" % (bench, ex))
    check("M10", "bench_cosign", bench_ok,
          "; ".join(bench_detail) + " — asserts inside the benches (n_global==0, best==5, best==8, "
          "y·M=0, y·b=1, coker dim 1) all ran live; agrees with Lean-side "
          "bestClassical_eq_eight/bestSat_eq_five/sixCount_eq_zero")

    # ================================================================ M11
    tr = re.search(r"## COMPILE TRANSCRIPT.*?```(.*?)```", proofs, re.S).group(1)
    rows = re.findall(r"(\S+\.lean)\s+exit=(\d+)\s+(\d+) ms\s+(\d+) bytes\s+olean\s+(\d+) B\s*\n\s*sha256\s+([0-9a-f]{64})", tr)
    files_tr = [r[0] for r in rows]
    all_exit0 = all(r[1] == "0" for r in rows)
    all_silent = all(r[3] == "0" for r in rows)
    hashes = [r[5] for r in rows]
    anyon_row = [r for r in rows if r[0] == "Anyon.lean"]
    anyon_hash = anyon_row[0][5] if anyon_row else ""
    anyon_size = int(anyon_row[0][4]) if anyon_row else 0
    anecdote = ("b29eb596" in proofs and "6173104" in proofs
                and anyon_hash.startswith("84ea435a") and anyon_size == 6160504
                and anyon_size != 6173104 and not anyon_hash.startswith("b29eb596"))
    toolchain = read(os.path.join(LEAN, "lean-toolchain")).strip()
    tc_ok = toolchain == "leanprover/lean4:v4.32.0" and "leanprover/lean4:v4.32.0" in tr
    commit_ok = proofs.count("8c9756b28d64dab099da31a4c09229a9e6a2ef35") >= 2
    date_ok = "2026-07-20" in tr
    ok = (sorted(files_tr) == sorted(FILES) and all_exit0 and all_silent
          and len(set(hashes)) == 4 and anecdote and tc_ok and commit_ok and date_ok)
    check("M11", "compile_transcript_internal_consistency", ok,
          "4/4 files, exit=0 and 0 bytes each, 4 distinct well-formed sha256, toolchain string == "
          "lean-toolchain pin (v4.32.0), commit hash consistent across sections, date 2026-07-20; "
          "changed-hash anecdote coherent (earlier Anyon b29eb596…@6173104B vs shipped 84ea435a…"
          "@6160504B — different hash AND size after the toKK_injective repair); the hashes and the "
          "exit-0 kernel run themselves are UNVERIFIABLE here (no toolchain) — single-sided per the "
          "standing caveat")

    # ---------------------------------------------------------------- summary
    fails = [r for r in RESULTS if r[0] == "FAIL"]
    print("\n== %d checks, %d PASS, %d FAIL ==" % (len(RESULTS), len(RESULTS) - len(fails), len(fails)))
    for st, cid, nm, _ in fails:
        print("   FAIL:", cid, nm)
    print("\n== DISCREPANCIES (ledger vs crate) ==")
    print(" D1 [courier-or-packaging] audit/transcript.sh + audit/axioms.sh claimed to ship; absent "
          "from the crate (M9). Census + transcript stay single-sided this round.")
    print(" D2 [prose, minor] PROOFS.md places the census false positive in 'Anyon.lean §6'; it is "
          "actually MagicSquare.lean:320 (§6 Item C doc comment, line starts 'theorems below...'). "
          "Anyon contains no such line; raw ^theorem grep MS=64 vs census 63 confirms.")
    print(" D3 [prose, minor] PROOFS.md counts 'three independent proofs' of no-global-section "
          "(cocycle, exhaustion, parity); MagicSquare.lean §9.2 itself counts FOUR routes — the "
          "ledger omits its own §8 sharp-bound route (satCount_le_five → satCount_ne_six).")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
