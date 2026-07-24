"""Independent verification of Exchangeable.lean, reimplemented from the Lean
definitions ONLY (init/step/run/num/numOfCounts/guardLive/numSpoiled/isRep),
in exact arithmetic: Python ints + fractions.Fraction. No floats.

Part 1: every numeric claim at length 6.
Part 2: fresh data at length 8 (and 7): class counts and cross-class
        numerator collisions.
"""
from fractions import Fraction
from math import factorial as fact
from itertools import product
from collections import defaultdict

FAIL = []

def check(name, ok, detail=""):
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)

# ---------------------------------------------------------------- the machine
# Lean: init = <false, 1,1,1,1, 1,1, 0,0,0,0>
#       step: draw from urn of current state x; numer *= u[x][nxt];
#             denom *= u[x][0]+u[x][1]; u[x][nxt] += 1; n[x][nxt] += 1; x=nxt
def run_path(bits):
    x = 0                       # start state false = 0
    u = [[1, 1], [1, 1]]        # u00,u01,u10,u11 all 1
    numer, denom = 1, 1
    n = [[0, 0], [0, 0]]
    frac = Fraction(1)          # bench-style Fraction, computed in parallel
    for nxt in bits:
        c = u[x]
        numer *= c[nxt]
        denom *= c[0] + c[1]
        frac *= Fraction(c[nxt], c[0] + c[1])
        c[nxt] += 1
        n[x][nxt] += 1
        x = nxt
    return numer, denom, (n[0][0], n[0][1], n[1][0], n[1][1]), frac

def numOfCounts(c, D):
    n00, n01, n10, n11 = c
    d = fact(n00 + n01 + 1) * fact(n10 + n11 + 1)
    exact = (D % d == 0)
    return (D // d) * (fact(n00) * fact(n01) * fact(n10) * fact(n11)), exact

def analyze(L, verbose_checks=True):
    """Run all 2^L paths; verify per-path claims; return structures."""
    D = fact(L + 1) ** 2
    data = {}                    # path -> (num, counts, frac, numer, denom)
    total_num = 0
    total_frac = Fraction(0)
    all_div, all_spec, all_pos, all_closed, all_frac = True, True, True, True, True
    for p in product((0, 1), repeat=L):
        numer, denom, cts, frac = run_path(p)
        all_div &= (D % denom == 0)                      # denom_divides_D
        num = (D // denom) * numer                       # def num (Nat division)
        all_spec &= (num * denom == D * numer)           # num_spec
        all_pos &= (num > 0)                             # num_pos
        noc, exact = numOfCounts(cts, D)
        all_closed &= exact and (num == noc)             # num_factors_through_counts
        all_frac &= (Fraction(num, D) == frac == Fraction(numer, denom))
        data[p] = (num, cts, frac)
        total_num += num
        total_frac += frac
    # classes
    classes = defaultdict(list)
    for p, (num, cts, frac) in data.items():
        classes[cts].append(p)
    class_val = {}
    exch_ok = True
    for cts, ps in classes.items():
        vals = {data[p][0] for p in ps}
        exch_ok &= (len(vals) == 1)                      # exchangeable / pairCheck
        class_val[cts] = vals.pop()
    byval = defaultdict(list)
    for cts, v in class_val.items():
        byval[v].append(cts)
    shared = {v: sorted(cs) for v, cs in byval.items() if len(cs) >= 2}
    if verbose_checks:
        check(f"L={L}: denom(p) | D for all {2**L} paths", all_div)
        check(f"L={L}: num*denom == D*numer for all paths (num_spec)", all_spec)
        check(f"L={L}: num > 0 for all paths (num_pos)", all_pos)
        check(f"L={L}: num == numOfCounts(counts p), division exact", all_closed)
        check(f"L={L}: Fraction cross-check num/D == numer/denom", all_frac)
        check(f"L={L}: total of all nums == D (total_is_D)", total_num == D,
              f"total={total_num}, D={D}")
        check(f"L={L}: Fraction total == 1", total_frac == 1)
        check(f"L={L}: within every class all nums identical (exchangeable)", exch_ok)
    return D, data, classes, class_val, shared, total_num

# =====================================================================
print("=" * 72)
print("PART 1 — LENGTH 6 (all claims of Exchangeable.lean)")
print("=" * 72)

D6 = fact(7) ** 2
check("D = (7!)^2 = 25401600", D6 == 25401600, f"(7!)^2 = {D6}")

D, data, classes, class_val, shared, total = analyze(6)

npaths = len(data)
check("64 paths (path_count)", npaths == 64)

# --- class count
check("22 distinct transition-count classes (class_count)", len(classes) == 22,
      f"got {len(classes)}")
check("classes fewer than paths (22 < 64)", len(classes) < npaths)

# --- guard-live pair counts: ordered pairs with equal counts
guard_live = sum(len(ps) ** 2 for ps in classes.values())
guard_live_offdiag = guard_live - npaths
# direct O(64^2) recount, no shortcut:
gl2 = sum(1 for p in data for q in data if data[p][1] == data[q][1])
gl2_off = sum(1 for p in data for q in data
              if data[p][1] == data[q][1] and p != q)
check("guardLive = 266", guard_live == 266 == gl2, f"got {gl2}")
check("guardLiveOffDiagonal = 202", guard_live_offdiag == 202 == gl2_off,
      f"got {gl2_off}")
check("0 < guardLiveOffDiagonal", gl2_off > 0)

# --- spoiled numerator: num p + (1 if first step is 1 else 0)
def spoiled(p):
    return data[p][0] + (1 if p[0] == 1 else 0)
viol = sum(1 for p in data for q in data
           if data[p][1] == data[q][1] and spoiled(p) != spoiled(q))
check("spoiledViolations = 98", viol == 98, f"got {viol}")
check("pairCheck can fail on spoiled num", viol > 0)
viol_real = sum(1 for p in data for q in data
                if data[p][1] == data[q][1] and data[p][0] != data[q][0])
check("num violations = 0 (num_violations_count)", viol_real == 0)

# --- specific paths.  Lean Path b1..b6, false=0; string b1 first.
def P(s):
    return tuple(int(ch) for ch in s)

pZeros, pOnes = P("000000"), P("111111")
pA, pB, pC = P("000010"), P("000100"), P("111110")

check("num(000000) = 3628800", data[pZeros][0] == 3628800,
      f"got {data[pZeros][0]}")
check("num(111111) = 2116800", data[pOnes][0] == 2116800,
      f"got {data[pOnes][0]}")
check("counts(000000) = (6,0,0,0)", data[pZeros][1] == (6, 0, 0, 0),
      f"got {data[pZeros][1]}")
check("counts(111111) = (0,1,0,5)", data[pOnes][1] == (0, 1, 0, 5),
      f"got {data[pOnes][1]}")
check("P(000000) = 1/7 (comment claim 3628800/D = 1/7)",
      data[pZeros][2] == Fraction(1, 7))
check("P(111111) = 1/12 (comment claim 2116800/D = 1/12)",
      data[pOnes][2] == Fraction(1, 12))
check("separates: counts and nums both differ for 000000 vs 111111",
      data[pZeros][1] != data[pOnes][1] and data[pZeros][0] != data[pOnes][0])

check("num(000010) = 423360", data[pA][0] == 423360, f"got {data[pA][0]}")
check("num(000100) = 423360", data[pB][0] == 423360, f"got {data[pB][0]}")
check("pA != pB as paths", pA != pB)
check("counts(000010) == counts(000100) (pA_pB_same_counts)",
      data[pA][1] == data[pB][1], f"{data[pA][1]} vs {data[pB][1]}")
check("P(000010) = 1/60 (comment claim 423360/D = 1/60)",
      data[pA][2] == Fraction(1, 60))

check("counts(000010) = (4,1,1,0)", data[pA][1] == (4, 1, 1, 0),
      f"got {data[pA][1]}")
check("counts(111110) = (0,1,1,4)", data[pC][1] == (0, 1, 1, 4),
      f"got {data[pC][1]}")
check("counts(000010) != counts(111110)", data[pA][1] != data[pC][1])
check("num(000010) == num(111110) (converse_false collision)",
      data[pA][0] == data[pC][0],
      f"{data[pA][0]} vs {data[pC][0]}")

# --- idx injectivity + one representative per class (structural claims)
def idx(p):
    return sum(b << (5 - i) for i, b in enumerate(p))
idxs = [idx(p) for p in data]
check("idx injective on 64 paths", len(set(idxs)) == 64
      and sorted(idxs) == list(range(64)))
reps = {min(ps, key=idx) for ps in classes.values()}
one_rep = all(sum(1 for q in classes[data[p][1]] if q in reps) == 1
              for p in data)
check("exactly one least-index representative per class", one_rep)
check("numClasses via representatives = 22", len(reps) == 22)

# --- shared numerator values across distinct classes at L=6
check("numerator values shared across distinct classes at L=6: FIVE",
      len(shared) == 5, f"got {len(shared)}")
print("\n  L=6 cross-class collisions (value: classes (n00,n01,n10,n11)):")
for v in sorted(shared):
    print(f"    num={v:>8}  P={Fraction(v, D)}  classes={shared[v]}")

# =====================================================================
print()
print("=" * 72)
print("PART 2 — FRESH DATA: LENGTH 8 (and 7)")
print("=" * 72)

for L in (7, 8):
    DL = fact(L + 1) ** 2
    print(f"\n--- length {L}: {2**L} paths, D{L} = ({L+1}!)^2 = {DL} ---")
    Dl, datal, classesl, cvl, sharedl, totall = analyze(L)
    print(f"  distinct transition-count classes: {len(classesl)}")
    print(f"  numerator values shared by >= 2 distinct classes: {len(sharedl)}")
    ncls_involved = sum(len(cs) for cs in sharedl.values())
    print(f"  (classes involved in a collision: {ncls_involved})")
    if sharedl:
        v = sorted(sharedl)[0]
        print(f"  example: num={v}  P={Fraction(v, DL)}  shared by classes:")
        for c in sharedl[v]:
            noc, _ = numOfCounts(c, DL)
            print(f"     counts (n00,n01,n10,n11)={c}: class size "
                  f"{len(classesl[c])}, numOfCounts={noc}")
        print("  all collisions:")
        for v in sorted(sharedl):
            print(f"     num={v:>12}  P={Fraction(v, DL)}  classes={sharedl[v]}")

# L=8 specific: D8 value and bench claim of 37
D8 = fact(9) ** 2
check("\nD8 = (9!)^2 = 131681894400", D8 == 131681894400, f"got {D8}")

print()
print("=" * 72)
print(f"RESULT: {'ALL CHECKS PASSED' if not FAIL else 'FAILURES: ' + str(FAIL)}")
print("=" * 72)
