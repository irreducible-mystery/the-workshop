#!/usr/bin/env python3
"""r3_pentagon_poly.py — round-3 audit, pentagon-uniqueness section of Anyon.lean.

Checks P1, P2(python side), P3, P4, P5, P6, P7a, P7b.

Reimplemented FROM THE LEAN SOURCE (round-3 /home/claude/workshop/lean/Anyon.lean):

  LIVENESS GUARD (Anyon.lean lines 119-121, `pentagonValid`):
      memA x (fuse a b) && memA y (fuse x c) && memA t (fuse y dd) &&
      memA w (fuse c dd) && memA v (fuse b w) && memA t (fuse a v)

  INSTANCE INDEXING: the file enumerates tuples (a,b,c,dd,x,y,t,w,v) in the
  `sumB` nest order (a outermost ... v innermost, `.one` before `.tau` — i.e.
  lexicographic with one<tau).  The 11 nonzero-residual instances, taken in
  that order, are the file's #1..#11 of section 7.1 (`pent_at_01`..`pent_at_11`),
  all at total charge (a,b,c,dd)=(tau,tau,tau,tau), indexed by (x,y,t,w,v):
    #1 (1,t,1,1,t) #2 (1,t,1,t,t) #3 (1,t,t,1,t) #4 (1,t,t,t,1) #5 (1,t,t,t,t)
    #6 (t,1,t,1,t) #7 (t,1,t,t,1) #8 (t,t,1,1,t) #9 (t,t,1,t,t) #10 (t,t,t,1,t)
    #11 (t,t,t,t,t)

  RESIDUAL CONVENTION: residual := LHS - RHS where
      LHS = sum_{u in fuse(b,c)} (Fs(a,b,c,y,x,u)*Fs(a,u,dd,t,y,v))*Fs(b,c,dd,v,u,w)
      RHS = Fs(x,c,dd,t,y,w)*Fs(a,b,w,t,x,v)
  exactly the two sides handed to K.beq in `pentagonCheck` (lines 125-133).

Two instruments inside this script:
  (A) an independent dict-based sparse ring Z[p,q,r,s];
  (B) a verbatim transcription of the file's own PentPoly list algorithm
      (monCmp/insSorted/monMul/insTerm/normP/addP/mulP, lines 1612-1656).
Exact integer arithmetic only.
"""
import sys
from itertools import product

ONE, TAU = 0, 1
LABELS = (ONE, TAU)  # one first == Lean sumB order (f .one + f .tau)

def fuse(a, b):
    if a == ONE: return (b,)
    if b == ONE: return (a,)
    return (ONE, TAU)

def memA(x, lst): return x in lst
def isOne(a): return a == ONE

# ---------- Instrument A: dict-based sparse poly ring Z[p,q,r,s] ----------
# monomial = sorted tuple of generator indices (0=p,1=q,2=r,3=s), file encoding.
PZERO = {}
def pconst(c): return {(): c} if c else {}
PONE = pconst(1)
def pvar(i): return {(i,): 1}
def padd(u, v):
    w = dict(u)
    for m, c in v.items():
        t = w.get(m, 0) + c
        if t: w[m] = t
        else: w.pop(m, None)
    return w
def pneg(u): return {m: -c for m, c in u.items()}
def psub(u, v): return padd(u, pneg(v))
def pmul(u, v):
    w = {}
    for m1, c1 in u.items():
        for m2, c2 in v.items():
            m = tuple(sorted(m1 + m2)); t = w.get(m, 0) + c1 * c2
            if t: w[m] = t
            else: w.pop(m, None)
    return w
def pbeq(u, v): return u == v

RingA = dict(zero=PZERO, one=PONE, add=padd, mul=pmul, beq=pbeq)
FgA = {(ONE, ONE): pvar(0), (ONE, TAU): pvar(1), (TAU, ONE): pvar(2), (TAU, TAU): pvar(3)}

# ---------- Instrument B: verbatim PentPoly (file lines 1612-1656) ----------
def monCmp(a, b):
    if not a and not b: return 0
    if not a: return -1
    if not b: return 1
    if a[0] < b[0]: return -1
    if b[0] < a[0]: return 1
    return monCmp(a[1:], b[1:])

def insSorted(x, m):
    if not m: return [x]
    y, ys = m[0], m[1:]
    if x <= y: return [x] + m
    return [y] + insSorted(x, ys)

def monMul(m1, m2):
    if not m1: return list(m2)
    a, rest = m1[0], m1[1:]
    return insSorted(a, monMul(rest, m2))

def insTerm(c, m, poly):
    if not poly:
        return [] if c == 0 else [(c, m)]
    (c2, m2), ps = poly[0], poly[1:]
    cmp = monCmp(m, m2)
    if cmp == -1:
        return list(poly) if c == 0 else [(c, m)] + list(poly)
    if cmp == 0:
        t = c + c2
        return list(ps) if t == 0 else [(t, m2)] + list(ps)
    return [(c2, m2)] + insTerm(c, m, ps)

def normP(p):
    acc = []
    for (c, m) in p: acc = insTerm(c, m, acc)
    return acc
def addP(p, q):
    acc = list(p)
    for (c, m) in q: acc = insTerm(c, m, acc)
    return acc
def mulP(p, q):
    return normP([(c1 * c2, monMul(m1, m2)) for (c1, m1) in p for (c2, m2) in q])

RingB = dict(zero=[], one=[(1, [])], add=addP, mul=mulP,
             beq=lambda a, b: a == b)
FgB = {(ONE, ONE): [(1, [0])], (ONE, TAU): [(1, [1])],
       (TAU, ONE): [(1, [2])], (TAU, TAU): [(1, [3])]}

# ---------- coherence code, transcribed from Fs / pentagonValid / pentagonCheck ----------
def Fs(K, F, a, b, c, d, x, y):
    if memA(x, fuse(a, b)) and memA(d, fuse(x, c)) and \
       memA(y, fuse(b, c)) and memA(d, fuse(a, y)):
        if isOne(a) or isOne(b) or isOne(c): return K['one']
        if isOne(d):
            return K['one'] if (not isOne(x)) and (not isOne(y)) else K['zero']
        return F[(x, y)]
    return K['zero']

def pentagonValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and
            memA(t, fuse(y, dd)) and memA(w, fuse(c, dd)) and
            memA(v, fuse(b, w)) and memA(t, fuse(a, v)))

def sumOver(K, f, lst):
    # Lean: f u + (rest); [] -> zero.  Order kept identical.
    if not lst: return K['zero']
    return K['add'](f(lst[0]), sumOver(K, f, lst[1:]))

def pent_sides(K, F, a, b, c, dd, x, y, t, w, v):
    lhs = sumOver(K, lambda u: K['mul'](K['mul'](Fs(K, F, a, b, c, y, x, u),
                                                 Fs(K, F, a, u, dd, t, y, v)),
                                        Fs(K, F, b, c, dd, v, u, w)), fuse(b, c))
    rhs = K['mul'](Fs(K, F, x, c, dd, t, y, w), Fs(K, F, a, b, w, t, x, v))
    return lhs, rhs

def pentagonCheck(K, F, *tup):
    if pentagonValid(*tup):
        lhs, rhs = pent_sides(K, F, *tup)
        return K['beq'](lhs, rhs)
    return True

# ---------- enumeration ----------
ALL = list(product(LABELS, repeat=9))          # file nest order: a..v, one first
assert len(ALL) == 512
VALID = [tp for tp in ALL if pentagonValid(*tp)]
INVALID = [tp for tp in ALL if not pentagonValid(*tp)]

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok), detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ===== P1: live/trivial split =====
check("P1.total_512", len(ALL) == 512, f"total={len(ALL)}")
check("P1.live_50", len(VALID) == 50, f"live={len(VALID)}")
check("P1.nest_total", len(VALID) + len(INVALID) == 512,
      f"{len(VALID)}+{len(INVALID)}=512")

resid = {}   # tuple -> residual poly (instrument A)
for tp in VALID:
    lhs, rhs = pent_sides(RingA, FgA, *tp)
    resid[tp] = psub(lhs, rhs)
zero_t = [tp for tp in VALID if not resid[tp]]
nonzero_t = [tp for tp in VALID if resid[tp]]
check("P1.zero_39", len(zero_t) == 39, f"identically-zero residuals={len(zero_t)}")
check("P1.nonzero_11", len(nonzero_t) == 11, f"nonzero residuals={len(nonzero_t)}")
check("P1.nest_live", len(zero_t) + len(nonzero_t) == 50,
      f"{len(zero_t)}+{len(nonzero_t)}=50")
check("P1.all_nonzero_at_tttt", all(tp[:4] == (TAU,) * 4 for tp in nonzero_t),
      "all 11 at (a,b,c,d)=(tau,tau,tau,tau)")

# file indexing: #1..#11 tuples hardcoded from pent_at_01..pent_at_11 statements
FILE11 = [(ONE,TAU,ONE,ONE,TAU),(ONE,TAU,ONE,TAU,TAU),(ONE,TAU,TAU,ONE,TAU),
          (ONE,TAU,TAU,TAU,ONE),(ONE,TAU,TAU,TAU,TAU),(TAU,ONE,TAU,ONE,TAU),
          (TAU,ONE,TAU,TAU,ONE),(TAU,TAU,ONE,ONE,TAU),(TAU,TAU,ONE,TAU,TAU),
          (TAU,TAU,TAU,ONE,TAU),(TAU,TAU,TAU,TAU,TAU)]
FILE11 = [(TAU,TAU,TAU,TAU)+t for t in FILE11]
check("P1.indexing_matches_file", nonzero_t == FILE11,
      "enumeration-order nonzero == file's pent_at_01..11")
R = {i + 1: resid[tp] for i, tp in enumerate(FILE11)}   # residual by file index

# dedupe + relations
distinct = []
for i in range(1, 12):
    if all(R[i] != d for d in distinct): distinct.append(R[i])
eq_pairs = [(i, j) for i in range(1, 12) for j in range(i + 1, 12) if R[i] == R[j]]
neg_pairs = [(i, j) for i in range(1, 12) for j in range(i + 1, 12)
             if R[i] == pneg(R[j])]
check("P1.distinct_10", len(distinct) == 10, f"distinct residual polynomials={len(distinct)}")
check("P1.dup_6_eq_4", eq_pairs == [(4, 6)], f"equal pairs={eq_pairs}")
check("P1.neg_7_of_4", set(neg_pairs) == {(4, 7), (6, 7)},
      f"negation pairs={neg_pairs} (6=4 so (6,7) forced)")
check("P1.nest_dedupe", len(distinct) + len(eq_pairs) == 11,
      f"10 distinct + {len(eq_pairs)} duplicate = 11")

# negative control: broken guard (drop last conjunct `memA t (fuse a v)`)
def brokenValid(a, b, c, dd, x, y, t, w, v):
    return (memA(x, fuse(a, b)) and memA(y, fuse(x, c)) and
            memA(t, fuse(y, dd)) and memA(w, fuse(c, dd)) and
            memA(v, fuse(b, w)))
nbroken = sum(1 for tp in ALL if brokenValid(*tp))
check("P1.negctrl_guard", nbroken != 50,
      f"guard minus last conjunct -> {nbroken} live (not 50): count is guard-sensitive")

# ===== P2 (python side): the file's own algorithm agrees =====
violB = 0; liveB = 0; violA = 0
for tp in ALL:
    if pentagonValid(*tp):
        liveB += 1
        if not pentagonCheck(RingB, FgB, *tp): violB += 1
        if not pentagonCheck(RingA, FgA, *tp): violA += 1
check("P2.file_algorithm_11", violB == 11,
      f"verbatim PentPoly transcription: countPentViolations={violB} (live={liveB})")
check("P2.dict_ring_11", violA == 11, f"independent dict ring: violations={violA}")
check("P2.two_instruments_agree", violA == violB, f"{violA}=={violB}")
# cross-validate the two representations term by term on all live residuals
xok = True
for tp in VALID:
    lhsB, rhsB = pent_sides(RingB, FgB, *tp)
    diffB = addP(lhsB, [(-c, m) for (c, m) in rhsB])
    if {tuple(m): c for (c, m) in normP(diffB)} != resid[tp]: xok = False
check("P2.representations_match", xok, "list-poly residuals == dict-poly residuals, all 50")
# negative control: the list ring distinguishes p from q
check("P2.negctrl_beq", RingB['beq']([(1, [0])], [(1, [1])]) is False,
      "beq(p,q)=false in file ring")

# ===== P3: residual identities in file indexing =====
p_, q_, r_, s_ = pvar(0), pvar(1), pvar(2), pvar(3)
P3_1 = padd(pmul(p_, p_), padd(pmul(q_, r_), pconst(-1)))   # p^2+qr-1
P3_4 = psub(pmul(q_, r_), p_)                               # qr-p
P3_3 = padd(pmul(p_, p_), pmul(pmul(q_, r_), s_))           # p^2+qrs
check("P3.resid1", R[1] == P3_1, "resid#1 == p^2+qr-1 exactly (unit +1, no scaling)")
check("P3.resid4", R[4] == P3_4, "resid#4 == qr-p exactly")
check("P3.resid3", R[3] == P3_3, "resid#3 == p^2+q*r*s exactly")
# instance 3 relates to p(p+s): substitute qr->p in resid3 gives p^2+ps = p*(p+s)
def sub_qr_to_p(poly):
    out = {}
    for m, c in poly.items():
        ep = m.count(0); eq = m.count(1); er = m.count(2); es = m.count(3)
        k = min(eq, er); ep += k; eq -= k; er -= k
        mm = tuple(sorted((0,) * ep + (1,) * eq + (2,) * er + (3,) * es))
        t = out.get(mm, 0) + c
        if t: out[mm] = t
        else: out.pop(mm, None)
    return out
check("P3.resid3_relation", sub_qr_to_p(P3_3) == pmul(p_, padd(p_, s_)),
      "resid#3 with qr:=p == p*(p+s)")

# ===== P4: the pentagon_forces_golden route, as exact polynomial algebra =====
golden = padd(padd(pmul(p_, p_), p_), pconst(-1))  # p^2+p-1
# step 1: resid1 = resid4 + (p^2+p-1): substitution alone, multiplier 1
check("P4.step1_substitution", psub(R[1], R[4]) == golden,
      "resid#1 - resid#4 == p^2+p-1 (coefficient 1, no cancellation)")
def red_p2(poly):  # p^2 := 1-p, exhaustively
    poly = dict(poly)
    while True:
        hit = None
        for m in poly:
            if m.count(0) >= 2: hit = m; break
        if hit is None: return poly
        c = poly.pop(hit)
        rest = list(hit); rest.remove(0); rest.remove(0)
        m1 = tuple(sorted(rest))                     # * 1
        m2 = tuple(sorted(rest + [0]))               # * (-p)
        for mm, cc in ((m1, c), (m2, -c)):
            t = poly.get(mm, 0) + cc
            if t: poly[mm] = t
            else: poly.pop(mm, None)
# step 2: p is a unit with inverse p+1
check("P4.step2_p_unit", red_p2(pmul(p_, padd(p_, PONE))) == PONE,
      "p*(p+1) reduces to 1 modulo p^2:=1-p")
# step 3: resid3 + inverse -> s = -p
r3sub = sub_qr_to_p(R[3])                          # p^2+ps = p(p+s)
step3 = red_p2(pmul(padd(p_, PONE), r3sub))
check("P4.step3_s_eq_neg_p", step3 == padd(p_, s_),
      "(p+1)*(resid#3 with qr:=p) reduces to p+s; p+s=0 gives s=-p by adding -p")
# no domain property: only multipliers used are units 1 and (p+1) with p*(p+1)=1;
# negative controls in the FREE ring (relation withheld):
check("P4.negctrl_free_unit", pmul(p_, padd(p_, PONE)) != PONE,
      "without the relation p*(p+1) != 1 (free ring)")
check("P4.negctrl_free_cancel", pmul(padd(p_, PONE), r3sub) != padd(p_, s_),
      "without the relation (p+1)*p*(p+s) != p+s (free ring)")
check("P4.negctrl_not_s_eq_p", red_p2(sub_qr_to_p({(1,): 1, (3,): 1})) != PZERO,
      "p+s does not reduce to 0 without s:=-p — s=+p is NOT derivable")

# ===== P5 / P6: reduction modulo the three forced relations =====
def NF(poly, use_s=True, use_qr=True, use_p2=True):
    out = {}
    for m, c in poly.items():
        ep = m.count(0); eq = m.count(1); er = m.count(2); es = m.count(3)
        if use_s:
            c *= (-1) ** es; ep += es; es = 0          # s := -p
        if use_qr:
            k = min(eq, er); ep += k; eq -= k; er -= k  # qr := p, repeatedly
        mm = tuple(sorted((0,) * ep + (1,) * eq + (2,) * er + (3,) * es))
        t = out.get(mm, 0) + c
        if t: out[mm] = t
        else: out.pop(mm, None)
    if use_p2: out = red_p2(out)                        # p^2 := 1-p
    return out

check("P5.resid9_to_zero", NF(R[9]) == PZERO,
      "resid#9 = qr+s^2-1 -> 0 under {s:=-p, qr:=p, p^2:=1-p}")
check("P5.fixpoint", NF(NF(R[9])) == NF(R[9]), "reduction idempotent on resid#9")
# negative control: a WRONG relation p^2 := 1+p leaves resid#1 nonzero
def red_p2_wrong(poly):
    poly = dict(poly)
    while True:
        hit = None
        for m in poly:
            if m.count(0) >= 2: hit = m; break
        if hit is None: return poly
        c = poly.pop(hit)
        rest = list(hit); rest.remove(0); rest.remove(0)
        for mm, cc in ((tuple(sorted(rest)), c), (tuple(sorted(rest + [0])), c)):
            t = poly.get(mm, 0) + cc
            if t: poly[mm] = t
            else: poly.pop(mm, None)
def NFwrong(poly):
    return red_p2_wrong(NF(poly, use_p2=False))
check("P5.negctrl_wrong_relation", NFwrong(R[1]) != PZERO,
      f"with p^2:=1+p resid#1 -> {NFwrong(R[1])} != 0")

# P6: ALL 50 live residuals
all_zero = all(NF(resid[tp]) == PZERO for tp in VALID)
n_zero_after = sum(1 for tp in VALID if NF(resid[tp]) == PZERO)
check("P6.sufficiency_all_50", all_zero,
      f"{n_zero_after}/50 live residuals reduce to 0 under the three forced "
      "relations — TRUE, verified in exact integer arithmetic; NOT a Lean theorem "
      "(declared gap, PROOFS.md)")
check("P6.nest", n_zero_after == len(zero_t) + len(nonzero_t),
      f"{len(zero_t)} already zero + {len(nonzero_t)} reduced = {n_zero_after}")

# ===== P7a: 2,5,8,10 vanish under s:=-p and p^2:=1-p WITHOUT qr:=p =====
gauge_idx = [2, 5, 8, 10]
ok_a = all(NF(R[i], use_qr=False) == PZERO for i in gauge_idx)
check("P7a.gauge_instances_vanish", ok_a,
      "resid#2,#5,#8,#10 -> 0 under {s:=-p, p^2:=1-p} with qr NOT used")
only_s = [i for i in gauge_idx if NF(R[i], use_qr=False, use_p2=False) == PZERO]
need_p2 = [i for i in gauge_idx if i not in only_s]
check("P7a.which_reductions", only_s == [2, 8] and need_p2 == [5, 10],
      f"s:=-p alone kills {only_s}; {need_p2} need also p^2:=1-p")
# negative control: #1 does NOT vanish without qr:=p (qr=p is a real constraint)
nc1 = NF(R[1], use_qr=False)
check("P7a.negctrl_resid1_needs_qr", nc1 == psub(pmul(q_, r_), p_),
      "resid#1 under {s,p^2} alone -> qr-p != 0: qr:=p not implied by the others")

# ===== P7b: q,r only through the product qr =====
def qr_balanced(poly):
    return all(m.count(1) == m.count(2) for m in poly)
others = [1, 3, 4, 6, 7, 9, 11]
raw_ok = [i for i in others if qr_balanced(R[i])]
check("P7b.balanced_raw", raw_ok == others,
      f"residuals {others}: per-monomial q-degree == r-degree ALREADY RAW "
      "(no reduction needed)")
check("P7b.gauge_raw_unbalanced", all(not qr_balanced(R[i]) for i in gauge_idx),
      f"residuals {gauge_idx} are NOT balanced raw — they are the ones killed "
      "by (a) instead")
post = {i: NF(R[i], use_qr=False) for i in others}
check("P7b.balanced_after", all(qr_balanced(post[i]) for i in others),
      "still balanced after {s:=-p, p^2:=1-p}")
check("P7b.nest", len(others) + len(gauge_idx) == 11, "7 balanced + 4 gauge = 11")

print()
nfail = sum(1 for _, ok, _ in results if not ok)
print(f"{'ALL PASS' if nfail == 0 else str(nfail) + ' FAILURES'}  "
      f"({len(results)} checks)")
sys.exit(0 if nfail == 0 else 1)
