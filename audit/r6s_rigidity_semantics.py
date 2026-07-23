#!/usr/bin/env python3
# =============================================================================
# r6s_rigidity_semantics.py -- round-6 SEAT audit: Rigidity.lean semantics
#
# Standalone, exact integer arithmetic only.  Everything below is transcribed
# from /home/claude/workshop/lean/Rigidity.lean (round-6 tree,
# sha256 d67d6437...) and checked against
#   (a) an INDEPENDENT jets-free route: SS built once as an integer-coefficient
#       polynomial in Z[p,q,r,s], differentiated exactly, evaluated in Zp / Ep;
#   (b) the file's own transcribed literals (GY GS GC GG, HY/HG entries, SOS
#       certificates, minors, determinants, kernel decompositions);
#   (c) the round-3 pentagon machinery (audit/r3_pentagon_complete.py), on
#       30 random ring points x 512 tuples  (house norm: grep the fact).
#
# PASS/FAIL per check; exit 0 iff all pass.
# =============================================================================
import sys, random, importlib.util
from itertools import product

random.seed(20260723)

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# ---------------------------------------------------------------------------
# Zp = Z[phi], transcribed from Rigidity.lean SS0/SS2
# ---------------------------------------------------------------------------
def zp(m, n=0): return (m, n)
ZP0, ZP1, PHI, INVPHI = (0,0), (1,0), (0,1), (-1,1)
def zadd(u,v): return (u[0]+v[0], u[1]+v[1])
def zneg(u):   return (-u[0], -u[1])
def zsub(u,v): return (u[0]-v[0], u[1]-v[1])
def zmul(u,v): return (u[0]*v[0]+u[1]*v[1], u[0]*v[1]+u[1]*v[0]+u[1]*v[1])
def zscale(c,u): return (c*u[0], c*u[1])

# Ord5.posUN, transcribed verbatim (branch for branch)
def posUN(u, y):
    if 0 <= y:
        if 0 <= u: return (0 < u) or (0 < y)
        return u*u < 5*(y*y)
    else:
        if 0 <= u: return 5*(y*y) < u*u
        return False
def zpos(a): return posUN(2*a[0]+a[1], a[1])       # Zp.pos
def znn(a):  return a == ZP0 or zpos(a)            # Zp.Nn

# semantic pin: m + n*phi > 0 in R  (float only as a CROSS-check of posUN)
import math
PHI_R = (1+math.sqrt(5))/2
def zreal(a): return a[0] + a[1]*PHI_R

# ---------------------------------------------------------------------------
# Ep = Zp[s]/(s^2 - phi), transcribed from SS8
# ---------------------------------------------------------------------------
EP0, EP1, RAD = (ZP0,ZP0), (ZP1,ZP0), (ZP0,ZP1)
def eofz(a): return (a, ZP0)
def eadd(u,v): return (zadd(u[0],v[0]), zadd(u[1],v[1]))
def eneg(u):   return (zneg(u[0]), zneg(u[1]))
def esub(u,v): return (zsub(u[0],v[0]), zsub(u[1],v[1]))
def emul(u,v):
    return (zadd(zmul(u[0],v[0]), zmul(PHI, zmul(u[1],v[1]))),
            zadd(zmul(u[0],v[1]), zmul(u[1],v[0])))
def escale(c,u): return (zscale(c,u[0]), zscale(c,u[1]))
def enrm(u): return zsub(zmul(u[0],u[0]), zmul(PHI, zmul(u[1],u[1])))
def epos(u):                                        # Ep.pos, verbatim branches
    x, y = u
    if zpos(x):
        if zpos(zneg(y)): return zpos(enrm(u))
        return True
    elif zpos(zneg(x)):
        if zpos(y): return zpos(zneg(enrm(u)))
        return False
    else:
        return zpos(y)
def ereal(u): return zreal(u[0]) + zreal(u[1])*math.sqrt(PHI_R)

# ---------------------------------------------------------------------------
# Pentagon machinery, transcribed from Rigidity.lean SS0 (generic ring K)
# K = dict(zero, one, add, neg, mul)
# ---------------------------------------------------------------------------
ONE, TAU = 0, 1
def fuse(a,b):
    if a == ONE: return (b,)
    if b == ONE: return (a,)
    return (ONE, TAU)
def isOne(a): return a == ONE
def sumOver(K, f, lst):
    if not lst: return K['zero']
    return K['add'](f(lst[0]), sumOver(K, f, lst[1:]))
def Fs(K, F, a,b,c,d,x,y):
    if (x in fuse(a,b)) and (d in fuse(x,c)) and (y in fuse(b,c)) and (d in fuse(a,y)):
        if isOne(a) or isOne(b) or isOne(c): return K['one']
        if isOne(d):
            return K['one'] if (not isOne(x)) and (not isOne(y)) else K['zero']
        return F(x,y)
    return K['zero']
def pentagonValid(a,b,c,dd,x,y,t,w,v):
    return ((x in fuse(a,b)) and (y in fuse(x,c)) and (t in fuse(y,dd)) and
            (w in fuse(c,dd)) and (v in fuse(b,w)) and (t in fuse(a,v)))
def Fg(p,q,r,sp):
    return lambda i,j: p if (i,j)==(ONE,ONE) else q if (i,j)==(ONE,TAU) \
        else r if (i,j)==(TAU,ONE) else sp
def pentResid(K, F, a,b,c,dd,x,y,t,w,v):
    lhs = sumOver(K, lambda u: K['mul'](K['mul'](Fs(K,F,a,b,c,y,x,u),
                                                 Fs(K,F,a,u,dd,t,y,v)),
                                        Fs(K,F,b,c,dd,v,u,w)), list(fuse(b,c)))
    return K['add'](lhs, K['neg'](K['mul'](Fs(K,F,x,c,dd,t,y,w),
                                           Fs(K,F,a,b,w,t,x,v))))
def sqResid(K, F, *tup):
    if pentagonValid(*tup):
        rr = pentResid(K, F, *tup)
        return K['mul'](rr, rr)
    return K['zero']
ALL9 = list(product((ONE,TAU), repeat=9))
def SS(K, F):
    acc = K['zero']
    for tup in ALL9:
        acc = K['add'](acc, sqResid(K, F, *tup))
    return acc
def pentOK(F, tup):     # over Zp, decide residual = 0 (file's pentOK)
    if pentagonValid(*tup):
        return pentResid(KZp, F, *tup) == ZP0
    return True

KZp = dict(zero=ZP0, one=ZP1, add=zadd, neg=zneg, mul=zmul)
KEp = dict(zero=EP0, one=EP1, add=eadd, neg=eneg, mul=emul)

# ---------------------------------------------------------------------------
# J2 jet ring, transcribed slot-for-slot from j2Rng (truncated Leibniz)
# jet = tuple of 15 base-ring elements: v d0 d1 d2 d3 e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
# ---------------------------------------------------------------------------
IDX = "v d0 d1 d2 d3 e00 e01 e02 e03 e11 e12 e13 e22 e23 e33".split()
def j2rng(K):
    Z, A, M = K['zero'], K['add'], K['mul']
    def jadd(u,w): return tuple(A(a,b) for a,b in zip(u,w))
    def jneg(u):   return tuple(K['neg'](a) for a in u)
    def jmul(u,w):
        (uv,ud0,ud1,ud2,ud3,ue00,ue01,ue02,ue03,ue11,ue12,ue13,ue22,ue23,ue33)=u
        (wv,wd0,wd1,wd2,wd3,we00,we01,we02,we03,we11,we12,we13,we22,we23,we33)=w
        return (M(uv,wv),
                A(M(uv,wd0),M(ud0,wv)), A(M(uv,wd1),M(ud1,wv)),
                A(M(uv,wd2),M(ud2,wv)), A(M(uv,wd3),M(ud3,wv)),
                A(A(M(uv,we00),M(ue00,wv)), M(ud0,wd0)),
                A(A(M(uv,we01),M(ue01,wv)), A(M(ud0,wd1),M(ud1,wd0))),
                A(A(M(uv,we02),M(ue02,wv)), A(M(ud0,wd2),M(ud2,wd0))),
                A(A(M(uv,we03),M(ue03,wv)), A(M(ud0,wd3),M(ud3,wd0))),
                A(A(M(uv,we11),M(ue11,wv)), M(ud1,wd1)),
                A(A(M(uv,we12),M(ue12,wv)), A(M(ud1,wd2),M(ud2,wd1))),
                A(A(M(uv,we13),M(ue13,wv)), A(M(ud1,wd3),M(ud3,wd1))),
                A(A(M(uv,we22),M(ue22,wv)), M(ud2,wd2)),
                A(A(M(uv,we23),M(ue23,wv)), A(M(ud2,wd3),M(ud3,wd2))),
                A(A(M(uv,we33),M(ue33,wv)), M(ud3,wd3)))
    jz = tuple([K['zero']]*15)
    jo = tuple([K['one']] + [K['zero']]*14)
    return dict(zero=jz, one=jo, add=jadd, neg=jneg, mul=jmul)
def jp(K, a, k):
    out = [a] + [K['zero']]*14
    out[1+k] = K['one']
    return tuple(out)
def germ(K, p, q, r, sp):
    J = j2rng(K)
    return SS(J, Fg(jp(K,p,0), jp(K,q,1), jp(K,r,2), jp(K,sp,3)))
def hessOf(K, g):
    d = dict(zip(IDX, g)); A = K['add']
    H = [[None]*4 for _ in range(4)]
    for i in range(4):
        H[i][i] = A(d[f"e{i}{i}"], d[f"e{i}{i}"])
    for (i,j) in [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]:
        H[i][j] = H[j][i] = d[f"e{i}{j}"]
    return H
def gradOf(g): return list(g[1:5])

# ---------------------------------------------------------------------------
# INDEPENDENT route (shares no code with the jets): SS as a polynomial in
# Z[p,q,r,s], exact partial derivatives, then evaluation in Zp / Ep.
# ---------------------------------------------------------------------------
def pz(): return {}
def pconst(c): return {(0,0,0,0): c} if c else {}
def pvar(i):
    e = [0,0,0,0]; e[i] = 1
    return {tuple(e): 1}
def padd(f,g):
    h = dict(f)
    for k,v in g.items():
        h[k] = h.get(k,0)+v
        if h[k]==0: del h[k]
    return h
def pneg(f): return {k:-v for k,v in f.items()}
def pmul(f,g):
    h = {}
    for k1,v1 in f.items():
        for k2,v2 in g.items():
            k = tuple(a+b for a,b in zip(k1,k2))
            h[k] = h.get(k,0)+v1*v2
            if h[k]==0: del h[k]
    return h
KPoly = dict(zero=pz(), one=pconst(1), add=padd, neg=pneg, mul=pmul)
def pdiff(f, i):
    h = {}
    for k,v in f.items():
        if k[i] > 0:
            kk = list(k); kk[i] -= 1
            h[tuple(kk)] = h.get(tuple(kk),0) + v*k[i]
    return h
def peval(f, K, pt):
    # pt: 4 ring elements; integer-coefficient monomial evaluation in K
    acc = K['zero']
    scale = zscale if K is KZp else escale
    for k,c in f.items():
        m = K['one']
        for i,e in enumerate(k):
            for _ in range(e): m = K['mul'](m, pt[i])
        acc = K['add'](acc, scale(c, m))
    return acc

FPOLY = Fg(pvar(0), pvar(1), pvar(2), pvar(3))
SS_POLY = SS(KPoly, FPOLY)
GRAD_POLY = [pdiff(SS_POLY, i) for i in range(4)]
HESS_POLY = [[pdiff(GRAD_POLY[i], j) for j in range(4)] for i in range(4)]

# ---------------------------------------------------------------------------
# The four points, and the file's transcribed literals
# ---------------------------------------------------------------------------
pY, qY, rY, sY = zneg(PHI), ZP1, zneg(PHI), PHI
PT_Y = (pY,qY,rY,sY)
PT_S = (ZP1,ZP1,ZP1,ZP1)
PT_C = ((1,0),(2,0),(3,0),(-1,0))
pG, qG, sG = ((-1,1),ZP0), (ZP0,(-1,1)), ((1,-1),ZP0)
PT_G = (pG,qG,qG,sG)

GY = (ZP0,ZP0,ZP0,ZP0,ZP0,(15,10),(8,18),(-10,-8),(12,18),(8,9),(-2,-16),(-4,-8),(7,1),(4,4),(29,29))
GS = ((17,0),(24,0),(20,0),(20,0),(26,0),(21,0),(14,0),(14,0),(16,0),(12,0),(24,0),(28,0),(12,0),(28,0),(26,0))
GC = ((201,0),ZP0,(220,0),(150,0),(-96,0),(39,0),(-10,0),ZP0,(-2,0),(64,0),(156,0),(-64,0),(29,0),(-56,0),(136,0))
GG = (EP0,EP0,EP0,EP0,EP0,
      (( 15,-4),ZP0),(ZP0,(26,-18)),(ZP0,(26,-18)),((-12,8),ZP0),
      (( -9, 8),ZP0),((-18,16),ZP0),(ZP0,(-12,8)),
      (( -9, 8),ZP0),(ZP0,(-12,8)),
      ((  1, 6),ZP0))

HY_ENT = {(0,0):(30,20),(0,1):(8,18),(0,2):(-10,-8),(0,3):(12,18),
          (1,1):(16,18),(1,2):(-2,-16),(1,3):(-4,-8),
          (2,2):(14,2),(2,3):(4,4),(3,3):(58,58)}
HG_ENT = {(0,0):((30,-8),ZP0),(0,1):(ZP0,(26,-18)),(0,2):(ZP0,(26,-18)),
          (0,3):((-12,8),ZP0),(1,1):((-18,16),ZP0),(1,2):((-18,16),ZP0),
          (1,3):(ZP0,(-12,8)),(2,2):((-18,16),ZP0),(2,3):(ZP0,(-12,8)),
          (3,3):((2,12),ZP0)}

# =============================================================================
# BLOCK 1 -- pentagon guard, solutionhood, anti-vacuity
# =============================================================================
VALID = [t for t in ALL9 if pentagonValid(*t)]
check("guard.live_count_50", len(VALID) == 50, f"live={len(VALID)}/512")

FY = Fg(*PT_Y)
ok_all = all(pentOK(FY, t) for t in ALL9)
live_zero = all(pentResid(KZp, FY, *t) == ZP0 for t in VALID)
check("YL.is_solution_512", ok_all and live_zero,
      "all 512 pentOK true; all 50 live residuals exactly 0 in Z[phi]")

FS_ = Fg(*PT_S)
bad = (TAU,TAU,TAU,TAU,ONE,TAU,ONE,ONE,TAU)
check("strict.fails_named_instance", pentOK(FS_, bad) == False,
      "pentOK (1,1,1,1) at (tau^4,1,tau,1,1,tau) = false  [pentOK_not_constant]")
n_live_bad = sum(1 for t in VALID if pentResid(KZp, FS_, *t) != ZP0)
check("strict.eight_of_eleven_alive",
      n_live_bad == 8 and len({tuple(pentResid(KZp,FS_,*t)) for t in VALID}) >= 2,
      f"nonzero live residuals at strict = {n_live_bad} (header: 'eight of the eleven live residuals alive')")

# =============================================================================
# BLOCK 2 -- germs: jet route == file literals == polynomial route
# =============================================================================
gY, gS, gC = germ(KZp,*PT_Y), germ(KZp,*PT_S), germ(KZp,*PT_C)
gG = germ(KEp,*PT_G)
check("germ.Y_matches_GY", gY == GY, "15/15 slots  [germ_Y]")
check("germ.S_matches_GS", gS == GS, "15/15 slots  [germ_S]")
check("germ.C_matches_GC", gC == GC, "15/15 slots  [germ_C]")
check("germ.G_matches_GG", gG == GG, "15/15 slots over E  [gg_e00..gg_e33 + SS_G_zero + grad_G_*]")

def poly_pack(K, pt):
    v  = peval(SS_POLY, K, pt)
    gr = [peval(GRAD_POLY[i], K, pt) for i in range(4)]
    H  = [[peval(HESS_POLY[i][j], K, pt) for j in range(4)] for i in range(4)]
    return v, gr, H
vY,grY,HpY = poly_pack(KZp, PT_Y)
vS,grS,HpS = poly_pack(KZp, PT_S)
vC,grC,HpC = poly_pack(KZp, PT_C)
vG,grG,HpG = poly_pack(KEp, PT_G)

HY, HS, HC = hessOf(KZp,gY), hessOf(KZp,gS), hessOf(KZp,gC)
HG = hessOf(KEp,gG)

check("poly.SS_values", (vY,vS,vC,vG) == (ZP0,(17,0),(201,0),EP0),
      "SS = 0 / 17 / 201 / 0 at YL / strict / control / golden (independent route)")
check("poly.gradients",
      grY == [ZP0]*4 and grS == [(24,0),(20,0),(20,0),(26,0)]
      and grC == [ZP0,(220,0),(150,0),(-96,0)] and grG == [EP0]*4,
      "grad: 0 at YL; (24,20,20,26) at strict [strict_not_critical]; (0,220,150,-96) at control; 0 at golden")

def eqM(A,B): return all(A[i][j]==B[i][j] for i in range(4) for j in range(4))
check("hessian.by_construction_Y", eqM(HY,HpY), "jet Hessian == d2SS/dxidxj exactly (diag doubling correct)")
check("hessian.by_construction_S", eqM(HS,HpS), "same at strict")
check("hessian.by_construction_C", eqM(HC,HpC), "same at control")
check("hessian.by_construction_G", eqM(HG,HpG), "same at golden, over E")

# negative control: drop the diagonal doubling and the tie MUST break
HY_bad = [row[:] for row in HY]
for i in range(4): HY_bad[i][i] = dict(zip(IDX,gY))[f"e{i}{i}"]
check("negctrl.diag_doubling_bites", not eqM(HY_bad,HpY),
      "hessOf without e_ii+e_ii disagrees with the polynomial Hessian")

check("HY.entries_match_docstring",
      all(HY[i][j]==HY_ENT[(min(i,j),max(i,j))] for i in range(4) for j in range(4)),
      "10 upper-triangle entries as in HY_entries; symmetric")
check("HG.entries_match_docstring",
      all(HG[i][j]==HG_ENT[(min(i,j),max(i,j))] for i in range(4) for j in range(4)),
      "10 entries as in HG_entries; four radical entries (26-18phi)sqrt(phi),(-12+8phi)sqrt(phi)")
check("HG.needs_radical_exactly4",
      [ (i,j) for (i,j),v in HG_ENT.items() if v[1]!=ZP0 ] == [(0,1),(0,2),(1,3),(2,3)],
      "[HG_needs_radical]")

# gift-letter basis conversion: H00 golden = 26-4sqrt5, H00 YL = 40+10sqrt5
def to_sqrt5(a):  # m+n*phi = (m+n/2) + (n/2)sqrt5  -> (2m+n, n)/2
    return (2*a[0]+a[1], a[1])
check("gift.basis_conversion",
      to_sqrt5(HG[0][0][0]) == (52,-8) and to_sqrt5(HY[0][0]) == (80,20),
      "H00_G = (52-8sqrt5)/2 = 26-4sqrt5 ; H00_Y = (80+20sqrt5)/2 = 40+10sqrt5")

# =============================================================================
# BLOCK 3 -- Yang-Lee: tangent, swap, rank, SOS certificate, PSD, kernel
# =============================================================================
def dot(K,u,w):
    return K['add'](K['add'](K['mul'](u[0],w[0]),K['mul'](u[1],w[1])),
                    K['add'](K['mul'](u[2],w[2]),K['mul'](u[3],w[3])))
def mvec(K,A,w): return [dot(K,A[i],w) for i in range(4)]
def qform(K,A,w): return dot(K,w,mvec(K,A,w))
def det2(K,a,b,c,d):
    sub = zsub if K is KZp else esub
    return sub(K['mul'](a,d),K['mul'](b,c))
def det3(K,A,r,c):
    r0,r1,r2 = r; c0,c1,c2 = c
    sub = zsub if K is KZp else esub
    return K['add'](sub(K['mul'](A[r0][c0],det2(K,A[r1][c1],A[r1][c2],A[r2][c1],A[r2][c2])),
                        K['mul'](A[r0][c1],det2(K,A[r1][c0],A[r1][c2],A[r2][c0],A[r2][c2]))),
                    K['mul'](A[r0][c2],det2(K,A[r1][c0],A[r1][c1],A[r2][c0],A[r2][c1])))
def det4(K,A):
    sub = zsub if K is KZp else esub
    return K['add'](sub(K['mul'](A[0][0],det3(K,A,(1,2,3),(1,2,3))),
                        K['mul'](A[0][1],det3(K,A,(1,2,3),(0,2,3)))),
                    sub(K['mul'](A[0][2],det3(K,A,(1,2,3),(0,1,3))),
                        K['mul'](A[0][3],det3(K,A,(1,2,3),(0,1,2)))))

tangentY = (ZP0, qY, zneg(rY), ZP0)          # (0, 1, phi, 0)
coTY     = (ZP0, rY, qY, ZP0)                # (0, -phi, 1, 0)
swapDir  = (ZP0, ZP1, zneg(ZP1), ZP0)

check("YL.tangent_null", mvec(KZp,HY,tangentY) == [ZP0]*4, "H.(0,q,-r,0) = 0  [HY_tangent_null]")
sw = qform(KZp,HY,swapDir)
check("YL.swap_not_null",
      mvec(KZp,HY,swapDir)[0] != ZP0 and sw == (34,52) and zpos(sw),
      f"qform(H,swapDir) = {sw} = 34+52phi > 0  [HY_swap_not_null]")
check("YL.rank3", det4(KZp,HY) == ZP0 and
      det3(KZp,HY,(0,1,3),(0,1,3)) == (21120,31480) and zpos((21120,31480)),
      "det4 = 0, det3(013) = 21120+31480phi > 0  [HY_det4_zero, HY_minor3_pos]")
check("YL.tangent_ne_swap", tangentY != swapDir, "(0,1,phi,0) != (0,1,-1,0)  [tangentY_ne_swapDir]")
check("YL.cols_differ", qY != rY and HY[1][1] != HY[1][2], "[YL_cols_differ]")

NY  = (111227520000, 179906032000)
eY1 = (1784777600, 2884209600); eY2 = (1263200, 1996400); eY3 = ZP1
LY1 = ((30,20),(8,18),(-10,-8),(12,18))
LY2 = (ZP0,(452,608),(-156,-452),(-700,-1164))
LY3 = (ZP0,ZP0,ZP0,(1263200,1996400))
sos_ok = all(
    zmul(NY,HY[a][b]) == zadd(zadd(zmul(eY1,zmul(LY1[a],LY1[b])),
                                   zmul(eY2,zmul(LY2[a],LY2[b]))),
                              zmul(eY3,zmul(LY3[a],LY3[b])))
    for a in range(4) for b in range(4))
check("YL.sos_identity_16", sos_ok, "N.H = e1 L1L1 + e2 L2L2 + e3 L3L3, all 16 entries  [sos_Y]")
check("YL.sos_scalars_pos", all(zpos(x) for x in (NY,eY1,eY2,eY3)), "[sos_Y_pos]")

# kernel decomposition receipts (dotLY1/dotLY2/dotLY3 coefficient identities)
cY3, lamY, aY3 = (1263200,1996400), (-156,-452), (-700,-1164)
bY0, bY2, bY3  = (30,20), (-10,-8), (12,18)
E0v, E3v = (ZP1,ZP0,ZP0,ZP0), (ZP0,ZP0,ZP0,ZP1)
d3 = all(LY3[k] == zmul(cY3,E3v[k]) for k in range(4))
d2 = all(LY2[k] == zadd(zmul(lamY,coTY[k]), zmul(aY3,E3v[k])) for k in range(4))
d1 = all(LY1[k] == zadd(zadd(zmul(bY0,E0v[k]), zmul(bY2,coTY[k])), zmul(bY3,E3v[k])) for k in range(4))
check("YL.kernel_decomp_receipts", d3 and d2 and d1,
      "LY3 = c.E3, LY2 = lam.coTY + a.E3, LY1 = b0.E0 + b2.coTY + b3.E3; lam,b0,c nonzero: "
      f"{lamY != ZP0 and zpos(bY0) and zpos(cY3)}")

# forall-w PSD + kernel iff, replayed mechanically (the psd_of_sos/ker_of_sos route)
# and sampled: 4000 random w; the line w = t.(0,1,phi,0); off-line perturbations
def rzp(B=25): return (random.randint(-B,B), random.randint(-B,B))
psd_ok, ker_ok = True, True
for _ in range(4000):
    w = (rzp(),rzp(),rzp(),rzp())
    qf = qform(KZp,HY,w)
    if not znn(qf): psd_ok = False; break
    lhs = (qf == ZP0)
    rhs = (w[0]==ZP0 and w[3]==ZP0 and dot(KZp,coTY,w)==ZP0)
    if lhs != rhs: ker_ok = False; break
line_ok = all(qform(KZp,HY,(ZP0,t,zmul(PHI,t),ZP0)) == ZP0 for t in [rzp() for _ in range(200)])
off_ok  = all(qform(KZp,HY,(ZP0,t,zadd(zmul(PHI,t),(1,0)),ZP0)) != ZP0 for t in [rzp() for _ in range(200)])
check("YL.psd_forall_sampled", psd_ok, "Nn(qform HY w) on 4000 random w in Z[phi]^4  [HY_psd]")
check("YL.kernel_iff_sampled", ker_ok and line_ok and off_ok,
      "qform=0 <-> w0=0 & w3=0 & <coTY,w>=0; whole line (0,t,phi t,0) null; off-line never  [HY_kernel, HY_kernel_is_line]")

# =============================================================================
# BLOCK 4 -- the strict battery (the refutation as theorems)
# =============================================================================
check("strict.not_critical", vS == (17,0) and grS[0] == (24,0) and grS[0] != ZP0,
      "SS=17, dSS/dp=24 != 0  [strict_not_critical]")
check("strict.cols_eq", all(HS[a][1]==HS[a][2] for a in range(4)), "[HS_cols_eq]")
check("strict.swap_null", mvec(KZp,HS,swapDir)==[ZP0]*4, "[HS_swap_null]")
NS_,eS1,eS2 = (22482448128,0),(535296384,0),(659232,0)
LS1,LS2,LS3 = ((42,0),(14,0),(14,0),(16,0)),(ZP0,(812,0),(812,0),(952,0)),(ZP0,ZP0,ZP0,(659232,0))
sosS = all(zmul(NS_,HS[a][b]) == zadd(zadd(zmul(eS1,zmul(LS1[a],LS1[b])),
                                           zmul(eS2,zmul(LS2[a],LS2[b]))),
                                      zmul(ZP1,zmul(LS3[a],LS3[b])))
           for a in range(4) for b in range(4))
psdS = all(znn(qform(KZp,HS,(rzp(),rzp(),rzp(),rzp()))) for _ in range(1500))
check("strict.also_psd", sosS and all(zpos(x) for x in (NS_,eS1,eS2,ZP1)) and psdS,
      "sos_S identity + positive scalars + 1500-sample PSD  [strict_also_psd]")
check("strict.also_rank3", det4(KZp,HS)==ZP0 and zpos(det3(KZp,HS,(0,1,3),(0,1,3))),
      "[strict_also_rank3]")

# =============================================================================
# BLOCK 5 -- the working negative control (1,2,3,-1)
# =============================================================================
tangentC = (ZP0,(2,0),(-3,0),ZP0)
wNegC    = ((-3,0),(-3,0),(3,0),(-1,0))
hv = mvec(KZp,HC,tangentC)
check("ctrl.tangent_not_null", hv == [(-20,0),(-212,0),(138,0),(40,0)],
      "H.(0,q,-r,0) = (-20,-212,138,40)  [HC_tangent_not_null; gift V3e]")
qn = qform(KZp,HC,wNegC)
check("ctrl.not_psd", qn == (-400,0) and zpos(zneg(qn)) and not znn(qn),
      "w^T H w = -400 < 0  [HC_not_psd]")
check("ctrl.rank4", det4(KZp,HC) == (-322420288,0) and det4(KZp,HC) != ZP0,
      "det4 = -322420288 != 0  [HC_rank4]")

# =============================================================================
# BLOCK 6 -- Ep order: brackets, controls, conservativity; golden certificate
# =============================================================================
b1 = epos(esub(emul(eofz((1000,0)),RAD), eofz((1272,0))))
b2 = epos(esub(eofz((1273,0)), emul(eofz((1000,0)),RAD)))
t1 = epos(esub(emul(eofz((1000,0)),RAD), eofz((1273,0))))
t2 = epos(esub(eofz((1272,0)), emul(eofz((1000,0)),RAD)))
check("Ep.rad_bracket_and_tight", b1 and b2 and (not t1) and (not t2),
      "1272 < 1000 sqrt(phi) < 1273, tight both sides  [rad_bracket, rad_bracket_tight]")
def nrmW(u): return zsub(zmul(u[0],u[0]), zmul(INVPHI, zmul(u[1],u[1])))
def posW(u):
    x,y = u
    if zpos(x):  return zpos(nrmW(u)) if zpos(zneg(y)) else True
    if zpos(zneg(x)): return zpos(zneg(nrmW(u))) if zpos(y) else False
    return zpos(y)
spec = ((-5,0),(4,0))
check("Ep.wrong_radicand_bites", epos(spec) and not posW(spec),
      "-5+4sqrt(phi) > 0; phi-1 radicand miscalls it  [wrong_radicand_miscalls]")
cons = all(epos(eofz(a)) == zpos(a) for a in [rzp() for _ in range(3000)])
check("Ep.conservative_over_Zp", cons, "pos(ofZ a) = Zp.pos a on 3000 samples  [pos_ofZ]")
tri = 0
for _ in range(3000):
    u = (rzp(6), rzp(6))
    tri += (1 if epos(u) else 0) + (1 if u == EP0 else 0) + (1 if epos(eneg(u)) else 0)
    if (1 if epos(u) else 0) + (1 if u == EP0 else 0) + (1 if epos(eneg(u)) else 0) != 1:
        tri = -1; break
check("Ep.trichotomy_sampled", tri != -1, "exactly one of u>0, u=0, -u>0 on 3000 samples  [Ep.trichotomy]")
fl = all((epos(u) == (ereal(u) > 0)) for u in
         [(rzp(40),rzp(40)) for _ in range(3000)] if abs(ereal(u)) > 1e-6)
check("Ep.semantics_float_pin", fl, "Ep.pos agrees with the real number x+y sqrt(phi) (float cross-check)")

check("G.on_variety", emul(qG,qG) == pG and sG == eneg(pG) and emul(qG,RAD) == EP1,
      "q^2 = p, s = -p, q.sqrt(phi) = 1  [G_on_variety, qG_inv_rad]")
tangentG = (EP0, qG, eneg(qG), EP0)
swapDirE = (EP0, EP1, eneg(EP1), EP0)
check("G.cols_eq_and_freebie",
      all(HG[a][1]==HG[a][2] for a in range(4)) and
      mvec(KEp,HG,tangentG)==[EP0]*4 and mvec(KEp,HG,swapDirE)==[EP0]*4 and
      all(tangentG[k] == emul(qG, swapDirE[k]) for k in range(4)),
      "q=r columns coincide; tangent AND swapDir null; tangent = qG . swapDir  [HG_cols_eq, HG_tangent_null]")
check("G.rank3", det4(KEp,HG)==EP0 and
      det3(KEp,HG,(0,1,3),(0,1,3)) == ((1920,360),ZP0) and
      epos(((1920,360),ZP0)),
      "det4E = 0; det3E(013) = 1920+360phi > 0  [HG_det4_zero, HG_minor3_pos]")

NG  = eofz((-160218240,152446080)); eG1 = eofz((-3867840,5522880)); eG2 = eofz((54720,-7440))
LG1 = (((30,-8),ZP0),(ZP0,(26,-18)),(ZP0,(26,-18)),((-12,8),ZP0))
LG2 = (EP0,((-56,108),ZP0),((-56,108),ZP0),(ZP0,(32,-8)))
LG3 = (EP0,EP0,EP0,((54720,-7440),ZP0))
sosG = all(emul(NG,HG[a][b]) == eadd(eadd(emul(eG1,emul(LG1[a],LG1[b])),
                                          emul(eG2,emul(LG2[a],LG2[b]))),
                                     emul(EP1,emul(LG3[a],LG3[b])))
           for a in range(4) for b in range(4))
check("G.sos_identity_16", sosG, "all 16 entries (file decides 10 upper + 6 lower)  [sos_G, sos_G_lower]")
check("G.sos_scalars_pos", all(epos(x) for x in (NG,eG1,eG2,EP1)), "[sos_G_pos]")
check("G.covectors_kill_tangent",
      all(dot(KEp,L,tangentG)==EP0 for L in (LG1,LG2,LG3)) and
      LG1[0] != EP0 and LG2[1] != EP0 and LG3[3] != EP0,
      "[LG_kill_tangent, LG_nontrivial]")
# corroborate the ADJUDICATED (not-in-Lean) forall-w reading at golden:
psdG = True
for _ in range(2000):
    w = ((rzp(8),rzp(8)),(rzp(8),rzp(8)),(rzp(8),rzp(8)),(rzp(8),rzp(8)))
    qf = qform(KEp,HG,w)
    if not (qf == EP0 or epos(qf)): psdG = False; break
check("G.psd_forall_SAMPLED_adjudicator_side", psdG,
      "2000 random w in E^4: qform >= 0 -- corroborates r6_gift V3d; DELIBERATELY not a Lean theorem (Ep.pos closure absent)")

# =============================================================================
# BLOCK 7 -- gauge curve differentiation, in the jet ring (DEFECT-2 site)
# =============================================================================
JZ = j2rng(KZp)
for _ in range(200):
    q_, r_ = rzp(), rzp()
    l  = tuple([ZP1, ZP0, ZP1] + [ZP0]*12)          # 1 + eps1
    li = tuple([ZP1, ZP0, zneg(ZP1)] + [ZP0]*12)    # 1 - eps1
    c1 = JZ['mul'](l,  tuple([q_]+[ZP0]*14))
    c2 = JZ['mul'](li, tuple([r_]+[ZP0]*14))
    prod = JZ['mul'](c1,c2)
    ok = (c1[0]==q_ and c1[2]==q_ and c2[0]==r_ and c2[2]==zneg(r_)
          and prod[0]==zmul(q_,r_) and prod[2]==ZP0)
    if not ok: break
check("gauge.jet_derivative", ok,
      "jets: d1(l q)=q, d1(li r)=-r, value(prod)=qr, d1(prod)=0 -- gamma'(1)=(0,q,-r,0), qr invariant to 1st order")
check("gauge.conjuncts_are_weaker", True,
      "NOTE: gauge_curve_deriv's 3 conjuncts = value slot (1q)(1r)=qr + d1 slots; the d1(prod)=0 half "
      "of 'qr invariant' is NOT a conjunct (trivial, but docstring claims it) -- see findings")

# =============================================================================
# BLOCK 8 -- pentResid vs the r3 pentagon machinery, 30 random ring points
# =============================================================================
spec_ = importlib.util.spec_from_file_location(
    "r3pent", "/home/claude/workshop/lean/audit/r3_pentagon_complete.py")
r3 = None
try:
    import io, contextlib
    r3 = importlib.util.module_from_spec(spec_)
    with contextlib.redirect_stdout(io.StringIO()):
        spec_.loader.exec_module(r3)   # module prints its own checks; silenced
except SystemExit:
    pass
if r3 is not None and hasattr(r3, "pent_sides"):
    agree = True
    for _ in range(30):
        p_,q_,r_,s_ = rzp(3),rzp(3),rzp(3),rzp(3)
        Ffile = Fg(p_,q_,r_,s_)
        Fr3   = {(x,y): (p_ if (x,y)==(0,0) else q_ if (x,y)==(0,1)
                         else r_ if (x,y)==(1,0) else s_)
                 for x in (0,1) for y in (0,1)}
        for t in ALL9:
            lhs, rhs = r3.pent_sides(r3.RingZp, Fr3, *t)
            if pentResid(KZp, Ffile, *t) != zsub(lhs, rhs): agree = False; break
            mine = pentOK(Ffile, t)
            theirs = r3.pentagonCheck(r3.RingZp, Fr3, *t)
            if mine != theirs: agree = False; break
        if not agree: break
    check("crossfile.pentResid_eq_r3_pentagonCheck", agree,
          "30 random Zp points x 512 tuples: pentResid = LHS-RHS of r3/Anyon pentagonCheck; pentOK <-> pentagonCheck")
else:
    check("crossfile.pentResid_eq_r3_pentagonCheck", False, "could not load r3_pentagon_complete.py")

# SS ties to the nest: sum over the 50 live squares only
for PT,expect in [(PT_S,(17,0)),(PT_C,(201,0))]:
    Ff = Fg(*PT)
    s50 = ZP0
    for t in VALID:
        rr = pentResid(KZp,Ff,*t); s50 = zadd(s50, zmul(rr,rr))
    if s50 != expect: break
check("SS.sum_is_50_live_squares", s50 == (201,0),
      "SS = sum of squares over exactly the 50 live tuples (462 contribute 0 by construction)")

# swap symmetry mechanism (SS6): pentResid_rev on random F, all 512 tuples
sym_ok = True
p_,q_,r_,s_ = rzp(4),rzp(4),rzp(4),rzp(4)
Fbase = Fg(p_,q_,r_,s_)
Ftr   = lambda i,j: Fbase(j,i)
for (a,b,c,dd,x,y,t,w,v) in ALL9:
    if pentResid(KZp,Ftr,dd,c,b,a,w,v,t,x,y) != pentResid(KZp,Fbase,a,b,c,dd,x,y,t,w,v):
        sym_ok = False; break
check("swap.residual_reversal_512", sym_ok,
      "pentResid (transp F) (d,c,b,a,w,v,t,x,y) = pentResid F (a,..,v), all 512  [pentResid_rev]")
ss_swap = SS(KZp, Fg(p_,r_,q_,s_)) == SS(KZp, Fg(p_,q_,r_,s_))
check("swap.SS_invariance_ADJUDICATOR_SIDE", ss_swap,
      "SS(p,r,q,s) = SS(p,q,r,s) numerically -- the DECLARED gap's content (r6_gift V3e), not a Lean theorem")

# counts tie to nests: the 50 live tuples carry 11 distinct residual
# polynomials (one identically zero); at strict, 8 of them are alive
respolys = [pentResid(KPoly, FPOLY, *t) for t in VALID]
def pkey(p): return tuple(sorted(p.items()))
distinct = {pkey(p) for p in respolys}
alive = {pkey(p) for p in respolys if sum(p.values()) != 0}
check("counts.11_distinct_8_alive",
      len(distinct) == 11 and (() in distinct) and len(alive) == 8
      and sum(1 for p in respolys if sum(p.values()) != 0) == 8,
      "50 live tuples -> 11 distinct residuals (incl. the zero one); 8 alive at (1,1,1,1) "
      "[header 'eight of the eleven live residuals alive'; ROUND6 '8 of 11']")

# =============================================================================
n_fail = sum(1 for _,ok in results if not ok)
print("-"*74)
print(f"TOTAL {len(results)} checks, {len(results)-n_fail} pass, {n_fail} fail")
print("RESULT: " + ("PASS" if n_fail == 0 else "FAIL"))
sys.exit(0 if n_fail == 0 else 1)
