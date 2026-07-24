"""Independent numerical verification of the repository's headline math claims.
All checks over complex numbers / exact integer arithmetic, written from scratch."""
import cmath, itertools, numpy as np

ok = lambda name, cond: print(("PASS " if cond else "FAIL ") + name)

phi = (1 + 5**0.5) / 2
z = cmath.exp(2j * cmath.pi / 5)  # zeta_5

# --- 1. Pentagon forces golden: F = [[1/phi, 1/sqrt(phi)],[1/sqrt(phi), -1/phi]] satisfies pentagon
ONE, TAU = 0, 1
def fuse(a, b):
    if a == ONE: return [b]
    if b == ONE: return [a]
    return [ONE, TAU]
def Fs(F, a,b,c,d,x,y):
    if x not in fuse(a,b) or d not in fuse(x,c): return 0
    if y not in fuse(b,c) or d not in fuse(a,y): return 0
    if ONE in (a,b,c): return 1
    if d == ONE: return 1 if (x,y)==(TAU,TAU) else 0
    return F[x][y]
F = [[1/phi, phi**-0.5],[phi**-0.5, -1/phi]]
maxres = 0; nvalid = 0
for a,b,c,d,x,y,t,w,v in itertools.product([0,1], repeat=9):
    # guard
    if not (x in fuse(a,b) and y in fuse(x,c) and t in fuse(y,d) and
            w in fuse(c,d) and v in fuse(b,w) and t in fuse(a,v)): continue
    nvalid += 1
    lhs = sum(Fs(F,a,b,c,y,x,u)*Fs(F,a,u,d,t,y,v)*Fs(F,b,c,d,v,u,w) for u in fuse(b,c))
    rhs = Fs(F,x,c,d,t,y,w)*Fs(F,a,b,w,t,x,v)
    maxres = max(maxres, abs(lhs-rhs))
ok(f"pentagon holds (50 valid instances: {nvalid}), residual {maxres:.2e}", nvalid==50 and maxres < 1e-12)

# golden relation p^2 + p = 1 for p = 1/phi
ok("golden relation (1/phi)^2 + 1/phi = 1", abs((1/phi)**2 + 1/phi - 1) < 1e-12)

# --- 2. Hexagon fixes braid eigenvalues r1 = z^2, rt = -z
r1, rt = z**2, -z
def Rb(x,y,c):
    if x==ONE or y==ONE: return 1
    return r1 if c==ONE else rt
maxres = 0; nvalid = 0
for a,b,c,d,e,zz in itertools.product([0,1], repeat=6):
    if not (e in fuse(a,b) and d in fuse(e,c) and zz in fuse(a,c) and d in fuse(zz,b)): continue
    nvalid += 1
    lhs = Rb(e,c,d)*Fs(F,c,a,b,d,zz,e)
    rhs = sum(Fs(F,a,b,c,d,e,g)*Rb(b,c,g)*Fs(F,a,c,b,d,zz,g)*Rb(a,c,zz) for g in fuse(b,c))
    maxres = max(maxres, abs(lhs-rhs))
ok(f"hexagon holds (15 valid instances: {nvalid}), residual {maxres:.2e}", nvalid==15 and maxres < 1e-12)

# forced quadratic rt^2 + (1/phi) rt + 1 = 0 and r1 = rt^2
ok("r1 = rt^2", abs(r1 - rt**2) < 1e-12)
ok("rt^2 + (1/phi) rt + 1 = 0", abs(rt**2 + rt/phi + 1) < 1e-12)

# --- 3. Yang-Baxter and non-abelian
B1 = np.diag([r1, rt])
Fm = np.array(F, dtype=complex)
B2 = Fm @ B1 @ Fm
ok("Yang-Baxter B1B2B1 = B2B1B2", np.allclose(B1@B2@B1, B2@B1@B2, atol=1e-12))
ok("non-abelian B1B2 != B2B1", not np.allclose(B1@B2, B2@B1, atol=1e-6))

# --- 4. Perron: Fibonacci fusion matrix [[0,1],[1,1]] has unique positive eigenvalue phi
evs = np.linalg.eigvals(np.array([[0,1],[1,1]], dtype=float))
ok(f"fusion eigenvalues {sorted(evs.round(6))} = (-1/phi, phi)",
   np.allclose(sorted(evs), [-1/phi, phi], atol=1e-9))

# --- 5. Verlinde over Z[phi], cleared: D^2 * N_ab^c = verlNum
# M = [[1, phi],[phi, -1]], D^2 = phi + 2. verlNum = M_a1 M_b1 M_c1 + M_at M_bt M_ct * (1/phi)
M = {(0,0):1, (0,1):phi, (1,0):phi, (1,1):-1}
D2 = phi + 2
def Nmult(a,b,c): return fuse(a,b).count(c)
allok = True
for a,b,c in itertools.product([0,1],repeat=3):
    vn = M[a,0]*M[b,0]*M[c,0] + M[a,1]*M[b,1]*M[c,1]*(1/phi)
    if abs(D2*Nmult(a,b,c) - vn) > 1e-9: allok=False; print("  cell fail",a,b,c,vn)
ok("verlinde_cleared all 8 cells", allok)

# S^2 = I check on cleared form: M^2 = D^2 I
Mm = np.array([[1,phi],[phi,-1]])
ok("M^2 = D^2 I", np.allclose(Mm@Mm, D2*np.eye(2), atol=1e-9))

# N(D^2) = 5: D^2 = phi+2 -> conj = 3-phi where phibar = 1-phi; (phi+2)(3-phi) = 3phi-phi^2+6-2phi = phi - (phi+1) + 6 = 5
ok("N(phi+2) = (phi+2)(3-phi) = 5", abs((phi+2)*(3-phi) - 5) < 1e-12)

# --- 6. T-layer: theta_tau = z^3; modular cube (ST)^3 = (phi+2) * pp * I with pp = z^3 - z
T = np.diag([1, z**3])
ShatT = Mm.astype(complex) @ T
cube = ShatT @ ShatT @ ShatT
pp = z**3 - z
ok("modular cube = (phi+2)*pp*I", np.allclose(cube, (phi+2)*pp*np.eye(2), atol=1e-9))
pm = z**2 - z**4
ok("pp * pm = phi + 2", abs(pp*pm - (phi+2)) < 1e-9)
ok("pm = conj(pp)", abs(pm - pp.conjugate()) < 1e-12)
ok("pp^4 = theta_tau (phi+2)^2", abs(pp**4 - z**3*(phi+2)**2) < 1e-8)
# lambda = zeta20^13, D = sqrt(phi+2): lambda*D = pp?
lam = cmath.exp(2j*cmath.pi*13/20)
ok("lambda*D = pp (lambda=zeta20^13)", abs(lam*(phi+2)**0.5 - pp) < 1e-9)
# c = -14/5: e^{2 pi i c / 8} = lambda?
ok("e^{2pi i(-14/5)/8} = lambda", abs(cmath.exp(2j*cmath.pi*(-14/5)/8) - lam) < 1e-12)
# ribbon: theta_tau = r1/phi + rt = z^3
ok("ribbon twist r1/phi + rt = z^3", abs(r1/phi + rt - z**3) < 1e-12)
# Frobenius-Schur nu = r1 * theta = 1
ok("Frobenius-Schur r1*theta = 1", abs(r1*z**3 - 1) < 1e-12)

# --- 7. Magic square: rank M = 5, rank [M|b] = 6, coker Z2, classical value 8/9, best sat 5
import numpy.linalg as la
# GF(2) rank via row reduction
def gf2_rank(rows):
    rows = [int(''.join(map(str,r)),2) for r in rows]
    rank = 0
    for bit in reversed(range(9)):
        piv = next((r for r in rows if (r>>bit)&1), None)
        if piv is None: continue
        rows = [r^piv if ((r>>bit)&1 and r!=piv) else r for r in rows]
        rows.remove(piv) if piv in rows else None
        rank += 1
    return rank
Mrows = []
for r in range(3):
    Mrows.append([1 if i//3==r else 0 for i in range(9)])
for c in range(3):
    Mrows.append([1 if i%3==c else 0 for i in range(9)])
ok("rank M = 5 (GF2)", gf2_rank(Mrows)==5)
# augmented [M|b], b = (0,0,0,0,0,1)
aug = [row+[bb] for row,bb in zip(Mrows,[0,0,0,0,0,1])]
def gf2_rank_w(rows, width):
    rows = [int(''.join(map(str,r)),2) for r in rows]
    rank = 0
    for bit in reversed(range(width)):
        piv = next((r for r in rows if (r>>bit)&1), None)
        if piv is None: continue
        rows = [rr^piv if ((rr>>bit)&1 and rr!=piv) else rr for rr in rows]
        if piv in rows: rows.remove(piv)
        rank += 1
    return rank
ok("rank [M|b] = 6 (GF2)", gf2_rank_w(aug,10)==6)

# no global section; satcount max 5; histogram
best = 0; hist = {}
for bits in itertools.product([0,1],repeat=9):
    v = lambda i,j: bits[3*i+j]
    rp = [v(r,0)^v(r,1)^v(r,2) for r in range(3)]
    cp = [v(0,c)^v(1,c)^v(2,c) for c in range(3)]
    sat = sum(p==0 for p in rp) + (cp[0]==0)+(cp[1]==0)+(cp[2]==1)
    best = max(best,sat); hist[sat]=hist.get(sat,0)+1
ok(f"max satisfiable contexts = 5, hist {sorted(hist.items())}", best==5 and hist.get(6,0)==0)
ok("satCount histogram 1:96, 3:320, 5:96 (all odd)", hist=={1:96,3:320,5:96})

# classical game value: 8 of 9, 144 maximizers
bestg = 0; cnt8 = 0; n=0
for a0,a1,a2,a3,a4,a5 in itertools.product([0,1],repeat=6):
    A = [[a0,a1,a0^a1],[a2,a3,a2^a3],[a4,a5,a4^a5]]
    for b0,b1,b2,b3,b4,b5 in itertools.product([0,1],repeat=6):
        B = [[b0,b2,b4],[b1,b3,b5],[b0^b1,b2^b3,1^(b4^b5)]]
        s = sum(A[i][j]==B[i][j] for i in range(3) for j in range(3))
        n+=1
        if s>bestg: bestg=s
        if s==8: cnt8+=1
ok(f"classical game: {n} pairs, best={bestg}, count8={cnt8}", n==4096 and bestg==8 and cnt8==144)

# image count = 32 (even weight covectors reachable)
img = set()
for bits in itertools.product([0,1],repeat=9):
    v = lambda i,j: bits[3*i+j]
    u = tuple([v(r,0)^v(r,1)^v(r,2) for r in range(3)] + [v(0,c)^v(1,c)^v(2,c) for c in range(3)])
    img.add(u)
even = {u for u in itertools.product([0,1],repeat=6) if sum(u)%2==0}
ok("im(M) = even-weight covectors (32)", img==even and len(img)==32)

# left kernel exactly {0, all-ones}
kers = []
for y in itertools.product([0,1],repeat=6):
    # y.M: entry (i,j) = y_i ^ y_{3+j}
    if all((y[i]^y[3+j])==0 for i in range(3) for j in range(3)): kers.append(y)
ok("left kernel = {0, all-ones}", sorted(kers)==[(0,)*6,(1,)*6])

print("\nAll independent checks complete.")
