"""Independent check of Rigidity.lean's Yang-Lee Hessian claims using sympy
over the exact field Q(sqrt5), built from scratch (not from the repo's floor)."""
import sympy as sp
import itertools

phi = sp.Rational(1,2) + sp.sqrt(5)/2

p,q,r,s = sp.symbols('p q r s')

ONE, TAU = 0, 1
def fuse(a,b):
    if a==ONE: return [b]
    if b==ONE: return [a]
    return [ONE,TAU]
Fdict = {(ONE,ONE):p,(ONE,TAU):q,(TAU,ONE):r,(TAU,TAU):s}
def Fs(a,b,c,d,x,y):
    if x not in fuse(a,b) or d not in fuse(x,c): return 0
    if y not in fuse(b,c) or d not in fuse(a,y): return 0
    if ONE in (a,b,c): return 1
    if d==ONE: return 1 if (x,y)==(TAU,TAU) else 0
    return Fdict[(x,y)]

SS = 0
nlive=0
for a,b,c,d,x,y,t,w,v in itertools.product([0,1],repeat=9):
    if not (x in fuse(a,b) and y in fuse(x,c) and t in fuse(y,d) and
            w in fuse(c,d) and v in fuse(b,w) and t in fuse(a,v)): continue
    nlive+=1
    resid = sum(Fs(a,b,c,y,x,u)*Fs(a,u,d,t,y,v)*Fs(b,c,d,v,u,w) for u in fuse(b,c)) \
            - Fs(x,c,d,t,y,w)*Fs(a,b,w,t,x,v)
    SS += resid**2
SS = sp.expand(SS)
print("live instances:", nlive)

YL = {p:-phi, q:1, r:-phi, s:phi}
SS_at = sp.simplify(SS.subs(YL))
print("SS at Yang-Lee:", SS_at)  # expect 0

vars4 = [p,q,r,s]
grad = [sp.simplify(sp.diff(SS,v).subs(YL)) for v in vars4]
print("gradient:", grad)  # expect all 0

H = sp.Matrix(4,4, lambda i,j: sp.simplify(sp.expand(sp.diff(SS,vars4[i],vars4[j]).subs(YL))))
print("Hessian:")
sp.pprint(H)

# expected HY from Lean file (m + n*phi):
def zp(m,n): return m + n*phi
HY_expected = sp.Matrix([
 [zp(30,20), zp(8,18),  zp(-10,-8), zp(12,18)],
 [zp(8,18),  zp(16,18), zp(-2,-16), zp(-4,-8)],
 [zp(-10,-8),zp(-2,-16),zp(14,2),   zp(4,4)],
 [zp(12,18), zp(-4,-8), zp(4,4),    zp(58,58)]])
diff = sp.simplify(H - HY_expected)
print("H - HY_expected == 0:", diff == sp.zeros(4,4))

# tangent (0, q, -r, 0) at YL = (0, 1, phi, 0): H*t = 0?
tv = sp.Matrix([0, 1, phi, 0])
print("H*tangent = 0:", sp.simplify(H*tv) == sp.zeros(4,1))

# swap dir (0,1,-1,0): qform = 34 + 52 phi?
sw = sp.Matrix([0,1,-1,0])
qf = sp.simplify((sw.T*H*sw)[0])
print("qform swap =", sp.nsimplify(qf), " expect", sp.nsimplify(34+52*phi), " equal:", sp.simplify(qf-(34+52*phi))==0)

# det H = 0, minor (0,1,3) positive
print("det H = 0:", sp.simplify(H.det())==0)
minor = H[[0,1,3],[0,1,3]].det()
mv = sp.simplify(minor)
print("minor(p,q,s) =", sp.nsimplify(mv), " expect", sp.nsimplify(21120+31480*phi),
      " equal:", sp.simplify(mv-(21120+31480*phi))==0, " positive:", mv > 0)

# eigenvalues nonneg (PSD)?
evs = [sp.nsimplify(sp.simplify(e)) for e in H.eigenvals()]
print("eigenvalues:", evs)
print("all >= 0:", all(sp.simplify(e) >= 0 for e in H.eigenvals()))

# SOS certificate: N*H = e1 L1L1^T + e2 L2L2^T + e3 L3L3^T
N  = zp(111227520000,179906032000)
e1 = zp(1784777600,2884209600)
e2 = zp(1263200,1996400)
e3 = 1
L1 = sp.Matrix([zp(30,20), zp(8,18), zp(-10,-8), zp(12,18)])
L2 = sp.Matrix([0, zp(452,608), zp(-156,-452), zp(-700,-1164)])
L3 = sp.Matrix([0,0,0, zp(1263200,1996400)])
lhs = N*H
rhs = e1*(L1*L1.T) + e2*(L2*L2.T) + e3*(L3*L3.T)
print("SOS certificate N*H = sum e_i L_i L_i^T:", sp.simplify(lhs-rhs)==sp.zeros(4,4))
print("N, e1, e2 positive:", N>0, e1>0, e2>0)
