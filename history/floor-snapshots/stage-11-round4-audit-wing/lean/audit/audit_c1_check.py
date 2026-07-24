"""Audit of claim C1: hexagon LHS index order, bench (z,e) vs charge (e,z).

Machinery copied from grammar_hexagon.py (fuse, Fsym, Rsym, hexagon loop),
parameterized by the F matrix and by which order the LHS F-move uses.
"""
import numpy as np
from itertools import product as iproduct

ONE, TAU = 0, 1
PHI = (1 + np.sqrt(5)) / 2

# golden symmetric F (exactly as grammar_hexagon.py)
FG = np.array([[1 / PHI, 1 / np.sqrt(PHI)],
               [1 / np.sqrt(PHI), -1 / PHI]])

# rational gauge for task 3
FP = np.array([[1 / PHI, 1 / PHI],
               [1.0, -1 / PHI]])


def fuse(a, b):
    if a == ONE:
        return (b,)
    if b == ONE:
        return (a,)
    return (ONE, TAU)


def make_Fsym(F):
    def Fsym(a, b, c, d, x, y):
        if x not in fuse(a, b) or d not in fuse(x, c):
            return 0.0
        if y not in fuse(b, c) or d not in fuse(a, y):
            return 0.0
        if ONE in (a, b, c):
            return 1.0
        if d == ONE:
            return 1.0 if (x, y) == (TAU, TAU) else 0.0
        return F[x, y]
    return Fsym


def Rsym(x, y, c, r1, rt):
    if x == ONE or y == ONE:
        return 1.0 + 0.0j
    return r1 if c == ONE else rt


def hexagon_stats(F, r1, rt, order):
    """Loop structure copied from grammar_hexagon.hexagon_residual.
    order='bench' -> LHS Fsym(c,a,b,d,z,e); order='charge' -> Fsym(c,a,b,d,e,z).
    Returns (n_valid, n_violated at tol 1e-9, total squared residual)."""
    Fsym = make_Fsym(F)
    n_valid = 0
    n_viol = 0
    total = 0.0
    violated = []
    for a, b, c, d in iproduct((ONE, TAU), repeat=4):
        for e in fuse(a, b):
            if d not in fuse(e, c):
                continue
            for z in fuse(a, c):
                if d not in fuse(z, b):
                    continue
                n_valid += 1
                if order == "bench":
                    lhs = Rsym(e, c, d, r1, rt) * Fsym(c, a, b, d, z, e)
                elif order == "charge":
                    lhs = Rsym(e, c, d, r1, rt) * Fsym(c, a, b, d, e, z)
                else:
                    raise ValueError(order)
                rhs = 0.0 + 0.0j
                for g in fuse(b, c):
                    rhs += (Fsym(a, b, c, d, e, g)
                            * Rsym(b, c, g, r1, rt)
                            * Fsym(a, c, b, d, z, g)
                            * Rsym(a, c, z, r1, rt))
                diff = abs(lhs - rhs)
                total += diff ** 2
                if diff > 1e-9:
                    n_viol += 1
                    violated.append((a, b, c, d, e, z, diff))
    return n_valid, n_viol, total, violated


r1 = np.exp(4j * np.pi / 5)
rt = np.exp(-3j * np.pi / 5)

print("=== Task 2: golden symmetric F, both orders, r1=e^{4i pi/5}, rt=e^{-3i pi/5} ===")
for order in ("bench", "charge"):
    nv, nb, tot, viol = hexagon_stats(FG, r1, rt, order)
    print(f"  order={order:6s}: valid instances = {nv}, violated (|LHS-RHS|>1e-9) = {nb}, "
          f"total squared residual = {tot:.6e}")
    for v in viol:
        print(f"     violated (a,b,c,d,e,z)={v[:6]}  |LHS-RHS|={v[6]:.6f}")

print()
print("=== Task 3: rational gauge FP, BENCH order, same r1, rt ===")
nv, nb, tot, viol = hexagon_stats(FP, r1, rt, "bench")
print(f"  order=bench : valid instances = {nv}, violated = {nb}, "
      f"total squared residual = {tot:.6e}")
print(f"  FP nonzero residual: {tot > 1e-9}")

print()
print("=== sanity: reproduce grammar_hexagon.hexagon_residual value for FG bench ===")
print(f"  residual(FG, bench) = {hexagon_stats(FG, r1, rt, 'bench')[2]:.3e} (expect ~0)")
