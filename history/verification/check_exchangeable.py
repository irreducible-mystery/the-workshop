"""Independent check of Exchangeable.lean: two-state Polya-urn walk, length 6.
Each state has its own urn tracking (count of 0-continuations, count of 1-continuations),
both urns start (1,1); walk starts at 0. Probability of next step from state s to state x
is urn_s[x]/(urn_s[0]+urn_s[1]); then urn_s[x] += 1."""
from fractions import Fraction
import itertools

D = 25401600
import math
assert D == math.factorial(7)**2, "D = (7!)^2"

def prob(path):
    # path: tuple of 6 bits, walk visits s0=0 -> path[0] -> ... -> path[5]? 
    # Actually: path of length 6 means 6 steps from start state 0.
    urn = {0: [1,1], 1: [1,1]}
    s = 0
    p = Fraction(1)
    for x in path:
        tot = urn[s][0]+urn[s][1]
        p *= Fraction(urn[s][x], tot)
        urn[s][x] += 1
        s = x
    return p

def counts(path):
    s = 0; c = {(0,0):0,(0,1):0,(1,0):0,(1,1):0}
    for x in path:
        c[(s,x)] += 1; s = x
    return (c[(0,0)],c[(0,1)],c[(1,0)],c[(1,1)])

paths = list(itertools.product([0,1],repeat=6))
total = sum(prob(p) for p in paths)
print("total prob =", total, " == 1:", total == 1)

# exchangeability: prob depends only on counts
by_counts = {}
okc = True
for p in paths:
    c = counts(p)
    if c in by_counts and by_counts[c] != prob(p): okc = False
    by_counts[c] = prob(p)
print("prob depends only on counts:", okc)

# numerators integral with denominator D
allint = all((prob(p)*D).denominator == 1 for p in paths)
print("D*P integral for all 64 paths:", allint)

# pA = 000010 (false false false false true false), pB = 000100, pC = 111110
pA = (0,0,0,0,1,0); pB = (0,0,0,1,0,0); pC = (1,1,1,1,1,0)
print("counts pA:", counts(pA), "counts pB:", counts(pB), "same:", counts(pA)==counts(pB))
print("num pA =", prob(pA)*D, "= 1/60 * D:", prob(pA)==Fraction(1,60))
print("num pB =", prob(pB)*D, " equal pA:", prob(pA)==prob(pB))
print("counts pC:", counts(pC), " num pC =", prob(pC)*D, " equal pA:", prob(pA)==prob(pC))
print("converse false (same num, diff counts):", prob(pA)==prob(pC) and counts(pA)!=counts(pC))
