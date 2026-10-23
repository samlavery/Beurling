# Lemma pattern: sum over invertible nonneg integer kxk E_P of prod_j tau_j^{-(s_j-1)} <= k! prod_j (1-1/tau_j)^{-k}
# Exact truncated enumeration (entries <= m); truncation only lowers the LHS.
from fractions import Fraction as Fr
from itertools import product
import math
def det(M):
    k = len(M)
    if k == 1: return M[0][0]
    if k == 2: return M[0][0]*M[1][1]-M[0][1]*M[1][0]
    return sum((-1)**c * M[0][c] * det([r[:c]+r[c+1:] for r in M[1:]]) for c in range(k))
for k, m, taus in [(2, 8, [Fr(2), Fr(3)]), (2, 10, [Fr(3,2), Fr(5,2)]), (3, 3, [Fr(3), Fr(4), Fr(5)]), (3, 4, [Fr(6), Fr(7), Fr(9)])]:
    lhs = Fr(0)
    for ent in product(range(m+1), repeat=k*k):
        M = [list(ent[i*k:(i+1)*k]) for i in range(k)]
        if det(M) == 0: continue
        w = Fr(1)
        for j in range(k):
            s = sum(M[i][j] for i in range(k))
            w *= taus[j] ** (-(s-1))
        lhs += w
    rhs = math.factorial(k)
    for t in taus: rhs *= (1 - 1/t) ** (-k)
    print("k=%d m=%d taus=%s: truncated LHS/k! = %.5f, prod(1-1/tau)^-k = %.5f, ratio %.4f" % (k, m, [str(t) for t in taus], float(lhs)/math.factorial(k), float(rhs)/math.factorial(k), float(lhs/rhs)))
    assert lhs <= rhs
