# T6: mixed ordered sums of the Step-3 hybrids: sum over (A-multiset X of size r) >= (B-multiset Y of size s) of prod 1/p,
# versus the single-system multiset bound (l + (r+s)b)^{r+s}/(r+s)!, l = max(l_A, l_B), b = 1/X0m.
import sys, math, bisect
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
import t3_realised as T3

def poly_mul_geo(P, a, deg):  # P * 1/(1 - a z)
    Q = P[:]
    for i in range(1, deg + 1):
        Q[i] += a * Q[i - 1]
    return Q
def poly_div_geo(P, a, deg):  # P * (1 - a z)
    Q = P[:]
    for i in range(deg, 0, -1):
        Q[i] -= a * Q[i - 1]
    return Q

def mixed(A, B, U, deg):
    A = [p for p in A if p <= U]; B = [p for p in B if p <= U]
    totA = [1.0] + [0.0] * deg
    for p in A: totA = poly_mul_geo(totA, 1 / p, deg)
    # S[r][s] for s >= 1: sum_y in B (1/y) h_{s-1}(B<=y) h_r(A>=y)
    S = [[0.0] * (deg + 1) for _ in range(deg + 1)]
    for r in range(deg + 1): S[r][0] = totA[r]
    pts = sorted([(p, 0) for p in A] + [(p, 1) for p in B])
    preB = [1.0] + [0.0] * deg
    sufA = totA[:]
    for p, kind in pts:
        if kind == 0:
            sufA = poly_div_geo(sufA, 1 / p, deg)  # A-points < next y removed
        else:
            preB = poly_mul_geo(preB, 1 / p, deg)  # includes y
            for r in range(deg + 1):
                for s in range(1, deg + 1 - r):
                    S[r][s] += (1 / p) * preB[s - 1] * sufA[r]
    lA = sum(1 / p for p in A); lB = sum(1 / p for p in B)
    return S, lA, lB

for (X0, k, H, variant, eps) in [(100, 0.2, 2, 'drift', 0.1), (100, 0.2, 2, 'del', 0.15), (1000, 0.05, 4, 'drift', 0.025)]:
    M = T3.Model(X0, k, H, 2.0e8 if X0 == 100 else 1e9, variant, eps, 7)
    A = sorted(M.real.vals); B = [float(p) for p in M.toy.large_rat]
    U = min(A[-1], B[-1])
    b = 1 / M.toy.X0m
    for AA, BB, lab in [(A, B, 'realised above rational'), (B, A, 'rational above realised')]:
        S, lA, lB = mixed(AA, BB, U, 6)
        l = max(lA, lB)
        worst = max(S[r][s] / ((l + (r + s) * b) ** (r + s) / math.factorial(r + s))
                    for r in range(7) for s in range(7) if 2 <= r + s <= 6 and r >= 1 and s >= 1)
        print(f"X0={X0} {variant}: U={U:.3g} l_A={lA:.4f} l_B={lB:.4f}; {lab}: max over r,s>=1, r+s<=6 of "
              f"S_mixed/((l+(r+s)b)^(r+s)/(r+s)!) = {worst:.4f}")
