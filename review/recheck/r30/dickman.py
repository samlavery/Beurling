# Dickman rho via the positive power series on unit intervals (Bach-Peralta style), double precision.
# rho(k - xi) = rho(k) * sum_i C[k][i] xi^i, 0 <= xi <= 1;  logrho[k] = log rho(k).
# Recursion (from u rho'(u) = -rho(u-1)):  d_1 = 1/k, d_{i+1} = (i d_i + C[k-1][i]) / (k (i+1)),
# d_0 = sum_{i>=1} d_i / ((i+1)(k-1)) = rho(k)/rho(k-1)  (from k rho(k) = int_{k-1}^k rho, no cancellation).
import math, array, pickle, sys, os
def build(KMAX):
    logrho = array.array('d', [0.0] * (KMAX + 1))
    C = [None] * (KMAX + 1)
    C[1] = array.array('d', [1.0]); logrho[1] = 0.0
    prev = [1.0]
    for k in range(2, KMAX + 1):
        d = [0.0, 1.0 / k]
        i = 1
        while True:
            cp = prev[i] if i < len(prev) else 0.0
            nd = (i * d[i] + cp) / (k * (i + 1))
            d.append(nd); i += 1
            if i > 12 and i >= len(prev) and nd < 1e-22 * d[1] * 1e-6: break
            if i > 400: break
        d0 = sum(d[j] / ((j + 1) * (k - 1)) for j in range(1, len(d)))
        c = [1.0] + [x / d0 for x in d[1:]]
        # trim negligible tail relative to sum at xi=1
        S = sum(c); n = len(c)
        while n > 2 and c[n - 1] < 1e-21 * S: n -= 1
        c = c[:n]
        logrho[k] = logrho[k - 1] + math.log(d0)
        C[k] = array.array('d', c); prev = c
    return logrho, C
class Rho:
    def __init__(s, KMAX): s.logrho, s.C = build(KMAX); s.K = KMAX
    def logrho_at(s, x):
        if x <= 1: return 0.0
        k = math.ceil(x); xi = k - x; c = s.C[k]
        v = 0.0
        for a in reversed(c): v = v * xi + a
        return s.logrho[k] + math.log(v)
    def r(s, x):  # r(x) = rho(x-1)/(x rho(x)), x > 1
        return math.exp(s.logrho_at(x - 1) - s.logrho_at(x)) / x
if __name__ == "__main__":
    import time
    t = time.time(); R = Rho(int(sys.argv[1])); print("built", R.K, "in", round(time.time() - t, 1), "s")
    for x in (2, 3, 4, 5, 10):
        print(x, math.exp(R.logrho_at(x)))
    print("r(2) =", R.r(2.0), " exact 1/(2-2log2) =", 1 / (2 - 2 * math.log(2)))
    print("rho(2.5) =", math.exp(R.logrho_at(2.5)))
    with open(sys.argv[2], "wb") as f: pickle.dump((R.logrho, [list(c) if c is not None else None for c in R.C]), f)
