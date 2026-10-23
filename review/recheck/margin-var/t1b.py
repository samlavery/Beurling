import sys, math, random
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from toy_common import Toy
sys.setrecursionlimit(100000)
X0, kappa = 100, 0.2
toy = Toy(X0, kappa, 2, LIM=3_000_000)
memo = {}
def g_neu(v):
    key = round(v, 6)
    if key in memo: return memo[key]
    s = toy.mu_edge(v)
    mmax = int((1 + kappa) * v / (2 * X0)) + 1
    for m in range(2, mmax + 1):
        if not (toy.Pp[m] * m < v) or v / m < X0: continue
        s -= g_neu(v / m) / m
    memo[key] = s
    return s
rnd = random.Random(5)
w1 = w2 = 0.0; cnt2P = 0
for i in range(60):
    v = rnd.uniform(1.0e6, 2.5e6)
    a = toy.g_formula(v); b = toy.g_direct(v)
    w1 = max(w1, abs(a - b))
    if i < 8:
        c = g_neu(v); w2 = max(w2, abs(a - c))
print(f"v in [1e6,2.5e6]: max|formula-LemmaM|={w1:.2e} (60 pts), max|formula-Neumann|={w2:.2e} (8 pts)")
