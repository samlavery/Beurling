# Identity checks: Lemma M (realised, decision order), eq:ratid, eq:shdecomp bookkeeping, Lemma margin(d)(i),
# the coefficient formula of (d)(iii), and the resolvent identity rho_edge - g = (1+K_pt)^{-1}(K'_Q - K_pt) g.
import sys, math, random
sys.argv = ['x', '100']
sys.path.insert(0, '/tmp/rhscratch/r15')
from toy_ops import *
from functools import lru_cache

print("X0", X0, "kappa", kappa, "H", H, "X0m", X0m, "#jit", len(JIT), "jit below X0:", [v for v, t in JIT if v < X0])
els = get_els()
print("#elements <= WMAX", len(els))

# ---- Lemma M: recursion vs formula, realised system ----
def resolvent_rec(x, h):
    memo = {}
    def rho(y):
        if y in memo:
            return memo[y]
        r = h(y) - Kpt(y, rho)
        memo[y] = r
        return r
    return rho(x)

rng = random.Random(7)
def htest(y):
    return 0.0 if y < X0 else math.sin(y) + 1.0 / math.log(y)
maxerr = 0.0
for _ in range(25):
    x = rng.uniform(2 * X0m, 60000)
    a = resolvent_pt(x, htest)
    b = resolvent_rec(x, htest)
    maxerr = max(maxerr, abs(a - b))
print("Lemma M (realised, decision order): max |formula - recursion| =", maxerr)

# ---- eq:ratid: 1 - rho_det = (1+K_Q) MA[P] + (k x - #ints)/(k x), exactly ----
def is_smooth(n):
    return gpf[n] < X0
def rho_det(u):
    lo = math.ceil(u); hi = math.floor((1 + kappa) * u)
    return sum(1 for n in range(lo, hi + 1) if is_smooth(n)) / (kappa * u)
mx = 0.0
for _ in range(300):
    u = rng.uniform(X0, 40000)
    lo = math.ceil(u); hi = math.floor((1 + kappa) * u)
    nint = hi - lo + 1
    lhs = 1 - rho_det(u)
    rhs = MAP(u) + KQwin(u, 'P', full=True) + (kappa * u - nint) / (kappa * u)
    mx = max(mx, abs(lhs - rhs))
print("eq:ratid exact residual max:", mx)

# ---- the split K_Q MA[P] = K_Q(MA[P]1) + mu_edge ----
mx = 0.0
for _ in range(300):
    u = rng.uniform(X0, 40000)
    mx = max(mx, abs(KQwin(u, 'P', full=True) - KQwin(u, 'P', full=False) - mu_edge(u)))
print("K_Q MA[P] - K_Q(MA[P]1) - mu_edge, max:", mx)

# ---- eq:shdecomp: rho_sh = MA[P]1 + rho_edge + (1+K_pt)^{-1}(mu0+mu1) with mu0+mu1 := (K_Q - K_pt)(MA[P]1) + O ----
def T1(u):  # (1 - rho_det) 1_{[X0,oo)}
    return 0.0 if u < X0 else 1 - rho_det(u)
def MAP1(u):
    return 0.0 if u < X0 else MAP(u)
def mu01(u):
    if u < X0:
        return 0.0
    lo = math.ceil(u); hi = math.floor((1 + kappa) * u)
    O = (kappa * u - (hi - lo + 1)) / (kappa * u)
    return KQwin(u, 'P', full=False) - Kpt(u, MAP1) + O
mx = 0.0
for _ in range(15):
    x = rng.uniform(X0m, 30000)
    lhs = resolvent_pt(x, T1)
    rhs = MAP1(x) + resolvent_pt(x, mu_edge) + resolvent_pt(x, mu01)
    mx = max(mx, abs(lhs - rhs))
print("eq:shdecomp residual max:", mx)

# ---- (d)(i): rho_edge(x) = -sum_N mu(N) MA[P](x/N)/N on X0 <= x <= X0^1.9 ----
mx = 0.0
for _ in range(400):
    x = rng.uniform(X0, X0 ** 1.9)
    a = resolvent_pt(x, mu_edge)
    b = 0.0
    for N in range(2, int((1 + kappa) * x / X0) + 2):
        if X0 / (1 + kappa) < x / N < X0:
            b += -mob[N] * MAP(x / N) / N
    mx = max(mx, abs(a - b))
print("(d)(i) residual max on [X0, X0^1.9]:", mx)
