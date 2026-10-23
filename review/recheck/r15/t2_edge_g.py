# (d)(iii): g = (1+K'_Q)^{-1} mu_edge; coefficient formula; monotone numerators; |g| bounds; total variation;
# resolvent identity rho_edge - g = (1+K_pt)^{-1}(K'_Q - K_pt) g.
import sys, math, random
sys.argv = ['x', '100']
sys.path.insert(0, '/tmp/rhscratch/r15')
from toy_ops import *

rng = random.Random(11)
_gc = {}
def g(x):
    v = _gc.get(x)
    if v is None:
        v = resolventQ(x, mu_edge, cutoff=X0)
        _gc[x] = v
    return v

def factor(N):
    ps = []
    m = N
    while m > 1:
        p = gpf[m]; ps.append(p); m //= p
    return ps  # descending, with multiplicity

def g_formula(x):
    """Coefficient formula: sum_N 1/(k x) sum_{p in window} -mu(N) chi_{N_>}(x) 1[N_<= > 1]."""
    s = 0.0
    for N in range(2, int((1 + kappa) * x / X0) + 2):
        q = x / N
        if not (X0 / (1 + kappa) < q < X0):
            continue
        ps = factor(N)
        lo = X0; hi = (1 + kappa) * q
        i0 = bisect.bisect_left(PR, lo); i1 = bisect.bisect_right(PR, hi)
        num = 0
        for p in PR[i0:i1]:
            Ngt = 1
            for r in ps:
                if r > p:
                    Ngt *= r
            Nle = N // Ngt
            if Nle == 1:
                continue
            if mob[N] == 0:
                continue
            # chi of N_> (as an n): squarefree and r * prod_{r'|Ngt, r'>=r} r' < x
            chi = 1 if (Ngt == 1 or chiQ(Ngt, x)) else 0
            num += -mob[N] * chi
        s += num / (kappa * x)
    return s

mx = 0.0
for _ in range(300):
    x = rng.uniform(2 * X0 / (1 + kappa), 3e5)
    mx = max(mx, abs(g(x) - g_formula(x)))
print("(d)(iii) coefficient formula vs Lemma-M expansion: max diff", mx)

# |g(x)| <= sum_N MA[P](x/N)/N <= (max partial MA)(kappa + X0/x)-type
maxMA = 0.0
for N in range(1, 1):
    pass
qs = [X0 / (1 + kappa) + (X0 - X0 / (1 + kappa)) * i / 4000 for i in range(1, 4000)]
maxMA = max(MAP(q) for q in qs)
print("max partial-window MA[P] on (X0/(1+k),X0):", maxMA, " vs 1/Lam", 1 / Lam)
viol = 0
worst = 0.0
for _ in range(2000):
    x = rng.uniform(2 * X0 / (1 + kappa), 3e5)
    gx = abs(g(x))
    Ns = [N for N in range(2, int((1 + kappa) * x / X0) + 2) if X0 / (1 + kappa) < x / N < X0]
    bnd = maxMA * sum(1 / N for N in Ns)
    if gx > bnd + 1e-15:
        viol += 1
    worst = max(worst, gx / (maxMA * (kappa + X0 / x)))
print("|g| <= maxMA*sum 1/N violations:", viol, " max |g|/(maxMA(k+X0/x))", worst)

# Total variation of each N-term T_N(x) = num_N(x)/(k x) on its window; claim TV(T_N) <= ~2.0003(1+k)^2 * max|T_N| ... paper: 3.1/(N Lam)
def TN(N, x):
    q = x / N
    if not (X0 / (1 + kappa) < q < X0):
        return 0.0
    ps = factor(N)
    if mob[N] == 0:
        return 0.0
    i0 = bisect.bisect_left(PR, X0); i1 = bisect.bisect_right(PR, (1 + kappa) * q)
    num = 0
    for p in PR[i0:i1]:
        Ngt = 1
        for r in ps:
            if r > p:
                Ngt *= r
        if N // Ngt == 1:
            continue
        chi = 1 if (Ngt == 1 or chiQ(Ngt, x)) else 0
        num += -mob[N] * chi
    return num / (kappa * x)

worst_ratio = 0.0
mono_viol = 0
for N in range(2, 3000):
    if mob[N] == 0:
        continue
    a = N * X0 / (1 + kappa); b = N * X0
    xs = [a + (b - a) * i / 3000 for i in range(1, 3000)]
    vals = [TN(N, x) for x in xs]
    nums = [v * kappa * x for v, x in zip(vals, xs)]
    # monotone numerator in direction -mu(N)
    sgn = -mob[N]
    for i in range(1, len(nums)):
        if sgn * (nums[i] - nums[i - 1]) < -1e-9:
            mono_viol += 1
    tv = sum(abs(vals[i] - vals[i - 1]) for i in range(1, len(vals))) + abs(vals[-1]) + abs(vals[0])
    mxv = max(abs(v) for v in vals)
    if mxv > 0:
        worst_ratio = max(worst_ratio, tv / (maxMA / N))
print("monotone-numerator violations:", mono_viol, "; max TV(T_N)/(maxMA/N):", worst_ratio, "(paper: 3.1/1.0001 ~ 3.1)")
