"""Independent brute-force check of the new (S3)(a): enumerate block contents explicitly (sets of realised primes,
exponent vectors in the K chain rows up to a cap), with chi cut-offs, against Phi_t(a) = G_t(Eu(a))/Eu(a)^K,
G_t(E) = int_E^A K x^{j-1} G_{t-1}(x) dx, G_{t-1} itself produced by the recursion (eq:A-Grec) from G_0 = 1 through a
random earlier composition.  Tiny primes (2, 3, 5, ...) are allowed, where the elementary inequalities are loosest.
Brute force uses exponents <= EMAX per row; the truncation only lowers the LHS, so a violation would be real."""
import itertools, math, random, sys

EMAX = 7

def grec(Gprev, K, j, A, grid):
    """G_t on a log-grid by trapezoid on y=log x (Gprev given on the same grid)."""
    ys = [math.log(x) for x in grid]
    f = [K * grid[i] ** j * Gprev[i] for i in range(len(grid))]   # K x^{j-1} G dx = K x^j G dy
    out = [0.0] * len(grid)
    acc = 0.0
    for i in range(len(grid) - 2, -1, -1):
        acc += 0.5 * (f[i] + f[i + 1]) * (ys[i + 1] - ys[i])
        out[i] = acc
    return out

def interp(grid, vals, x):
    if x >= grid[-1]:
        return 0.0
    lo, hi = 0, len(grid) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if grid[mid] <= x: lo = mid
        else: hi = mid
    t = (math.log(x) - math.log(grid[lo])) / (math.log(grid[hi]) - math.log(grid[lo]))
    return vals[lo] * (1 - t) + vals[hi] * t

def vec_sum(g, K, nonzero):
    """sum over exponent vectors in K rows (entries <= EMAX) of g^{-|v|}, zero vector excluded if nonzero."""
    s1 = sum(g ** (-e) for e in range(EMAX + 1))
    tot = s1 ** K
    return tot - 1 if nonzero else tot

def run(seed):
    rnd = random.Random(seed)
    n = rnd.randint(1, 9)
    pool = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    primes = sorted(rnd.sample(pool, n))
    Ea = rnd.choice([1.0, 1.5, 2.0])
    E = [Ea]
    for g in primes:
        E.append(E[-1] / (1 - 1 / g))
    cut = rnd.randint(1, n)
    A = E[cut] * rnd.choice([1.0, 1.0, 1.3])      # A_top >= Eu(u*)
    # earlier composition producing G_{t-1}
    m = rnd.randint(0, 3)
    grid = [Ea * (A / Ea) ** (i / 4000) for i in range(4001)] if A > Ea else [Ea, Ea * 1.0000001]
    G = [1.0] * len(grid)
    Kc = 0
    if m > 0:
        parts = []
        left = m
        while left > 0:
            p = rnd.randint(0, left)   # allow j = 0 stages
            if Kc == 0 and p == 0: p = 1
            parts.append(p); left -= p; Kc += p
        Kc = 0
        for p in parts:
            Kc += p
            G = grec(G, Kc, p, A, grid) if A > Ea else [0.0] * len(grid)
    j = rnd.randint(0, 3)
    if m + j == 0: j = 1
    K = m + j
    # brute force LHS: contents = nonempty subsets S of primes[:]; latest f; chi(f) = 1 iff index < cut
    lhs = 0.0
    for size in range(1, n + 1):
        for S in itertools.combinations(range(n), size):
            fi = S[-1]
            if fi >= cut: continue
            w = vec_sum(primes[fi], K, True)
            for gi in S[:-1]:
                w *= vec_sum(primes[gi], K, True)
            E2 = E[fi + 1]
            Phi = (interp(grid, G, E2) if m > 0 else 1.0) / E2 ** m
            lhs += w * Phi
    Gt = grec(G, K, j, A, grid) if A > Ea else [0.0] * len(grid)
    rhs = Gt[0] / Ea ** K
    return lhs, rhs, (primes, Ea, A, m, j, cut)

worst = 0; viol = 0; N = 1500
for s in range(N):
    l, r, info = run(s)
    if r > 0:
        worst = max(worst, l / r)
    if l > r * (1 + 1e-4) + 1e-12:
        viol += 1
        if viol < 5: print("VIOLATION", l, r, info)
print(f"(S3)(a) brute force: {N} random cases (primes from 2, j_t=0 allowed, chi cut-offs), {viol} violations, "
      f"max LHS/RHS = {worst:.4f}")
