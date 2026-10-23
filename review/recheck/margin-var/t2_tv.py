# T2: exact total variation of g (and of each N-term) versus the paper's bounds, toy-scaled:
#   per N-term   TV <= 3.1/(N Lam)            -> toy: (3.1/1.0001) Me / N    (Me = sup_edge MA, analog of 1.0001/Lam)
#   on [a,b]     TV(g) <= (3.1/Lam)(log(b/a)+1) -> toy: (3.1/1.0001) Me (log(b/a)+1)
#   sup |g(x)| <= (1.0001/Lam)(k + X0/x)    -> toy: Me (k + X0/x)
import sys, math, random, bisect
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from toy_common import Toy


def thr(ell):
    """chi_ell(v)=1 iff v > thr(ell) (ell descending)."""
    t = 0.0
    prod = 1
    for r in ell:
        prod *= r
        t = max(t, r * prod)
    return t


def nterm_pieces(toy, N):
    """Return (v0, v1, events) for the N-term: on (v0,v1) it equals -mu(N) C(v)/(k v),
    C a step function switching on at the event points (sorted list of (v, +1))."""
    X0, k = toy.X0, toy.k
    v0, v1 = N * X0 / (1 + k), N * X0
    if toy.mu[N] == 0:
        return v0, v1, []
    f = sorted((p for p, _ in toy.factor(N)), reverse=True)
    ev = []
    a = bisect.bisect_left(toy.primes, X0)
    for p in toy.primes[a:]:
        if p >= (1 + k) * X0:
            break
        ell = [r for r in f if r > p]
        if len(ell) == len(f):  # s = 1
            continue
        on = max(N * p / (1 + k), thr(ell) if ell else 0.0)
        if on < v1:
            ev.append(max(on, v0))
    ev.sort()
    return v0, v1, ev


def tv_nterm(toy, N):
    k = toy.k
    v0, v1, ev = nterm_pieces(toy, N)
    if not ev:
        return 0.0, 0.0, 0.0
    tv = 0.0
    C = 0
    prev = v0
    rise = 0.0
    for e in ev:
        # smooth piece (prev, e) with value C/(k v): variation C/k (1/prev - 1/e)
        rise += C / k * (1 / prev - 1 / e)
        rise += 1 / (k * e)  # jump +1/(k e)
        C += 1
        prev = e
    rise += C / k * (1 / prev - 1 / v1)
    drop = C / (k * v1)
    return rise + drop, rise, drop


def tv_g(toy, a, b):
    """exact TV of g on [a,b] via merged breakpoints."""
    X0, k = toy.X0, toy.k
    pts = {a, b}
    Nlo = max(2, int(a / X0))
    Nhi = int((1 + k) * b / X0) + 2
    for N in range(Nlo, Nhi + 1):
        v0, v1, ev = nterm_pieces(toy, N)
        for t in [v0, v1] + ev:
            if a < t < b:
                pts.add(t)
    pts = sorted(pts)
    tv = 0.0
    prevS = None
    for i in range(len(pts) - 1):
        lo, hi = pts[i], pts[i + 1]
        if hi - lo < 1e-9:
            continue
        mid = 0.5 * (lo + hi)
        S = toy.g_formula(mid) * mid  # g = S/v on the piece
        tv += abs(S) * (1 / lo - 1 / hi)
        if prevS is not None:
            tv += abs(S - prevS) / lo
        prevS = S
    return tv


def run(X0, kappa, H, Nmax, intervals, seed):
    toy = Toy(X0, kappa, H, LIM=int((1 + kappa) * Nmax * X0) + 100)
    Me = toy.Me
    worstN = 0.0
    worst_rise = worst_drop = 0.0
    for N in range(2, Nmax + 1):
        tv, rise, drop = tv_nterm(toy, N)
        worstN = max(worstN, tv * N / Me)
        worst_rise = max(worst_rise, rise * N / Me)
        worst_drop = max(worst_drop, drop * N / Me)
    print(f"X0={X0} k={kappa}: Me={Me:.4f} (1/Lam={1/toy.Lam:.4f}); N<= {Nmax}: "
          f"max N*TV(Nterm)/Me = {worstN:.4f} (paper 3.1/1.0001=3.0997; derived bound 2+2k={2+2*kappa:.2f}); "
          f"max rise {worst_rise:.4f} (bound 1+2k), max drop {worst_drop:.4f} (bound 1)")
    rnd = random.Random(seed)
    worst_ratio = 0.0
    rows = []
    for (a, b) in intervals:
        tv = tv_g(toy, a, b)
        bnd = (3.1 / 1.0001) * Me * (math.log(b / a) + 1)
        worst_ratio = max(worst_ratio, tv / bnd)
        rows.append((a, b, tv, bnd))
    for a, b, tv, bnd in rows:
        print(f"   TV(g;[{a:.4g},{b:.4g}]) = {tv:.4f}   bound {bnd:.4f}   ratio {tv/bnd:.3f}")
    # sup |g| vs Me (k + X0/x)
    worst = 0.0
    for _ in range(3000):
        x = math.exp(rnd.uniform(math.log(2 * X0 / (1 + kappa)), math.log(Nmax * X0 / (1 + kappa))))
        gx = toy.g_formula(x)
        worst = max(worst, abs(gx) / (Me * (kappa + X0 / x)))
    print(f"   sup |g(x)| / (Me (k + X0/x)) over 3000 random x: {worst:.4f}  (paper: <= 1)")


if __name__ == '__main__':
    run(100, 0.2, 2, 3000, [(250, 2000), (2000, 20000), (2e4, 2e5), (1e5, 3e5), (250, 3e5)], 1)
    run(300, 0.1, 2, 1500, [(700, 7000), (7000, 7e4), (7e4, 4.5e5), (700, 4.5e5)], 2)
