# T1: validate the coefficient formula for g = (1+K'_Q)^{-1} mu_edge against
#     (a) Lemma M (rational) and (b) the Neumann recursion g = mu_edge - K'_Q g (no Lemma M).
import sys, math, random
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from toy_common import Toy

sys.setrecursionlimit(10000)


def run(X0, kappa, H, vmax, nsamp, seed):
    toy = Toy(X0, kappa, H, LIM=int(vmax) + 10)
    memo = {}

    def g_neu(v):
        key = round(v, 7)
        if key in memo:
            return memo[key]
        s = toy.mu_edge(v)
        mmax = int((1 + kappa) * v / (2 * X0)) + 1
        for m in range(2, mmax + 1):
            if not (toy.Pp[m] * m < v):
                continue
            if v / m < X0:
                continue
            s -= g_neu(v / m) / m
        memo[key] = s
        return s

    rnd = random.Random(seed)
    worst_fd = worst_fn = 0.0
    nz = 0
    for _ in range(nsamp):
        v = rnd.uniform(X0, vmax)
        a = toy.g_formula(v)
        b = toy.g_direct(v)
        c = g_neu(v)
        if abs(a) > 0:
            nz += 1
        worst_fd = max(worst_fd, abs(a - b))
        worst_fn = max(worst_fn, abs(a - c))
    print(f"X0={X0} k={kappa} v<= {vmax:.3g}: samples={nsamp} nonzero={nz} "
          f"max|formula-LemmaM|={worst_fd:.2e} max|formula-Neumann|={worst_fn:.2e}  Me={toy.Me:.4f} 1/Lam={1/toy.Lam:.4f}")


if __name__ == '__main__':
    run(100, 0.2, 2, 6.0e4, 600, 1)
    run(300, 0.1, 2, 4.0e5, 300, 2)
