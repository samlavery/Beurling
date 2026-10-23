# Resolvent identity of Lemma margin(d)(iii): rho_edge - g = (1+K_pt)^{-1}(K'_Q - K_pt) g, and the Lemma-M bound
# |rho_edge - g|(x) <= (sum_{n<=x/X0m} 1/n) * sup_{u<=x} |(K'_Q - K_pt) g (u)|.
import sys, math, random
sys.argv = ['x', '100']
sys.path.insert(0, '/tmp/rhscratch/r15')
from toy_ops import *

_gc = {}
def g(x):
    v = _gc.get(x)
    if v is None:
        v = resolventQ(x, mu_edge, cutoff=X0)
        _gc[x] = v
    return v
_dc = {}
def Dg(u):
    v = _dc.get(u)
    if v is None:
        v = KQsh(u, g, cutoff=X0, strict=True) - Kpt(u, g)
        _dc[u] = v
    return v

thr = 2 * X0 * X0m / (1 + kappa)
rng = random.Random(5)
xs = sorted([rng.uniform(1.2e4, 2.5e5) for _ in range(14)])
zero_viol = 0
for _ in range(300):
    u = rng.uniform(X0, thr * 0.999)
    if abs(Dg(u)) > 1e-15:
        zero_viol += 1
print("(K'_Q-K_pt)g(u) != 0 below 2 X0 X0^-/(1+k) =", round(thr, 1), ":", zero_viol, "of 300")
for x in xs:
    re = resolvent_pt(x, mu_edge)
    gx = g(x)
    rhs = resolvent_pt(x, Dg)
    harm = sum(1.0 / el[0] for el in get_els() if el[0] <= x / X0m)
    sup = max([abs(Dg(x / el[0])) for el in get_els() if el[0] <= x / X0m] + [0.0])
    print(f"x={x:10.1f} rho_edge={re:+.4e} g={gx:+.4e} lhs-rhs={(re-gx)-rhs:+.1e} |rho_edge-g|={abs(re-gx):.2e} "
          f"<= harm*sup={harm*sup:.2e} ({abs(re-gx) <= harm*sup + 1e-16})")
