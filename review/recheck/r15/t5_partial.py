# Partial windows: Lemma blin(3) for the prime measure / nu0, and the nu1 partial windows inside mu_1 (Lemma margin(c)).
import sys, math, random
sys.argv = ['x', '100']
sys.path.insert(0, '/tmp/rhscratch/r15')
from toy_ops import *

def MAP1(q): return MAP(q) if q >= X0 else 0.0
def f01(q): return f0(q)
def f11(q): return f1(q)

rng = random.Random(9)
cnt_exceed = 0; tot = 0
worst = 0.0
for _ in range(400):
    x = rng.uniform(1e4, 4e6)
    partP = KQwin(x, 'P') - KQsh(x, MAP1)
    part0 = KQwin(x, 'nu0') - KQsh(x, f01)
    part1 = KQwin(x, 'nu1') - KQsh(x, f11)
    # weight of partial components and the paper's (3) bound
    w = 0.0; dens = 0.0; bnd_drop = 0.0; nu1_abs = 0.0
    for m in range(2, int(x / X0) + 1):
        q = x / m; P = gpf[m]
        if q < P <= (1 + kappa) * q:
            w += 1.0 / m
            dens = max(dens, MA_P_restr(q, P))
            bnd_drop += abs(f1(q)) / m          # what "dropping the restriction" would charge
            nu1_abs += abs(MA_P_restr(q, P) - MA_nu0_restr(q, P)) / m
    blin3 = sum(kappa / (2 * m) + 1 / math.sqrt(x * m) for m in range(1, int(x / X0 ** 2) + 2))
    tot += 1
    if nu1_abs > bnd_drop + 1e-15:
        cnt_exceed += 1
    worst = max(worst, abs(part1) / max(bnd_drop, 1e-300))
    if _ < 6:
        print(f"x={x:10.1f} partial weight={w:.4e} (blin(3) count bound {blin3:.4e}) max dens={dens:.3f} "
              f"partP={partP:+.2e} part0={part0:+.2e} part1={part1:+.2e} sum|f1(q)|/m' over partial={bnd_drop:.2e}")
print(f"nu1 partial |components| exceed |f1(q)|/m' bound in {cnt_exceed}/{tot} cases; max |part1|/sum|f1|/m' = {worst:.2f}")
