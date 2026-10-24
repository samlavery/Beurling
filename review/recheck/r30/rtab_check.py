import sys, math, pickle, random, time
sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from bs_cert_arb import r_low, r_up, _rl
sys.path.insert(0, "/tmp/rhscratch/r30/indep")
from dickman import Rho
R = Rho.__new__(Rho)
with open("/tmp/rhscratch/r30/indep/rho270k.pkl","rb") as f: R.logrho, R.C = pickle.load(f)
R.K = len(R.logrho)-1
# integers: r_low(k) = _rl[k] <= r(k); also r_up(k) >= r(k)
worst_lo = math.inf; worst_up = math.inf; bad=0
for k in range(2, 269999):
    rt = R.r(float(k))
    gl = (rt - _rl[k]) / rt; gu = (r_up(float(k)) - rt) / rt
    if gl < -1e-12 or gu < -1e-12: bad += 1
    worst_lo = min(worst_lo, gl); worst_up = min(worst_up, gu)
print("integers 2..269998: violations(rel tol 1e-12) =", bad, " min (r - r_low)/r =", worst_lo, " min (r_up - r)/r =", worst_up)
random.seed(7); bad=0; wl=math.inf; wu=math.inf
for _ in range(200000):
    x = 1.0 + random.random()*(268000 if random.random()<0.5 else 60)
    rt = R.r(x)
    gl = (rt - r_low(x))/rt; gu = (r_up(x) - rt)/rt
    if gl < -1e-12 or gu < -1e-12: bad += 1; print("VIOL", x, rt, r_low(x), r_up(x))
    wl=min(wl,gl); wu=min(wu,gu)
print("random reals in [1,2.7e5]: violations =", bad, " min rel slack low =", wl, " up =", wu)
# r at a few points vs asymptotic xi (e^xi = 1 + x xi)
for x in (10.0, 100.0, 1e3, 1e4, 1e5, 2.5e5):
    xi = math.log(x*math.log(x))
    for _ in range(60): xi = xi - (math.exp(xi) - 1 - x*xi)/(math.exp(xi) - x)
    print(f"x={x:g} r_table={R.r(x):.12f} xi={xi:.12f} r_low={r_low(x):.6f} r_up={r_up(x):.6f}")
