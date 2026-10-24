# Toy check of the rho_det smooth-change bounds of correction 93.
# rho_det(u) = Psi([u,(1+k)u], X0)/(k u), Psi counts X0-smooth integers (all prime factors < X0).
import math, random, sys
X0 = 100; k = 0.15
NMAX = 2_000_000
# smallest-prime-factor sieve -> largest prime factor
lpf = list(range(NMAX + 1))
for p in range(2, NMAX + 1):
    if lpf[p] == p:  # p prime
        for m in range(2 * p, NMAX + 1, p):
            lpf[m] = p  # overwritten by larger primes: ends as largest prime factor
smooth = [0] * (NMAX + 1)
for n in range(1, NMAX + 1):
    smooth[n] = 1 if (n == 1 or lpf[n] < X0) else 0
S = [0] * (NMAX + 1)
for n in range(1, NMAX + 1):
    S[n] = S[n - 1] + smooth[n]

def cnt(a, b):  # #D in closed [a,b]
    lo = math.ceil(a - 1e-12); hi = math.floor(b + 1e-12)
    if hi < lo: return 0
    return S[hi] - S[lo - 1]

def rho(u): return cnt(u, (1 + k) * u) / (k * u)
def Psi(x): return S[math.floor(x + 1e-12)]

def check(delta, vmin, vmax, trials):
    worst = dict(r1=0, r2=0, rc=0, rn=0)
    eps = 1e-9
    for _ in range(trials):
        v = math.exp(random.uniform(math.log(vmin), math.log(vmax)))
        # critical v' candidates in [(1-2d)v, v]: integers m and m/(1+k), plus endpoints, +- eps
        lo = (1 - 2 * delta) * v
        cands = [lo, v]
        # sample a few critical points
        m1 = math.ceil(lo); m2 = math.floor(v)
        for m in random.sample(range(m1, m2 + 1), min(6, max(0, m2 - m1 + 1))) if m2 >= m1 else []:
            cands += [m, m + eps, m - eps]
        a = math.ceil((1 + k) * lo); b = math.floor((1 + k) * v)
        for m in random.sample(range(a, b + 1), min(6, max(0, b - a + 1))) if b >= a else []:
            cands += [m / (1 + k), m / (1 + k) + eps, m / (1 + k) - eps]
        # also perturb v to its critical points
        for vv in [v, math.floor(v) + 0.0, math.floor(v) - eps + 1, math.ceil((1 + k) * v) / (1 + k) - eps]:
            if vv < X0: continue
            for vp in cands:
                if not (max(X0, (1 - 2 * delta) * vv) <= vp <= vv): continue
                A = cnt(vv, (1 + k) * vv); Ap = cnt(vp, (1 + k) * vp)
                d = abs(A / (k * vv) - Ap / (k * vp))
                L = 2 * delta * (1 + k) * vv
                b1 = 2 * (L + 1) / (k * vv)
                b2 = 3 * Psi(2 * vv) / (k * vv)
                worst['r1'] = max(worst['r1'], d / b1)
                worst['r2'] = max(worst['r2'], d / b2)
                worst['rc'] = max(worst['rc'], abs(A - Ap) / (L + 1))
                nrm = Ap * abs(1 / (k * vv) - 1 / (k * vp))
                worst['rn'] = max(worst['rn'], nrm / (2.01 * delta * (1 + 1 / (k * vv))))
    return worst

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
for delta in [1e-4, 1e-3, 5e-3, 0.02, 0.05, 0.07, 0.1, 0.2]:
    w = check(delta, X0, NMAX / 2.5, 20000)
    print(f"delta={delta:<7} 2delta<kappa={2*delta<k}  max|D|/bound1={w['r1']:.4f}  max|D|/bound2={w['r2']:.4f}  "
          f"max|countdiff|/(L+1)={w['rc']:.4f}  max norm/(2.01d(1+1/kv))={w['rn']:.4f}")
