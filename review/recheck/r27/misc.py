import math, random
from fractions import Fraction as F
# (a) Rankin: zeta_y(sigma) = prod_{p<y}(1-p^-sigma)^-1 with sigma = 1-1/(2 log y); need <= 5 Lam^1.65 (Lam = log y)
def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
for y in [10**4, 10**6, 10**7]:
    L = math.log(y); sig = 1 - 1 / (2 * L)
    lz = sum(-math.log(1 - p ** (-sig)) for p in primes(y - 1))
    print(f"y={y:.0e}: zeta_y(sigma)/Lam={math.exp(lz)/L:.3f}  5Lam^1.65/zeta={5*L**1.65/math.exp(lz):.2f}")
# (b) count difference with D = all integers (densest case), exact rationals, kappa=3/20, 2delta<kappa
k = F(3, 20)
def cnt(a, b):
    lo = math.ceil(a); hi = math.floor(b); return max(0, hi - lo + 1)
worst = F(0)
random.seed(3)
for _ in range(20000):
    d = F(random.randint(1, 70), 1000)          # delta in (0, 0.07], 2delta < kappa
    v = F(random.randint(100 * 1000, 3000 * 1000), 1000)
    # critical v' : integers m in [(1-2d)v, v], and m/(1+k)
    lo = (1 - 2 * d) * v
    cands = [lo, v]
    for m in range(math.ceil(lo), math.floor(v) + 1): cands.append(F(m))
    for m in range(math.ceil((1 + k) * lo), math.floor((1 + k) * v) + 1): cands.append(F(m) / (1 + k))
    for vp in cands:
        if not (lo <= vp <= v): continue
        A = cnt(v, (1 + k) * v); Ap = cnt(vp, (1 + k) * vp)
        L = 2 * d * (1 + k) * v
        r = F(abs(A - Ap)) / (L + 1)
        if r > worst: worst = r
        tot = abs(F(A) / (k * v) - F(Ap) / (k * vp)) / (2 * (L + 1) / (k * v))
        assert tot <= 1, (v, vp, d)
print("all-integers D: max |count diff|/(2delta(1+k)v+1) =", float(worst), "(<= 1 required)")
# (c) R_j' smooth change: R(x) = a x^th cos(g log x); compare |R'(v)-R'(v')| with delta*g*kap*(v/xj)^(th-1), |v-v'|<=2 delta v
th, g, xj = 0.3, 2000.0, 1e5
kap = 1e-3; a = kap / 2 / (g * xj ** (th - 1))       # a g xj^(th-1) = kap/2
def Rp(x): L = math.log(x); return a * x ** (th - 1) * (th * math.cos(g * L) - g * math.sin(g * L))
mx = 0
for _ in range(200000):
    v = xj * math.exp(random.uniform(0, 8)); d = 10 ** random.uniform(-9, -6)
    vp = v * (1 - 2 * d * random.random())
    r = abs(Rp(v) - Rp(vp)) / (d * g * kap * (v / xj) ** (th - 1))
    mx = max(mx, r)
print("R_j': max |R'(v)-R'(v')| / (delta*gamma*kappa*(v/x_j)^(theta-1)) =", round(mx, 4), "(paper's per-level room: factor 2/(1-theta)/F_theta)")
