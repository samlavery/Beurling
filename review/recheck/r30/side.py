import sys, math, random
sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from bs_cert_arb import r_low, r_up
from flint import arb, ctx
ctx.prec = 200
# Step 6: on the tail w > U(m), need 1 + w > u* = U(l) + 1/2, i.e. w* >= U(l) - 1/2 where w* = U(m(w*))
def U(x, tau): x = arb(x); return x.root(4) * (1 + (2 * (x / tau).log() + 4).sqrt())
worst = -1e9; random.seed(2)
for _ in range(3000):
    l = 10 ** random.uniform(math.log10(3e9), 18); tau = arb(10) ** random.uniform(8, math.log10(l / 30))
    if random.random() < 0.3: tau = arb(10) ** 8
    a, b = arb(1.0), U(l, tau) + 2
    for _ in range(120):
        m = (a + b) / 2
        if m - U(arb(l) * m / (1 + m), tau) > 0: b = m
        else: a = m
    worst = max(worst, float((U(l, tau) - a).upper()))
print("max over samples of U(l) - w*  =", worst, " (Step 6 needs <= 1/2)")
print("r_low(4e5-1) =", r_low(4e5 - 1), " r_low(4e5) =", r_low(4e5), " (paper: r_low >= 15.3 beyond 4e5)")
