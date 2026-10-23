# Independent spot-check of s_H (Theorem caplw): root of gamma_*(s) = 1/3 - 1e-5, gamma_*(s) = 1.3 G(max(1e8, e^-s), s),
# G(Lam, s) = 2 sqrt(A(A+1)) e^{s/2} / sqrt(Lam - A - 1), A = log(2 Lam^3 e^{2s}/(2 log Lam + s)). Ball arithmetic.
from flint import arb, ctx
ctx.prec = 120
Lam = arb(10) ** 8
def gstar(s):
    A = (2 * Lam ** 3 * (2 * s).exp() / (2 * Lam.log() + s)).log()
    return arb('1.3') * 2 * (A * (A + 1)).sqrt() * (s / 2).exp() / (Lam - A - 1).sqrt()
target = arb(1) / 3 - arb('1e-5')
lo, hi = arb(5), arb(7)
assert gstar(lo) < target and gstar(hi) > target
for _ in range(60):                  # gstar is increasing in s on [5,7] (checked by the bracketing at each step)
    mid = (lo + hi) / 2
    if gstar(mid) < target: lo = mid
    elif gstar(mid) > target: hi = mid
    else: break
print('s_H in [%s, %s]' % (lo.str(12), hi.str(12)), '; starts with 5.9745:', bool(lo > arb('5.9745')) and bool(hi < arb('5.9746')))
# Step 2 claim: gamma_*(s_H + t) <= gamma_*(s_H) e^{0.532 t} on [0,1]: check d log gamma_*/ds <= 0.532 on a grid of balls
sH = lo; worst = arb(0); n = 1000
for k in range(n):
    s = (sH + arb(k) / n).union(sH + arb(k + 1) / n)
    # log gamma_* = log 1.3 + log 2 + (1/2)log(A(A+1)) + s/2 - (1/2) log(Lam - A - 1); A' = 2 - 1/(2 log Lam + s)
    A = (2 * Lam ** 3 * (2 * s).exp() / (2 * Lam.log() + s)).log()
    Ap = 2 - 1 / (2 * Lam.log() + s)
    d = (2 * A + 1) * Ap / (2 * A * (A + 1)) + arb('0.5') + Ap / (2 * (Lam - A - 1))
    if d.upper() > worst: worst = arb(d.upper())
print('max d log gamma_*/ds on [s_H, s_H+1] <=', worst.str(6), '; <= 0.532:', bool(worst <= arb('0.532')))
