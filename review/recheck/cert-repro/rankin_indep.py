# Independent check of the Rankin constants (working-tree Lemma rowweights (c),(e); App B app:cert-rankin).
# R(sigma) = sum_p (-log(1 - p^-sigma) - p^-sigma) = sum_{k>=2} P(k sigma)/k, P = prime zeta function, computed by
# Moebius inversion P(s) = sum_{n>=1} mu(n)/n log zeta(n s), with rigorous tails. A different method from the
# script's direct prime sum. A direct prime sum (p <= 10^6, Euler-Maclaurin-free tail) is computed as a cross-check.
import time
from flint import arb, ctx
ctx.prec = 300
t0 = time.time()

def mobius_upto(n):
    mu = [1] * (n + 1); isp = [True] * (n + 1)
    for p in range(2, n + 1):
        if isp[p]:
            for m in range(p, n + 1, p):
                if m > p: isp[m] = False
                mu[m] = -mu[m]
            for m in range(p * p, n + 1, p * p): mu[m] = 0
    return mu

NM = 120; KM = 250
mu = mobius_upto(NM)
two = arb(2)

def zeta_m1_bound(t):          # zeta(t) - 1 <= 2^-t (1 + 2/(t-1)), t > 1
    return two ** (-t) * (1 + 2 / (t - 1))

def P(s):                      # prime zeta, s >= 1.38
    acc = arb(0)
    for n in range(1, NM + 1):
        if mu[n]: acc += arb(mu[n]) / n * (n * s).zeta().log()
    # tail: |sum_{n>NM} mu(n)/n log zeta(ns)| <= sum_{n>NM} (zeta(ns)-1)/n
    t = (NM + 1) * s
    tail = zeta_m1_bound(t) / (NM + 1) / (1 - two ** (-s))
    return acc + arb(0, tail.upper())

def R(sig):
    sig = arb(sig)
    acc = arb(0)
    for k in range(2, KM + 1): acc += P(k * sig) / k
    t = (KM + 1) * sig
    tail = zeta_m1_bound(t) / (KM + 1) / (1 - two ** (-sig))   # P(t) <= zeta(t) - 1
    return acc + arb(0, tail.upper())

for sig, claim in (('0.69', '0.77'), ('0.75', '0.63')):
    r = R(sig)
    print('R(%s) = %s   <= %s: %s' % (sig, r.str(15), claim, bool(r < arb(claim))))

# cross-check: direct prime sum to 10^6 + tail bound sum_{n>N} n^{-2s}/(2(1-n^{-s})) (all integers n > N)
ctx.prec = 80
N = 10 ** 6
s_ = bytearray([1]) * (N + 1); s_[0] = s_[1] = 0
for i in range(2, int(N ** 0.5) + 1):
    if s_[i]: s_[i*i::i] = bytearray(len(range(i*i, N + 1, i)))
for sig in ('0.69', '0.75'):
    sg = arb(sig); acc = arb(0)
    for p in range(2, N + 1):
        if s_[p]:
            x = arb(p) ** (-sg)
            acc += -(-x).log1p() - x
    # -log(1-x) - x <= x^2/(2(1-x)); sum_{n>N} n^{-2s} <= N^{1-2s}/(2s-1)
    tail = arb(N) ** (1 - 2 * sg) / (2 * sg - 1) / (2 * (1 - arb(N) ** (-sg)))
    print('direct: sum_{p<=1e6} = %s, + tail <= %s  -> R(%s) in [%s, %s]' % (acc.str(10), tail.str(5), sig,
          acc.lower().str(10), (acc + tail).upper().str(10)))
ctx.prec = 120
E11 = arb(11).ei() - arb(11).exp() / 11 - arb(11).exp() / 121
print('Ei(11) - e^11/11 - e^11/121 =', E11.str(12), '<= 134:', bool(E11 < 134))
f = lambda x: arb('2.75') / x + 134 * x * x * (-x).exp()
print('f(x) = 2.75/x + 134x^2e^-x: f(11) =', f(arb(11)).str(10), '< 1:', bool(f(arb(11)) < 1),
      '; f decreasing on [2,oo) since d/dx(x^2 e^-x) = x(2-x)e^-x < 0 and -2.75/x^2 < 0')
# sanity: Ei(x) <= (e^x/x)(1+2/x) at sample x >= 11, and the integrated-by-parts form
for xx in (11, 12, 15, 25, 50, 100, 411, 1000):
    x = arb(xx)
    lhs = x.ei(); rhs = x.exp() / x * (1 + 2 / x); rhs2 = x.exp() / x * (1 + 1 / x + arb('2.75') / x ** 2) + 134
    assert lhs < rhs and lhs < rhs2, xx
print('Ei(x) <= (e^x/x)(1+2/x) and <= (e^x/x)(1+1/x+2.75/x^2)+134 at x in {11,...,1000}: OK')
v = arb('1.5') ** arb('0.75')
print('(3/2)^(3/4) =', v.str(12), '<= 1.3555:', bool(v < arb('1.3555')))
e = (arb(2).log() / 4).ei()
print('Ei(log2/4) =', e.str(12), '>= -1:', bool(e > -1))
# Ein <= Ei for x >= 11: Ein(x) = Ei(x) - gamma - log x
print('gamma + log 11 > 0:', bool(arb.const_euler() + arb(11).log() > 0))
print('runtime %.1f s' % (time.time() - t0))
