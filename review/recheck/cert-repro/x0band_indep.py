# Independent re-implementation of the x0-band small-range certificate, from the paper's definition of B(n)
# (Proposition xb-ranges (i)):
#   B(n) = (1/n) [ mu^2(n)/2 + (1/2) sum_{d|n, 1<d<n} (2 mu^2(d) + (1/2) lam X(d)/d) ],
#   X(d) = sum_{e|d, 1<e<d} mu^2(e) e Hord(d/e),  lam = 1.0001.
# Everything is exact integer arithmetic: X(d)/d is replaced by ceil(X(d) * 2^40 / d) / 2^40 (an upper bound), and
# B(n) <= W(n) / (n * 4 * 10^4 * 2^40) with W(n) an integer. The comparison with 5/12 is exact.
import sys, time
from fractions import Fraction
from flint import arb, ctx
ctx.prec = 80
t0 = time.time()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 6
SH = 40
SC = 4 * 10 ** 4 << SH           # common scale 4 * 10^4 * 2^40

# mu^2 via smallest-prime sieve
mu2 = bytearray([1]) * (N + 1); mu2[0] = 0
r = int(N ** 0.5) + 1
isp = bytearray([1]) * (r + 1); isp[0] = isp[1] = 0
for p in range(2, r + 1):
    if isp[p]:
        isp[p*p::p] = bytearray(len(range(p*p, r + 1, p)))
        if p * p <= N: mu2[p*p::p*p] = bytearray(len(range(p*p, N + 1, p*p)))
# Hord: Hord(1) = 1, Hord(m) = sum_{d|m, d<m} Hord(d); push each finished value to its proper multiples
H = [0] * (N + 1); H[1] = 1
for d in range(1, N // 2 + 1):
    h = H[d]
    for m in range(2 * d, N + 1, d): H[m] += h
# X(d) = sum over e | d, 1 < e < d, mu^2(e) e Hord(d/e): loop over squarefree e >= 2 and cofactors k >= 2
X = [0] * (N + 1)
for e in range(2, N // 2 + 1):
    if mu2[e]:
        k = 2
        for d in range(2 * e, N + 1, e):
            X[d] += e * H[k]; k += 1
# per-divisor weight, scaled by SC: SC * (mu^2(d) + lam X(d) / (4 d)) <= w(d)  (exact integer upper bound)
w = [0] * (N + 1)
for d in range(2, N + 1):
    q = -((-X[d] << SH) // d)                     # ceil(X(d) 2^40 / d)
    w[d] = mu2[d] * SC + 10001 * q                # 4*10^4*2^40 * lam/4 * X/d = 10001 * 2^40 * X/d
W = [0] * (N + 1)
for n in range(2, N + 1): W[n] = mu2[n] * (SC // 2)
for d in range(2, N // 2 + 1):
    wd = w[d]
    for n in range(2 * d, N + 1, d): W[n] += wd
# SC * n * B(n) <= W(n), i.e. B(n) <= W(n) / (SC * n)
# check: 12 W(n) <= 5 * SC * n, report the top values exactly
viol = []; top = []
for n in range(2, N + 1):
    lhs = 12 * W[n]; rhs = 5 * SC * n
    if lhs > rhs: viol.append(n)
    if lhs == rhs: top.append(n)
print('N =', N, ' max Hord =', max(H), ' max X =', max(X))
print('violations of B(n) <= 5/12:', viol[:10], ' equality cases:', top)
vals = sorted(((Fraction(W[n], SC * n), n) for n in range(2, N + 1)), reverse=True)[:8]
print('top upper bounds of B(n):', [(n, float(v)) for v, n in vals])
print('B(6) upper bound exactly =', Fraction(W[6], SC * 6))
for a in range(1, 6):
    lo = 10 ** a
    m = max((Fraction(W[n], SC * n), n) for n in range(lo, N + 1))
    print('sup_{%d<=n<=N} B(n) <= %.6f (at n=%d)' % (lo, float(m[0]), m[1]))
# analytic tail ingredients (paper 04x, proof of (i))
s = arb('1.8') - arb('3e-6')
A = 1 / (2 - s.zeta()) - 1
print('A(1.8-3e-6) =', A.str(8), ' <= 7.4915:', bool(A < arb('7.4915')), ' A(1.8) =', (1 / (2 - arb('1.8').zeta()) - 1).str(8))
c = arb('0.25') * arb('7.4915') * arb(2) ** arb('0.2')
print('(1/4) 7.4915 2^0.2 =', c.str(8), ' <= 2.152:', bool(c <= arb('2.152')))
n = arb(10 ** 6)
tb = (arb('0.5') + arb('1.64') * n.sqrt()) / n + arb('2.152') * n ** arb('-0.2')
print('tail bound at n = 1e6:', tb.str(8), ' <= 0.14:', bool(tb < arb('0.14')), ' (decreasing in n)')
print('max prod_{p|n} 2 p^{-1/2} = 4/sqrt6 =', (4 / arb(6).sqrt()).str(8), ' <= 1.64:', bool(4 / arb(6).sqrt() < arb('1.64')))
print('1.0001*(1.01+1e-18) * 5/12 + e^{-0.99e8} <= 0.42088:', bool(arb('1.0001') * (arb('1.01') + arb('1e-18')) * 5 / 12 < arb('0.42088')),
      (arb('1.010102') * 5 / 12).str(8))
print('runtime %.1f s' % (time.time() - t0))
