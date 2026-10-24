import math
from fractions import Fraction
# primes and prime powers up to LIM
LIM = 10**7
sieve = bytearray([1])*(LIM+1); sieve[0]=sieve[1]=0
for i in range(2, int(LIM**0.5)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(range(i*i, LIM+1, i)))
pp = {}  # prime power -> log p
for p in range(2, LIM+1):
    if sieve[p]:
        q = p
        while q <= LIM:
            pp[q] = math.log(p); q *= p
keys = sorted(pp)
# psi as step function
import bisect
cum = []; s = 0.0
for k in keys: s += pp[k]; cum.append(s)
def psi(x):
    i = bisect.bisect_right(keys, x)
    return cum[i-1] if i else 0.0
# (1) sup over real x < 1500 of (psi(x)-psi(x/2))/x: breakpoints are prime powers b and 2b
bps = sorted(set([k for k in keys if k < 1500] + [2*k for k in keys if 2*k < 1500]))
best = max(((psi(b)-psi(b/2))/b, b) for b in bps)
print('max (psi(x)-psi(x/2))/x for x<1500:', best)
# check of x log2 + 3 log x + 3 <= 0.71 x at x=1500 and beyond (monotone)
x=1500; print('at 1500: lhs', x*math.log(2)+3*math.log(x)+3, ' rhs', 0.71*x)
# also verify the N-system bound psi(x)-psi(x/2) <= 0.71x directly up to 1e7 at breakpoints
mx = 0; arg=None
for k in keys:
    for b in (k, 2*k):
        if b <= LIM:
            v = (psi(b)-psi(b/2))/b
            if b >= 1500 and v > mx: mx, arg = v, b
print('max over breakpoints in [1500,1e7]:', mx, arg)
# (2) induction coefficient
print('log2+0.008+0.0043 =', math.log(2)+0.008+0.0043)
# (3) Mertens perturbation with eta1, eta2, sup eps1 <= 1e-3
print('eta2+sup eps1+1.42 eta1 <=', 1e-3+1e-3+1.42e-3)
# (4) S(x)-log x for N, x <= 1e7: max at jumps (x = prime power), inf just before jumps
smax = -1e9; smin = 1e9; s = 0.0; prev = 1.0
for k in keys:
    # just before k: S = s, x -> k^-
    smin = min(smin, s - math.log(k))
    s += pp[k]/k
    smax = max(smax, s - math.log(k))
smin = min(smin, s - math.log(LIM))
print('S(x)-log x on [1,1e7]: min %.6f max %.6f' % (smin, smax))
# Sp(x)-log x (primes only)
smax = -1e9; smin = 1e9; s = 0.0
for p in range(2, LIM+1):
    if sieve[p]:
        smin = min(smin, s - math.log(p)); s += math.log(p)/p; smax = max(smax, s - math.log(p))
print('Sp(x)-log x on [2,1e7]: min %.6f max %.6f (claimed range [-1.77,0.43])' % (smin, smax))
print('width 0.43+1.77 =', 0.43+1.77)
