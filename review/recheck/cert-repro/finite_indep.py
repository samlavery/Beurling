# Independent re-implementation of the finite-n checks, written from the paper text only.
# Ball arithmetic (python-flint arb) or exact rationals throughout; no floating-point sums.
import sys, time
from fractions import Fraction
from flint import arb, ctx
ctx.prec = 96
t0 = time.time()

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(range(i*i, n + 1, i)))
    return s

N7 = 10 ** 7
isp = sieve(N7)
primes = [i for i in range(N7 + 1) if isp[i]]
print('primes <= 1e7:', len(primes))

def prime_powers(limit):
    """sorted list of (p^k, p) for p^k <= limit"""
    pp = []
    for p in primes:
        if p > limit: break
        q = p
        while q <= limit:
            pp.append((q, p)); q *= p
    pp.sort()
    return pp

# 1. CM(i): sup_{1<=x<1500} (psi(x)-psi(x/2))/x.  psi right-continuous step function; on each piece where
# psi(x) and psi(x/2) are constant, the ratio decreases in x, so the sup is at the left ends: x in {1} U {q} U {2q}.
pp = prime_powers(1500)
brk = sorted({1} | {q for q, _ in pp} | {2 * q for q, _ in pp if 2 * q < 1500})
def psi_prod(x):  # exp(psi(x)) as an exact integer, x rational
    r = 1
    for q, p in pp:
        if q <= x: r *= p
    return r
best = None
for b in brk:
    if b >= 1500: continue
    num = Fraction(psi_prod(b), psi_prod(Fraction(b, 2)))
    assert num.denominator == 1
    val = arb(num.numerator).log() / b
    if best is None or val.upper() > best[0].upper(): best = (val, b)
print('1  CM(i): sup_{1<=x<1500} (psi(x)-psi(x/2))/x =', best[0].str(8), 'at x =', best[1],
      '| <= 0.6803:', bool(best[0] < arb('0.6803')), '| <= 0.71:', bool(best[0] < arb('0.71')))
x = arb(1500)
g = arb('0.71') * x - (x * arb(2).log() + 3 * x.log() + 3)
print('   x>=1500: 0.71x - (x log2 + 3 log x + 3) at 1500 =', g.str(6), '(> 0:', bool(g > 0), '); derivative 0.71-log2-3/x > 0 for x >= 1500:',
      bool(arb('0.71') - arb(2).log() - arb(3) / 1500 > 0))

# 2. CM(ii): S(x) - log x on [1, 1e7]. S right-continuous step function with jumps at prime powers q.
# On [b_i, b_{i+1}) S is constant: sup at b_i, inf approached at b_{i+1}-.
pp = prime_powers(N7)
S = arb(0); sup = (arb(0), 1); inf = None; prev = 1
for q, p in pp:
    cand = S - arb(q).log()           # value approached as x -> q-
    if inf is None or cand.lower() < inf[0].lower(): inf = (cand, q)
    S += arb(p).log() / q
    c2 = S - arb(q).log()             # value at x = q
    if c2.upper() > sup[0].upper(): sup = (c2, q)
cand = S - arb(N7).log()
if cand.lower() < inf[0].lower(): inf = (cand, N7)
print('2  CM(ii): over 1<=x<=1e7, S(x)-log x in [', inf[0].str(8), '(x->', inf[1], '-),', sup[0].str(8), '(x=', sup[1], ')];',
      len(pp), 'prime powers | inf >= -0.753:', bool(inf[0] > arb('-0.753')), '| sup <= 0:', bool(sup[0] <= 0))

# 3a/3b. F(Y) = sum_{Y<n<=2Y} 1/n is constant on [j/2, (j+1)/2): F = H(j) - H(floor(j/2)).
Hn = [arb(0)]
for n in range(1, 20001): Hn.append(Hn[-1] + arb(1) / n)
best = None
for j in range(144, 20000):
    v = Hn[j] - Hn[j // 2]
    if best is None or v.upper() > best[0].upper(): best = (v, j)
print('3a Lemma V: max_{72<=Y<1e4} sum_{Y<n<=2Y} 1/n =', best[0].str(10), 'on Y in [', best[1] / 2, ',', (best[1] + 1) / 2, ')',
      '| <= 0.69658:', bool(best[0] <= arb('0.69658')), '| > 0.69658:', bool(best[0] > arb('0.69658')), '| <= 0.70:', bool(best[0] < arb('0.70')))
ex = sum(Fraction(1, n) for n in range(73, 146))
print('   exact sum_{n=73}^{145} 1/n =', arb(ex.numerator) / ex.denominator, '; log2 + 1e-4 =', (arb(2).log() + arb('1e-4')).str(8),
      '<= 0.6933:', bool(arb(2).log() + arb('1e-4') < arb('0.6933')))
Hq = [Fraction(0)]
for n in range(1, 145): Hq.append(Hq[-1] + Fraction(1, n))
vals = [(Hq[j] - Hq[j // 2], j) for j in range(2, 144)]
mx = max(vals)
print('3b Lemma V: max_{1<=Y<72} =', mx[0], 'on Y in [', mx[1] / 2, ',', (mx[1] + 1) / 2, ') exact; <= 0.8334:', mx[0] <= Fraction(8334, 10000),
      '; 0.8334 - C0 <= 0.1334:', Fraction(8334, 10000) - Fraction(7, 10) <= Fraction(1334, 10000))

# 4. F_{1/2}(y) = y^{-1/2} sum_{n<=y} mu^2(n) n^{-1/2}; constant numerator on [n, n+1), so max at integers.
M6 = 10 ** 6
sqf = bytearray([1]) * (M6 + 1); sqf[0] = 0
for p in primes:
    if p * p > M6: break
    sqf[p*p::p*p] = bytearray(len(range(p*p, M6 + 1, p*p)))
s = arb(0); best = None
for n in range(1, M6 + 1):
    if sqf[n]: s += arb(n).rsqrt()
    v = s * arb(n).rsqrt()
    if best is None or v.upper() > best[0].upper(): best = (v, n)
print('4  F_1/2: max_{1<=y<=1e6} =', best[0].str(10), 'at y =', best[1], '| <= 1.3296:', bool(best[0] <= arb('1.3296')),
      '| <= 1.33:', bool(best[0] < arb('1.33')))

# 5. threshold mass: max over primes p < 400 of prod_{q<p} (1-1/q)^{-1} - 1.8 log p (exact product).
prod = Fraction(1); best = None
for p in primes:
    if p >= 400: break
    v = arb(prod.numerator) / prod.denominator - arb('1.8') * arb(p).log()
    if best is None or v.upper() > best[0].upper(): best = (v, p)
    prod *= Fraction(p, p - 1)
print('5  threshold-mass: max_{p<400} prod_{q<p}(1-1/q)^{-1} - 1.8 log p =', best[0].str(8), 'at p =', best[1],
      '| <= 0.25:', bool(best[0] < arb('0.25')))

# 6. sum_p log p/(p(p-1)): partial sum over p <= 1e7 plus tail
#    sum_{n>N} log n/(n(n-1)) <= int_N^oo log(t+1)/t^2 dt <= (log N + 1)/N + 1/(2N^2).
s = arb(0)
for p in primes: s += arb(p).log() / (p * (p - 1))
tail = (arb(N7).log() + 1) / N7 + arb(1) / (2 * N7 * N7)
tot = s + tail
print('6  CM(iii): sum_{p<=1e7} =', s.str(10), '+ tail <=', tail.str(4), '=', tot.str(10), '| <= 0.75537:', bool(tot < arb('0.75537')),
      '| <= 0.7554 (S-S_p bound):', bool(tot + 0 < arb('0.7554')))
print('runtime %.1f s' % (time.time() - t0))
