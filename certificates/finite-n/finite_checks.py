# Finite computations on the integers N quoted in Section 5 of the paper (noise section).
# Standard library only. Run:  python3 -I -B finite_checks.py
#
# Each check prints one line: the quantity, the value found, where it is attained, and the bound the paper uses.
# Real-variable suprema are reduced to finitely many points by the step structure stated in each check.
# Floating point: every quantity is a sum of at most 10^6 nonnegative doubles, or (check 2) at most 7*10^5 terms of
# size <= 0.35; the accumulated rounding error is below the stated "err" in each line, and every margin printed
# exceeds it by many orders of magnitude. Checks 3b and 5 are exact rational arithmetic.
import math
import time
from fractions import Fraction

T0 = time.time()


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p :: p] = bytearray(len(range(p * p, n + 1, p)))
    return [i for i in range(n + 1) if s[i]]


def psi_table(n):
    """psi[k] = sum_{p^j <= k} log p, k = 0..n."""
    lam = [0.0] * (n + 1)
    for p in primes_upto(n):
        q = p
        while q <= n:
            lam[q] = math.log(p)
            q *= p
    psi = [0.0] * (n + 1)
    acc = 0.0
    for k in range(1, n + 1):
        acc += lam[k]
        psi[k] = acc
    return psi


# 1. Lemma CM (i), below 1500: max over real 1 <= x < 1500 of (psi(x) - psi(x/2))/x.
#    On [n, n+1) both psi(x) and psi(x/2) = psi(floor(n/2)) are constant, so the sup is attained at x = n.
psi = psi_table(1500)
best, arg = -1.0, None
for n in range(1, 1500):
    v = (psi[n] - psi[n // 2]) / n
    if v > best:
        best, arg = v, n
tail = 0.71 * 1500 - (1500 * math.log(2) + 3 * math.log(1500) + 3)
print("1  CM(i), N, 1<=x<1500: max (psi(x)-psi(x/2))/x = %.6f at x = %d (paper: 0.6803 <= 0.71); "
      "x>=1500: 0.71x - (x log2 + 3log x + 3) >= %.3f at x=1500, increasing; err < 1e-12" % (best, arg, tail))

# 2. Lemma CM (ii): S(x) - log x on 1 <= x <= 10^7, S(x) = sum_{p^k <= x} log p / p^k.
#    S is a right-continuous step function with jumps at prime powers q. Between consecutive jumps S is constant and
#    -log x decreases, so: the sup is attained at x = 1 or at a jump point q (value S(q) - log q); the inf over
#    [q_prev, q) is the limit S(q_prev) - log q (not attained), and on [q_last, 10^7] it is S(q_last) - log 10^7.
X = 10 ** 7
pp = []
for p in primes_upto(X):
    q = p
    lp = math.log(p)
    while q <= X:
        pp.append((q, lp / q))
        q *= p
pp.sort()
S = 0.0
smax, smax_at = 0.0, 1          # x = 1: S = 0, log 1 = 0
smin, smin_at = 0.0, 1
for q, t in pp:
    lq = math.log(q)
    if S - lq < smin:           # limit from the left at q
        smin, smin_at = S - lq, q
    S += t
    if S - lq > smax:
        smax, smax_at = S - lq, q
if S - math.log(X) < smin:
    smin, smin_at = S - math.log(X), X
print("2  CM(ii), N, 1<=x<=1e7: S(x)-log x in [%.6f, %.6f]; inf approached as x -> %d-, sup at x = %d "
      "(paper: [-0.753, 0]); %d prime powers; err < 1e-8" % (smin, smax, smin_at, smax_at, len(pp)))

# 3. Lemma V, small heights: sup over real Y of sum_{Y < n <= 2Y} 1/n.
#    For Y in [k/2, (k+1)/2) the set {n : Y < n <= 2Y} is exactly {ceil((k+1)/2), ..., k}, so the sup over that
#    interval is attained (the set is constant).
K = 2 * 10 ** 4
H = [0.0] * (K + 1)
acc = 0.0
for n in range(1, K + 1):
    acc += 1.0 / n
    H[n] = acc
best, arg = -1.0, None
for k in range(144, K):         # 72 <= Y < 10^4
    v = H[k] - H[(k + 2) // 2 - 1]   # n runs over ceil((k+1)/2) = (k+2)//2, ..., k
    if v > best:
        best, arg = v, k
print("3a Lemma V, N, 72<=Y<1e4: max sum_{Y<n<=2Y} 1/n = %.6f for Y in [%.1f, %.1f) (paper: 0.69658 <= C0 = 0.70); "
      "Y>=1e4: log2 + 1e-4 = %.6f (paper: 0.6933); err < 1e-11" % (best, arg / 2, (arg + 1) / 2, math.log(2) + 1e-4))
bestq, argq = Fraction(-1), None
for k in range(2, 144):         # 1 <= Y < 72, exact
    v = sum(Fraction(1, n) for n in range((k + 2) // 2, k + 1))
    if v > bestq:
        bestq, argq = v, k
print("3b Lemma V, N, 1<=Y<72: max sum_{Y<n<=2Y} 1/n = %s = %.6f for Y in [%.1f, %.1f), exact "
      "(paper: 0.8334)" % (bestq, float(bestq), argq / 2, (argq + 1) / 2))

# 4. F_{1/2} on N: max over real 1 <= y <= 10^6 of y^{-1/2} sum_{n <= y} mu^2(n) n^{-1/2}.
#    On [n, n+1) the sum is constant and y^{-1/2} decreases, so the sup is attained at an integer.
Y = 10 ** 6
sqf = bytearray([1]) * (Y + 1)
sqf[0] = 0
for p in primes_upto(int(Y ** 0.5) + 1):
    sqf[p * p :: p * p] = bytearray(len(range(p * p, Y + 1, p * p)))
acc = 0.0
best, arg = -1.0, None
for n in range(1, Y + 1):
    if sqf[n]:
        acc += n ** -0.5
    v = acc / math.sqrt(n)
    if v > best:
        best, arg = v, n
print("4  F_{1/2}, N, 1<=y<=1e6: max y^{-1/2} sum_{n<=y} mu^2(n) n^{-1/2} = %.6f at y = %d "
      "(paper: 1.3296 <= 1.33); err < 1e-9" % (best, arg))

# 5. Lemma 3.12 (threshold mass), small primes: max over primes p < 400 of prod_{q<p}(1-1/q)^{-1} - 1.8 log p.
#    The products are exact rationals.
prod = Fraction(1)
best, arg = None, None
for p in primes_upto(400):
    v = float(prod) - 1.8 * math.log(p)
    if best is None or v > best:
        best, arg = v, p
    prod *= Fraction(p, p - 1)
print("5  Lemma threshold-mass, primes p<400: max prod_{q<p}(1-1/q)^{-1} - 1.8 log p = %.6f at p = %d "
      "(paper: <= 0.25)" % (best, arg))

# 6. Lemma CM (iii): sum over primes p of log p/(p(p-1)) <= 0.75537.
#    Partial sum over p <= 10^7, plus the tail bound sum_{n>N} log n/(n(n-1)) <= (log N + 1)/(N - 1) + 1/(N-1)^2.
part = math.fsum(math.log(p) / (p * (p - 1)) for p in primes_upto(X))
tailb = (math.log(X) + 1) / (X - 1) + 1 / (X - 1) ** 2
print("6  CM(iii), rational primes: sum log p/(p(p-1)) <= %.7f + %.2e = %.7f (paper: 0.75537); err < 1e-12"
      % (part, tailb, part + tailb))

print("runtime %.1f s" % (time.time() - T0))
