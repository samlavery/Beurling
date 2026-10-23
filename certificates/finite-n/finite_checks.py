# Finite computations on the integers N quoted in Section 5 of the paper (noise section).
# Needs python-flint 0.9.0 (Arb ball arithmetic). Run:  python3 -I -B finite_checks.py
#
# Each check prints one line: the quantity, the value found (an Arb ball, or an exact rational), where it is attained,
# and the bound the paper uses, followed by the result of the comparison with that bound.
# Real-variable suprema are reduced to finitely many points by the step structure stated in each check.
# Rigour: every quantity is either an exact rational (Fraction) or an Arb ball that contains the true value; no
# floating-point number enters a computed quantity. Every comparison with a bound of the paper is decided on the ball
# (True means the whole ball satisfies it). The maxima are taken over the ball upper bounds, so the printed maximum
# ball contains the true maximum.
import time
from fractions import Fraction
from flint import arb, ctx

ctx.prec = 96
T0 = time.time()


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p :: p] = bytearray(len(range(p * p, n + 1, p)))
    return [i for i in range(n + 1) if s[i]]


def argmax(items):
    """items: iterable of (ball, where); returns the pair whose ball has the largest upper bound."""
    best = None
    for v, w in items:
        if best is None or v.upper() > best[0].upper():
            best = (v, w)
    return best


def dec(b):
    """Result of a comparison decided on the ball (b is the outcome of an arb comparison)."""
    return "True" if b else "False"


# 1. Lemma CM (i), below 1500: max over real 1 <= x < 1500 of (psi(x) - psi(x/2))/x.
#    On [n, n+1) both psi(x) and psi(x/2) = psi(floor(n/2)) are constant (psi jumps only at integers), so the sup over
#    that interval is attained at x = n.
lam = [arb(0)] * 1501
for p in primes_upto(1500):
    q = p
    while q <= 1500:
        lam[q] = arb(p).log()
        q *= p
psi = [arb(0)] * 1501
for k in range(1, 1501):
    psi[k] = psi[k - 1] + lam[k]
v1, x1 = argmax(((psi[n] - psi[n // 2]) / n, n) for n in range(1, 1500))
x = arb(1500)
tail = arb("0.71") * x - (x * arb(2).log() + 3 * x.log() + 3)
slope = arb("0.71") - arb(2).log() - arb(3) / 1500       # derivative 0.71 - log 2 - 3/x, increasing in x
print("1  CM(i), N, 1<=x<1500: max (psi(x)-psi(x/2))/x = %s at x = %d (paper: 0.6803 <= 0.71): %s; "
      "x>=1500: 0.71x - (x log2 + 3log x + 3) = %s at x=1500, derivative >= %s for x>=1500: %s"
      % (v1.str(8), x1, dec(v1 <= arb("0.6803")), tail.str(6), slope.str(4), dec(tail > 0 and slope > 0)))

# 2. Lemma CM (ii): S(x) - log x on 1 <= x <= 10^7, S(x) = sum_{p^k <= x} log p / p^k.
#    S is a right-continuous step function with jumps at prime powers q. Between consecutive jumps S is constant and
#    -log x decreases, so: the sup is attained at x = 1 or at a jump point q (value S(q) - log q); the inf over
#    [q_prev, q) is the limit S(q_prev) - log q (not attained), and on [q_last, 10^7] it is S(q_last) - log 10^7.
X = 10 ** 7
pp = []
for p in primes_upto(X):
    q = p
    while q <= X:
        pp.append((q, p))
        q *= p
pp.sort()
S = arb(0)
smax, smax_at = arb(0), 1          # x = 1: S = 0, log 1 = 0
smin, smin_at = arb(0), 1
for q, p in pp:
    lq = arb(q).log()
    c = S - lq                      # limit from the left at q
    if c.lower() < smin.lower():
        smin, smin_at = c, q
    S += arb(p).log() / q
    c = S - lq                      # value at q
    if c.upper() > smax.upper():
        smax, smax_at = c, q
c = S - arb(X).log()
if c.lower() < smin.lower():
    smin, smin_at = c, X
print("2  CM(ii), N, 1<=x<=1e7: S(x)-log x in [%s, %s]; inf approached as x -> %d-, sup at x = %d "
      "(paper: [-0.753, 0]): %s; %d prime powers"
      % (smin.str(8), smax.str(8), smin_at, smax_at, dec(smin >= arb("-0.753") and smax <= 0), len(pp)))

# 3. Lemma V, small heights: sup over real Y of sum_{Y < n <= 2Y} 1/n.
#    For Y in [k/2, (k+1)/2) the set {n : Y < n <= 2Y} is exactly {floor(k/2)+1, ..., k}, so the sup over that
#    interval is attained (the set is constant).
K = 2 * 10 ** 4
H = [arb(0)] * (K + 1)
for n in range(1, K + 1):
    H[n] = H[n - 1] + arb(1) / n
v3, k3 = argmax((H[k] - H[k // 2], k) for k in range(144, K))     # 72 <= Y < 10^4
big = arb(2).log() + arb("1e-4")                                    # Y >= 10^4: log 2 + 1/ceil(Y)
print("3a Lemma V, N, 72<=Y<1e4: max sum_{Y<n<=2Y} 1/n = %s for Y in [%.1f, %.1f) (paper: 0.69659 <= C0 = 0.70): %s; "
      "Y>=1e4: log2 + 1e-4 = %s (paper: 0.6933): %s"
      % (v3.str(8), k3 / 2, (k3 + 1) / 2, dec(v3 <= arb("0.69659") and v3 <= arb("0.70")), big.str(8),
         dec(big <= arb("0.6933"))))
Hq = [Fraction(0)]
for n in range(1, 144):
    Hq.append(Hq[-1] + Fraction(1, n))
bestq, argq = max((Hq[k] - Hq[k // 2], k) for k in range(2, 144))   # 1 <= Y < 72, exact
print("3b Lemma V, N, 1<=Y<72: max sum_{Y<n<=2Y} 1/n = %s for Y in [%.1f, %.1f), exact (paper: 0.8334): %s"
      % (bestq, argq / 2, (argq + 1) / 2, bestq <= Fraction(8334, 10000)))

# 4. F_{1/2} on N: max over real 1 <= y <= 10^6 of y^{-1/2} sum_{n <= y} mu^2(n) n^{-1/2}.
#    On [n, n+1) the sum is constant and y^{-1/2} decreases, so the sup is attained at an integer.
Y = 10 ** 6
sqf = bytearray([1]) * (Y + 1)
sqf[0] = 0
for p in primes_upto(int(Y ** 0.5) + 1):
    sqf[p * p :: p * p] = bytearray(len(range(p * p, Y + 1, p * p)))
acc = arb(0)
best = None
for n in range(1, Y + 1):
    r = arb(n).rsqrt()
    if sqf[n]:
        acc += r
    v = acc * r
    if best is None or v.upper() > best[0].upper():
        best = (v, n)
v4, y4 = best
print("4  F_{1/2}, N, 1<=y<=1e6: max y^{-1/2} sum_{n<=y} mu^2(n) n^{-1/2} = %s at y = %d (paper: 1.32964 <= 1.33): %s"
      % (v4.str(8), y4, dec(v4 <= arb("1.32964"))))

# 5. Lemma 3.12 (threshold mass), small primes: max over primes p < 400 of prod_{q<p}(1-1/q)^{-1} - 1.8 log p.
#    The products are exact rationals; only log p is a ball.
prod = Fraction(1)
items = []
for p in primes_upto(400):
    items.append((arb(prod.numerator) / prod.denominator - arb("1.8") * arb(p).log(), p))
    prod *= Fraction(p, p - 1)
v5, p5 = argmax(items)
print("5  Lemma threshold-mass, primes p<400: max prod_{q<p}(1-1/q)^{-1} - 1.8 log p = %s at p = %d (paper: <= 0.25): %s"
      % (v5.str(8), p5, dec(v5 <= arb("0.25"))))

# 6. Lemma CM (iii): sum over primes p of log p/(p(p-1)) <= 0.75537.
#    Partial sum over p <= N = 10^7, plus the tail over all n > N: log t/(t(t-1)) <= log t/(t-1)^2 is decreasing for
#    t >= 3, so the tail is <= int_{N-1}^oo log(s+1)/s^2 ds <= (log N + 1)/(N - 1) + 1/(N-1)^2.
part = arb(0)
for p in primes_upto(X):
    part += arb(p).log() / (p * (p - 1))
tailb = (arb(X).log() + 1) / (X - 1) + arb(1) / (X - 1) ** 2
tot = part + tailb
print("6  CM(iii), rational primes: sum log p/(p(p-1)) <= %s + %s = %s (paper: 0.75537): %s"
      % (part.str(8), tailb.str(3), tot.str(8), dec(tot <= arb("0.75537"))))

print("runtime %.1f s" % (time.time() - T0))
