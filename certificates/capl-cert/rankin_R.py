# Interval-arithmetic checks for Lemma 4.15(c) and (e) (rowweights), correction 49.
#  (1) R(sigma) := sum_p ( -log(1-p^-sigma) - p^-sigma ) over all primes, at sigma = 0.69 and 0.75:
#      exact sum over p <= 1e7 in arb, plus the tail bound sum_{n>N} n^{-2 sigma}/(2(1-n^{-sigma}))
#      <= N^{1-2 sigma}/((2 sigma-1) * 2 * (1-N^{-sigma})).   Paper: R(0.69) <= 0.77, R(0.75) <= 0.63.
#  (2) Ei(11) - e^11/11 - e^11/121 <= 134, and 2.75/x + 134 x^2 e^{-x} < 1 on [11, 411] (decreasing beyond),
#      which give Ei(x) <= (e^x/x)(1+2/x) for x >= 11.
#  (3) (3/2)^{3/4} <= 1.3555 and Ei(log(2)/4) >= -1.
# Run with python-flint 0.9.0:  python3 -I -B rankin_R.py   (about 3 s)
from flint import arb, ctx
ctx.prec = 100
N = 10**7
sieve = bytearray([1]) * (N + 1); sieve[0] = sieve[1] = 0
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
primes = [i for i in range(N + 1) if sieve[i]]
ok = True
for sig, claim in (("0.69", "0.77"), ("0.75", "0.63")):
    s = arb(sig); tot = arb(0)
    for p in primes:
        x = arb(p) ** (-s)
        tot += -(1 - x).log() - x
    tail = arb(N) ** (1 - 2 * s) / ((2 * s - 1) * 2 * (1 - arb(N) ** (-s)))
    good = (tot + tail) < arb(claim)
    ok &= bool(good)
    print(f"R({sig}) <= {(tot + tail).str(8)}  (claim <= {claim}): {'OK' if good else 'FAIL'}")
e11 = arb(11).exp()
c = arb(11).ei() - e11 / 11 - e11 / 121
good = c < 134; ok &= bool(good)
print(f"Ei(11) - e^11/11 - e^11/121 = {c.str(8)}  (claim <= 134): {'OK' if good else 'FAIL'}")
good = all((arb("2.75") / x + 134 * x ** 2 * (-x).exp()) < 1 for x in [arb(11) + arb(k) / 10 for k in range(4001)])
ok &= bool(good)
print(f"2.75/x + 134 x^2 e^-x < 1 on [11, 411]: {'OK' if good else 'FAIL'}")
v = (arb(3) / 2) ** (arb(3) / 4); good = v < arb("1.3555"); ok &= bool(good)
print(f"(3/2)^(3/4) = {v.str(10)}  (claim <= 1.3555): {'OK' if good else 'FAIL'}")
v = (arb(2).log() / 4).ei(); good = v > -1; ok &= bool(good)
print(f"Ei(log(2)/4) = {v.str(10)}  (claim >= -1): {'OK' if good else 'FAIL'}")
print("ALL OK" if ok else "SOME CHECK FAILED")
