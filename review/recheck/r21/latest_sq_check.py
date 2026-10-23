"""Small-scale check of the #83 counterexample mechanism.

For an integer window I = [N, N+W), compare
  A = #{p prime: p^2 <= W}                       (reporter: every such p has a multiple of p^2 in I)
  B = #{p prime: some n in I with P+(n) = p and p^2 | n}   (X^(2)_p(I) >= 1 with p latest, rational case)
Segmented sieve: factor every n in I by primes up to sqrt(N+W).
"""
import math
import sys


def primes_upto(m):
    s = bytearray([1]) * (m + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(m + 1) if s[i]]


def run(N, W):
    ps = primes_upto(int(math.isqrt(N + W)) + 1)
    rem = list(range(N, N + W))
    largest = [1] * W
    largest_exp = [0] * W
    for p in ps:
        start = (-N) % p
        for i in range(start, W, p):
            e = 0
            while rem[i] % p == 0:
                rem[i] //= p
                e += 1
            # primes are processed in increasing order, so the last one seen is the largest so far
            largest[i] = p
            largest_exp[i] = e
    hits = set()
    for i in range(W):
        if rem[i] > 1:
            # the leftover cofactor is a prime > sqrt(N+W), with exponent 1
            continue
        if largest_exp[i] >= 2:
            hits.add(largest[i])
    A = sum(1 for p in ps if p * p <= W)
    return A, len(hits), sorted(hits)[:20]


if __name__ == "__main__":
    for N, W in [(10**10, 10**5), (10**12, 2 * 10**5), (10**13, 2 * 10**5)]:
        A, B, ex = run(N, W)
        print(f"N={N:.0e} W={W:.0e}: #p with p^2<=W = {A}; #p latest with p^2|n in I = {B}; examples {ex}")
        sys.stdout.flush()
