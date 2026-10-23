"""Closed form of the run-structure sum H_K(E) (Theorem R repair) and the identity H_K(0) = K^K/K!."""
from fractions import Fraction as Fr
from math import factorial, comb
def integ_from(poly):
    out = {0: Fr(0)}
    for d, c in poly.items():
        out[0] += c / (d + 1); out[d + 1] = out.get(d + 1, Fr(0)) - c / (d + 1)
    return out
def S2(n, k):
    return sum((-1) ** (k - i) * comb(k, i) * i ** n for i in range(k + 1)) // factorial(k)
H = [{0: Fr(1)}]
for K in range(1, 11):
    acc = {}
    for j in range(1, K + 1):
        p = {d + j - 1: c for d, c in H[K - j].items()}
        for d, c in integ_from(p).items():
            acc[d] = acc.get(d, Fr(0)) + K * c
    H.append(acc)
ok = True
for K in range(1, 11):
    q = {}
    for d, c in H[K].items():
        for i in range(d + 1):
            q[i] = q.get(i, Fr(0)) + c * comb(d, i) * (-1) ** i
    for m in range(0, K + 1):
        want = Fr(K * S2(K - 1, K - m), factorial(m)) if m >= 1 else Fr(0)
        if q.get(m, Fr(0)) != want:
            ok = False
print("H_K(E) = K * sum_m S(K-1,K-m) (1-E)^m / m!  for K <= 10:", ok)
print("sum_{m=1}^K S(K-1,K-m)/m! == K^(K-1)/K!  for K <= 40:",
      all(sum(Fr(S2(K - 1, K - m), factorial(m)) for m in range(1, K + 1)) == Fr(K ** (K - 1), factorial(K))
          for K in range(1, 41)))
