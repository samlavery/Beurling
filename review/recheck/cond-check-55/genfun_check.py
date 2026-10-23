"""Independent check of eq:A-HK's generating function: P(E,z) = (1-Ez)/(1-T(z e^{-Ez})) has z^K-coefficient H_K(E)
(polynomials in E, exact rationals), and F_k(rho) = H_k(rho) + sum_j rho^j H_{k-j}(rho) = [z^k] 1/(1-T(z e^{-rho z}))."""
from fractions import Fraction as Fr
from math import factorial
N = 11
# polynomials in E: dict deg -> Fr ; series in z: list of polys
def padd(a, b):
    c = dict(a)
    for d, v in b.items(): c[d] = c.get(d, Fr(0)) + v
    return {d: v for d, v in c.items() if v != 0}
def pmul(a, b):
    c = {}
    for d1, v1 in a.items():
        for d2, v2 in b.items():
            c[d1 + d2] = c.get(d1 + d2, Fr(0)) + v1 * v2
    return {d: v for d, v in c.items() if v != 0}
def smul(A, B):
    C = [{} for _ in range(N + 1)]
    for i in range(N + 1):
        if not A[i]: continue
        for j in range(N + 1 - i):
            if B[j]: C[i + j] = padd(C[i + j], pmul(A[i], B[j]))
    return C
# w = z e^{-Ez} = sum_m (-E)^m z^{m+1}/m!
w = [{} for _ in range(N + 1)]
for m in range(N):
    w[m + 1] = {m: Fr((-1) ** m, factorial(m))}
# T(w) = sum_n n^{n-1} w^n / n!
T = [{} for _ in range(N + 1)]
wp = [{0: Fr(1)}] + [{} for _ in range(N)]
for n in range(1, N + 1):
    wp = smul(wp, w)
    coef = Fr(n ** (n - 1), factorial(n))
    for i in range(N + 1):
        if wp[i]: T[i] = padd(T[i], {d: v * coef for d, v in wp[i].items()})
# 1/(1-T) = sum T^n
inv = [{0: Fr(1)}] + [{} for _ in range(N)]
Tp = [{0: Fr(1)}] + [{} for _ in range(N)]
for n in range(1, N + 1):
    Tp = smul(Tp, T)
    for i in range(N + 1):
        if Tp[i]: inv[i] = padd(inv[i], Tp[i])
# P = (1 - E z) * inv
P = [dict(p) for p in inv]
for i in range(N):
    if inv[i]: P[i + 1] = padd(P[i + 1], pmul({1: Fr(-1)}, inv[i]))
# H_K from the integral recursion
def integ_from(poly):
    out = {0: Fr(0)}
    for d, c in poly.items():
        out[0] += c / (d + 1); out[d + 1] = out.get(d + 1, Fr(0)) - c / (d + 1)
    return {d: v for d, v in out.items() if v != 0}
H = [{0: Fr(1)}]
for K in range(1, N + 1):
    acc = {}
    for j in range(1, K + 1):
        acc = padd(acc, {d: K * v for d, v in integ_from({d + j - 1: c for d, c in H[K - j].items()}).items()})
    H.append(acc)
ok = all(P[K] == H[K] for K in range(N + 1))
print(f"[z^K](1-Ez)/(1-T(z e^(-Ez))) == H_K(E) for K <= {N}: {ok}")
# F_k(rho) identity: 1/(1-T(z e^{-rho z})) = inv ; F_k = H_k + sum_j rho^j H_{k-j}
def peval(p, x): return sum(v * x ** d for d, v in p.items())
ok2 = True
for rho in (Fr(0), Fr(1, 3), Fr(1, 2), Fr(1)):
    for k in range(1, N + 1):
        Fk = peval(H[k], rho) + sum(rho ** j * peval(H[k - j], rho) for j in range(1, k + 1))
        if Fk != peval(inv[k], rho): ok2 = False
print(f"F_k(rho) == [z^k] 1/(1-T(z e^(-rho z))) for k <= {N}, rho in {{0,1/3,1/2,1}}: {ok2}")
print("H_k(0) == k^k/k!:", all(peval(H[k], 0) == Fr(k ** k, factorial(k)) for k in range(N + 1)))
print("F_k(1) == 1:", all(peval(H[k], 1) + sum(peval(H[k - j], 1) for j in range(1, k + 1)) == 1 for k in range(1, N + 1)))
