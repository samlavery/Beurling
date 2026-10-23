# Exact checks of the run-structure sum in Theorem R: H_K, F_k, compositions, generating function.
from flint import fmpq_poly, fmpq, fmpz
from itertools import product
import math

X = fmpq_poly([0,1])
ONE = fmpq_poly([1])

def integ_E_to_1(p):
    # returns polynomial Q(E) = int_E^1 p(x) dx
    P = p.integral()
    return fmpq_poly([P(fmpq(1))]) - P

def g_comp(comp):
    # g_t for a composition (j_1..j_T) with A=1, K_t cumulative
    g = ONE
    K = 0
    for j in comp:
        K += j
        g = integ_E_to_1(fmpq(K) * X**(j-1) * g) if j>=1 else None
    return g

def compositions(n):
    if n == 0:
        yield ()
        return
    for first in range(1, n+1):
        for rest in compositions(n-first):
            yield (first,)+rest

Kmax = 12
H = [ONE]
for K in range(1, Kmax+1):
    s = fmpq_poly([0])
    for j in range(1, K+1):
        s += integ_E_to_1(X**(j-1) * H[K-j])
    H.append(fmpq(K)*s)

ok = True
for K in range(1, Kmax+1):
    # sum over compositions of g_T equals H_K
    tot = fmpq_poly([0])
    for c in compositions(K):
        tot += g_comp(c)
    if tot != H[K]:
        ok = False; print("composition mismatch", K)
    # H_K(0) = K^K/K!
    v = H[K](fmpq(0))
    target = fmpq(K**K, math.factorial(K))
    if v != target:
        ok = False; print("H_K(0) mismatch", K, v, target)
print("H_K checks:", ok)

# F_k(rho) and its properties; also brute force Fin sum over run structures
for k in range(1, Kmax+1):
    F = H[k] + sum((X**j * H[k-j] for j in range(1, k+1)), fmpq_poly([0]))
    # brute force: sum over compositions of Fin = g_T(rho) + rho^{j_T} g_{T-1}(rho)
    tot = fmpq_poly([0])
    for c in compositions(k):
        gT = g_comp(c)
        gTm1 = g_comp(c[:-1]) if len(c) > 1 else ONE
        tot += gT + X**c[-1] * gTm1
    assert tot == F, k
    assert F(fmpq(0)) == fmpq(k**k, math.factorial(k))
    assert F(fmpq(1)) == 1, (k, F(fmpq(1)))
    # derivative <= 0 on [0,1]: check -F' has no sign change: sample + exact formula
    dF = F.derivative()
    mx = max(dF(fmpq(i, 400)) for i in range(401))
    assert mx <= 0, (k, mx)
    # H_K nonneg and non-increasing on [0,1]
    for K in range(k+1):
        assert min(H[K](fmpq(i,200)) for i in range(201)) >= 0
        if K>0: assert max(H[K].derivative()(fmpq(i,200)) for i in range(201)) <= 0
print("F_k: Fin-sum = F_k, F_k(0)=k^k/k!, F_k(1)=1, F_k' <= 0 sampled: ok up to", Kmax)

# Generating function: F_k(rho) = [z^k] 1/(1 - T(z e^{-rho z})), verify at several rationals rho
N = Kmax
def series_mul(a, b, N):
    c = [fmpq(0)]*(N+1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b[:N+1-i]):
            c[i+j] += ai*bj
    return c
for rho in [fmpq(i,13) for i in range(14)]:
    # w(z) = z e^{-rho z}
    expo = [(-rho)**n / math.factorial(n) for n in range(N+1)]
    w = [fmpq(0)] + expo[:N]
    # T(w) = sum n^{n-1} w^n / n!
    Tw = [fmpq(0)]*(N+1)
    wp = [fmpq(1)] + [fmpq(0)]*N
    for n in range(1, N+1):
        wp = series_mul(wp, w, N)
        coef = fmpq(n**(n-1), math.factorial(n))
        Tw = [Tw[i] + coef*wp[i] for i in range(N+1)]
    # 1/(1-Tw) = sum Tw^m
    inv = [fmpq(1)] + [fmpq(0)]*N
    p = [fmpq(1)] + [fmpq(0)]*N
    for m in range(1, N+1):
        p = series_mul(p, Tw, N)
        inv = [inv[i] + p[i] for i in range(N+1)]
    for k in range(1, N+1):
        F = H[k] + sum((X**j * H[k-j] for j in range(1, k+1)), fmpq_poly([0]))
        assert F(rho) == inv[k], (rho, k, F(rho), inv[k])
print("generating function identity F_k(rho) = [z^k] 1/(1-T(z e^{-rho z})) verified exactly for k<=%d at 14 points rho=i/13 (degree<=12 polys: identity holds identically)" % N)
print("sample F_k(rho):", [(k, float(H[k](fmpq(0)))) for k in (5,10,12)])
