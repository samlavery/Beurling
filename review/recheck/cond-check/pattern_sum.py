"""Thm R, pattern E_P = I (row i = q_i * c_i, pivots decided p_1 > ... > p_k), summed over all
free-prime structures, evaluated with the #48 scheme at its sharpest:
  label sum at the last pivot of each run replaced by u_t (slot after the latest block prime),
  then the exact block sum over ALL contents of the block (no type count),
  end step over the early block (empty or not) and the tails.
Compared with the per-pattern bound Thm R claims (before delta^k theta^k): A_top^k.

Recursion (derived in the report):  K_t = |P_{<=t}|, j_t = |P_t|,
  G_0 = 1,
  G_t(a) = sum_{f: slot >= a} [(1-1/f)^{-K_t} - 1] (1-1/f)^{K_{t-1}} Eu(sigma_f)^{j_t} G_{t-1}(u_f),
  Final  = Eu_rat^{j_T} G_{T-1}(X0) + sum_f [(1-1/f)^{-k} - 1](1-1/f)^{K_{T-1}} Eu(sigma_f)^{j_T} G_{T-1}(u_f).
Continuous model (Eu as the variable, A = 1, Eu_rat = rho):
  G_t(E) = int_E^1 K_t x^{j_t-1} G_{t-1}(x) dx,
  Final  = rho^{j_T} G_{T-1}(rho) + int_rho^1 k x^{j_T-1} G_{T-1}(x) dx.
"""
from fractions import Fraction as Fr
import sys


def compositions(k):
    if k == 0:
        yield ()
        return
    for first in range(1, k + 1):
        for rest in compositions(k - first):
            yield (first,) + rest


# ---------- continuous model: exact polynomial arithmetic ----------
def pint(poly, lo):
    """int_lo^1 poly(x) dx as a polynomial in lo (poly: dict deg->coef)."""
    out = {}
    const = Fr(0)
    for d, c in poly.items():
        const += c / (d + 1)
        out[d + 1] = out.get(d + 1, Fr(0)) - c / (d + 1)
    out[0] = out.get(0, Fr(0)) + const
    return out


def pmul_mono(poly, deg, coef):
    return {d + deg: c * coef for d, c in poly.items()}


def peval(poly, x):
    return sum(c * x ** d for d, c in poly.items())


def final_cont(comp, rho):
    k = sum(comp)
    G = {0: Fr(1)}
    K = 0
    for jt in comp[:-1]:
        K += jt
        G = pint(pmul_mono(G, jt - 1, Fr(K)), None)
    jT = comp[-1]
    integrand = pmul_mono(G, jT - 1, Fr(k))
    I = pint(integrand, None)
    return rho ** jT * peval(G, rho) + peval(I, rho)


# ---------- discrete model with realised primes ----------
def primes_in(lo, hi):
    s = bytearray([1]) * (hi + 1)
    s[0:2] = b"\x00\x00"
    for p in range(2, int(hi ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(s[p * p::p]))
    return [p for p in range(lo, hi + 1) if s[p]]


def final_disc(comp, primes, Erat):
    n = len(primes)
    sig = [0.0] * n
    E = Erat
    for i, g in enumerate(primes):
        sig[i] = E
        E = E / (1 - 1.0 / g)
    Atop = E
    k = sum(comp)
    # G as array over "a" = slot index 0..n (a = n means beyond all primes); G(a) for a <= i
    # G_{t-1}(u_f) with u_f = index i+1.
    G = [1.0] * (n + 1)
    K = 0
    for jt in comp[:-1]:
        Kp = K
        K += jt
        newG = [0.0] * (n + 1)
        acc = 0.0
        for i in range(n - 1, -1, -1):
            x = 1 - 1.0 / primes[i]
            acc += (x ** (-K) - 1) * x ** Kp * sig[i] ** jt * G[i + 1]
            newG[i] = acc
        G = newG
    jT = comp[-1]
    Kp = K
    tot = Erat ** jT * G[0]
    for i in range(n):
        x = 1 - 1.0 / primes[i]
        tot += (x ** (-k) - 1) * x ** Kp * sig[i] ** jT * G[i + 1]
    return tot, Atop


def main():
    print("continuous model: ratio_k(rho) = sum over run structures of Final / A_top^k")
    rhos = [Fr(0), Fr(1, 100), Fr(1, 10), Fr(3, 10), Fr(1, 2), Fr(9, 10)]
    print(f"{'k':>3} " + " ".join(f"{('rho='+str(r)):>12}" for r in rhos) + f" {'ratio_k/ratio_(k-1) at 0':>26}")
    prev = None
    for k in range(1, 13):
        vals = [sum(final_cont(c, r) for c in compositions(k)) for r in rhos]
        gr = float(vals[0] / prev) if prev else float('nan')
        prev = vals[0]
        print(f"{k:3d} " + " ".join(f"{float(v):12.4f}" for v in vals) + f" {gr:26.4f}")
    # worst single structure at rho = 0
    print("\nlargest single run structure at rho=0:")
    for k in range(2, 9):
        best = max(compositions(k), key=lambda c: final_cont(c, Fr(0)))
        print(f"  k={k}: {best}  Final/A^k = {float(final_cont(best, Fr(0))):.4f}")

    print("\ndiscrete model (realised primes = rational primes in [lo,hi], Eu_rat = E0 = 1):")
    for (lo, hi) in [(101, 10**4), (101, 10**5), (101, 10**6)]:
        primes = primes_in(lo, hi)
        for k in (2, 3, 4):
            tot = 0.0
            Atop = None
            for c in compositions(k):
                f, Atop = final_disc(c, primes, 1.0)
                tot += f
            rho = 1.0 / Atop
            cont = float(sum(final_cont(c, Fr(rho).limit_denominator(10**9)) for c in compositions(k)))
            print(f"  [{lo},{hi}] A_top/Eu_rat={Atop:.3f}  k={k}: discrete ratio {tot / Atop ** k:.4f}   continuous {cont:.4f}")


if __name__ == "__main__":
    main()
