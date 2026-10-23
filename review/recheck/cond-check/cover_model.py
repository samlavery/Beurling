"""Prop cover analogue of pattern_sum.py: chain rows = rows of C; rows of R join without a chain.
Model: E_P = I, pivots p_1 > ... > p_r in decision order, each pivot in its own row; `seq` gives the kind
(C or R) of each pivot's row, latest first.  A run structure is a composition of r.  At stage t:
K_t = #C rows joined so far, j_t = #C rows joining at t (may be 0: an R-only stage).
Continuous model in the Euler variable E in [rho, 1] (A_top = 1, Eu_rat = rho):
  G_t(E) = int_E^1 K_t x^{j_t - 1} G_{t-1}(x) dx,     G_0 = 1,
  Final  = rho^{j_T} G_{T-1}(rho) + int_rho^1 K_T x^{j_T - 1} G_{T-1}(x) dx,
the #48 scheme at its sharpest summed over all block contents; the per-type claim is A_top^kappa = 1.
Numerical quadrature on a log grid.
"""
import math
import sys
from itertools import product


def compositions(k):
    if k == 0:
        yield ()
        return
    for first in range(1, k + 1):
        for rest in compositions(k - first):
            yield (first,) + rest


def final(seq, comp, rho, N=4000):
    # grid in y = log E from log rho to 0
    y0 = math.log(rho)
    ys = [y0 * (1 - i / N) for i in range(N + 1)]  # increasing from y0 to 0
    xs = [math.exp(y) for y in ys]
    G = [1.0] * (N + 1)
    pos = 0
    K = 0
    blocks = []
    for size in comp:
        kinds = seq[pos:pos + size]
        pos += size
        j = sum(1 for c in kinds if c == 'C')
        blocks.append(j)
    T = len(comp)
    Ks = []
    for j in blocks:
        K += j
        Ks.append(K)
    for t in range(T - 1):
        Kt, jt = Ks[t], blocks[t]
        # integrand in y: K x^{j} G(x)  (since dx = x dy, x^{j-1} dx = x^j dy)
        f = [Kt * xs[i] ** jt * G[i] for i in range(N + 1)]
        newG = [0.0] * (N + 1)
        acc = 0.0
        for i in range(N - 1, -1, -1):
            acc += 0.5 * (f[i] + f[i + 1]) * (ys[i + 1] - ys[i])
            newG[i] = acc
        G = newG
    jT, KT = blocks[-1], Ks[-1]
    f = [KT * xs[i] ** jT * G[i] for i in range(N + 1)]
    integ = sum(0.5 * (f[i] + f[i + 1]) * (ys[i + 1] - ys[i]) for i in range(N))
    return rho ** jT * G[0] + integ


def main():
    print("Sum over run structures of Final (claim: 1 = A_top^kappa per type), E_P = I model")
    for rho in (1e-1, 1e-2, 1e-4, 1e-8):
        print(f"\nrho = Eu_rat/A_top = {rho:g}   (log(1/rho) = {math.log(1/rho):.2f})")
        for seq in ['C', 'CC', 'CR', 'CRR', 'CRRR', 'CCR', 'CRC', 'CCRR', 'CRCR', 'CCCR', 'CRRRR']:
            tot = sum(final(seq, c, rho) for c in compositions(len(seq)))
            worst = max(compositions(len(seq)), key=lambda c: final(seq, c, rho))
            print(f"  seq={seq:6s} kappa={seq.count('C')} |R|={seq.count('R')}: sum {tot:10.3f}   "
                  f"worst structure {worst} -> {final(seq, worst, rho):9.3f}")


if __name__ == "__main__":
    main()
