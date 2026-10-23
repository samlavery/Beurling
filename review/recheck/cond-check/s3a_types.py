"""(S3)(a): per-type bound versus the sum over block types.

Model of one late block F_t: realised primes g_1<g_2<... (one per slot, slots >= a),
Eu_s(a) = E0, Eu_s(u(g)) = Eu_s(sigma(g)) / (1-1/g).  chi == 1 (s_max beyond all primes).
A_top := Eu_s(u(g_last)), the sharpest constant (S3)(d) could supply.
K = j + m chain rows: j joining, m passing.  Passing rows carry 1/Eu_s(u_t), u_t = slot after f_t.

Per type: the columns of F_t, latest first, carry fixed row labels (owner of each column).
  LHS_type = sum over decreasing sequences of distinct primes on the columns of
             prod 1/g * prod_passing 1/Eu_s(u(g_latest)).
  RHS      = prod_passing 1/Eu_s(a) * prod_joining A_top/Eu_s(a)        (S3)(a).
Sum over all types (all label sequences, all lengths) = variable-content block sum.
"""
from fractions import Fraction as Fr
from itertools import product
import sys


def eu_prefix(primes, E0):
    """Eu_s(sigma(g_i)) for each i (product over primes before g_i), and Eu_s(u(g_i))."""
    sig, u = [], []
    E = E0
    for g in primes:
        sig.append(E)
        E = E / (1 - Fr(1, g)) if isinstance(E, Fr) else E / (1 - 1.0 / g)
        u.append(E)
    return sig, u


def lhs_type(primes, E0, labels, passing):
    """Exact per-type LHS by DP. labels: owner row of each column, latest first.
    Rows in `passing` carry 1/Eu_s(u_t)."""
    n = len(primes)
    sig, u = eu_prefix(primes, E0)
    r = len(labels)
    one = Fr(1) if isinstance(E0, Fr) else 1.0
    # W[c][i] = sum over assignments of columns c..r-1 (earlier columns) to primes with index < i
    # of prod 1/g ; column c gets prime index i'<i.
    W = [[one] * (n + 1) for _ in range(r + 1)]
    for c in range(r - 1, 0, -1):
        acc = [0 * one] * (n + 1)
        run = 0 * one
        for i in range(n + 1):
            acc[i] = run
            if i < n:
                run = run + W[c + 1][i] / primes[i]
        W[c] = acc
    tot = 0 * one
    for i in range(n):  # latest column f_t = primes[i]
        term = W[1][i] / primes[i] if r > 1 else one / primes[i]
        term = term / (u[i] ** len(passing))
        tot += term
    return tot


def rhs(primes, E0, j, m):
    sig, u = eu_prefix(primes, E0)
    Atop = u[-1]
    return (Atop ** j) / (E0 ** (j + m))


def all_types_sum(primes, E0, j, m):
    """Sum over all types: every nonempty set S, each element labelled by one of K rows
    (single occurrence, weight 1/g).  Closed form."""
    K = j + m
    sig, u = eu_prefix(primes, E0)
    one = Fr(1) if isinstance(E0, Fr) else 1.0
    tot = 0 * one
    P = one
    for i, g in enumerate(primes):
        tot += P * Fr(K, g) / (u[i] ** m) if isinstance(E0, Fr) else P * K / g / (u[i] ** m)
        P = P * (1 + (Fr(K, g) if isinstance(E0, Fr) else K / g))
    return tot


def all_types_sum_sharp(primes, E0, j, m):
    """Variable contents with full exponent vectors and weight g^{-a_g}: per prime
    sum_{e != 0} prod_y g^{-e_y} = (1-1/g)^{-K} - 1."""
    K = j + m
    sig, u = eu_prefix(primes, E0)
    tot = 0.0
    for i, g in enumerate(primes):
        x = 1 - 1.0 / g
        tot += (x ** (-K) - 1) * (sig[i] / E0) ** K / (u[i] ** m)
    return tot


def primes_in(lo, hi):
    s = bytearray([1]) * (hi + 1)
    s[0:2] = b"\x00\x00"
    for p in range(2, int(hi ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(s[p * p::p]))
    return [p for p in range(lo, hi + 1) if s[p]]


def main():
    # 1. exact per-type check (sanity: the paper's (S3)(a) per type), small sets
    viol = 0
    worst = 0.0
    ntest = 0
    for (lo, hi) in [(11, 60), (5, 40), (101, 200)]:
        primes = primes_in(lo, hi)
        E0 = Fr(3)
        for j, m in [(1, 0), (0, 1), (1, 1), (0, 2), (2, 1), (1, 2)]:
            K = j + m
            rows = list(range(K))
            passing = rows[j:]
            for r in range(1, 4):
                for labels in product(rows, repeat=r):
                    L = lhs_type(primes, E0, list(labels), passing)
                    R = rhs(primes, E0, j, m)
                    ntest += 1
                    worst = max(worst, float(L / R))
                    if L > R:
                        viol += 1
    print(f"per-type (S3)(a): {ntest} exact checks, {viol} violations, max LHS/RHS = {worst:.4f}")

    # 2. sum over types = variable-content block sum, versus the (S3)(a) right side
    print("\nsum over block types / (S3)(a) RHS   (realised primes = rational primes in [lo,hi], E0 = Eu_s(a))")
    print(f"{'range':>16} {'Atop/E0':>8} {'j':>2} {'m':>2} {'types(1/g)':>11} {'sharp g^-a':>11} {'model: (1+m/j)(1-rho^j) | m*sum1/p':>36}")
    for (lo, hi) in [(101, 10**3), (101, 10**4), (101, 10**5), (101, 10**6)]:
        primes = primes_in(lo, hi)
        E0 = 1.0
        sig, u = eu_prefix(primes, E0)
        s1p = sum(1.0 / p for p in primes)
        for j, m in [(1, 1), (1, 2), (2, 2), (1, 4), (0, 1), (0, 2)]:
            R = rhs(primes, E0, j, m)
            T = all_types_sum(primes, E0, j, m)
            S = all_types_sum_sharp(primes, E0, j, m)
            pred = (1 + m / j) * (1 - (E0 / u[-1]) ** j) if j else m * s1p
            print(f"{f'[{lo},{hi}]':>16} {u[-1]/E0:8.3f} {j:2d} {m:2d} {T/R:11.4f} {S/R:11.4f} {pred:36.4f}")


if __name__ == "__main__":
    main()
