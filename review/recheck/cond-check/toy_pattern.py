"""Pattern-level toy (Thm R analogue, k = 2, E_P = I): the TRUE expectation summed over all free-prime
structures, against
  (a) the claimed per-pattern bound            theta^2 delta^2 A_top^2,
  (b) the #48 scheme at its sharpest, per pattern (label at u_t, exact block sums over all contents),
  (c) the per-type PIL envelopes summed over the feasible types (each = theta^2 delta^2 A_top^2).
Toy world of toy_exact.py: J-slots (jittered pivots, H = 2) at even positions 4..16, R-slots (free primes,
rigid values) at odd positions 3..15, every slot decided, G = 1, per-row windows J_1, J_2 of length 1.
"""
from fractions import Fraction as Fr
from itertools import combinations_with_replacement
import sys

H = Fr(2)
Jpos = [Fr(p) for p in range(4, 17, 2)]
Rval = [Fr(v) for v in range(3, 16, 2)]
theta = Fr(1, 2)


def overlap(a, b, c, d):
    lo, hi = max(a, c), min(b, d)
    return hi - lo if hi > lo else Fr(0)


def multisets(vals, cap):
    """all products (as sorted tuples) of values from vals with product <= cap"""
    out = [()]
    def rec(start, cur, prod):
        for i in range(start, len(vals)):
            p = prod * vals[i]
            if p > cap:
                break
            t = cur + (vals[i],)
            out.append(t)
            rec(i, t, p)
    rec(0, (), Fr(1))
    return out


def prod(t):
    r = Fr(1)
    for x in t:
        r *= x
    return r


def true_E(J1, J2):
    E = Fr(0)
    types = set()
    for i1, p1 in enumerate(Jpos):
        for p2 in Jpos[:i1]:
            # c1: R-values < p1 ; c2: R-values < p2 ; (decision order = position order)
            R1 = [v for v in Rval if v < p1]
            R2 = [v for v in Rval if v < p2]
            for c1 in multisets(R1, J1[1] / (p1 - H / 2)):
                a = overlap(p1 - H / 2, p1 + H / 2, J1[0] / prod(c1), J1[1] / prod(c1)) / H
                if a == 0:
                    continue
                for c2 in multisets(R2, J2[1] / (p2 - H / 2)):
                    b = overlap(p2 - H / 2, p2 + H / 2, J2[0] / prod(c2), J2[1] / prod(c2)) / H
                    if b == 0:
                        continue
                    E += a * b
                    # type = decision-ordered column structure (pivots + distinct free primes with row exponents)
                    cols = {}
                    for v in c1:
                        cols.setdefault(v, [0, 0])[0] += 1
                    for v in c2:
                        cols.setdefault(v, [0, 0])[1] += 1
                    seq = sorted([(p1, 'P0'), (p2, 'P1')] + [(v, tuple(e)) for v, e in cols.items()], reverse=True)
                    types.add(tuple(x[1] for x in seq))
    return E, types


def sharp48(primes, Erat=1.0):
    """sum over run structures (2) and (1,1) of Final, discrete recursion of pattern_sum.py"""
    n = len(primes)
    sig = []
    E = Erat
    for g in primes:
        sig.append(E)
        E = E / (1 - 1.0 / g)
    Atop = E
    tot = 0.0
    for comp in [(2,), (1, 1)]:
        k = 2
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
        f = Erat ** jT * G[0]
        for i in range(n):
            x = 1 - 1.0 / primes[i]
            f += (x ** (-k) - 1) * x ** Kp * sig[i] ** jT * G[i + 1]
        tot += f
    return tot, Atop


def main():
    primes = [float(v) for v in Rval]
    S48, Atop = sharp48(primes)
    print(f"A_top (sup of Eu over R-primes) = {Atop:.4f}, theta = {theta}")
    print(f"{'J1':>10} {'J2':>8} {'true E (all types)':>19} {'claim th^2 d^2 A^2':>19} "
          f"{'#48 sharp/pattern':>18} {'#feasible types':>16} {'sum per-type env':>17}")
    claim = float(theta) ** 2 * Atop ** 2
    for z1, z2 in [(185, 12), (66, 21), (120, 30), (300, 45), (500, 60), (850, 21)]:
        J1, J2 = (Fr(z1), Fr(z1 + 1)), (Fr(z2), Fr(z2 + 1))
        E, types = true_E(J1, J2)
        env48 = float(theta) ** 2 * S48
        print(f"{str((z1, z1 + 1)):>10} {str((z2, z2 + 1)):>8} {float(E):19.5f} {claim:19.5f} "
              f"{env48:18.5f} {len(types):16d} {len(types) * claim:17.3f}")


if __name__ == "__main__":
    main()
