"""Exact toy model of the Pivot-Integration Lemma (per type) and of the pattern-level sum.

Process.  Slots at integer positions s0, s0+1, ..., processed in order.  Two kinds of slot:
  J-slot: if decided, its prime has value q = s + H(U - 1/2), U uniform on [0,1) (continuous), independent of the past;
  R-slot: if decided, its prime has the deterministic value s.
Decisions are adaptive: P(decide at slot) depends on the history (past decisions and the half-bits
b = 1(U >= 1/2) of past J-primes).  The good event G_{<s} also depends on past decisions and half-bits.
Pivots are J-primes, free columns are R-primes (so (F2) holds at every pivot slot; free primes are summed
pathwise, as in the PIL).  Given the history (decisions + half-bits) the U's are independent and uniform on
their halves, so E[X_tau 1(G)] is a finite sum of products of interval overlaps: exact in rationals.

Envelope (Lemma pil with (S3)): theta^k * delta^k * prod over chain rows (A_top per joining, 1 per passing),
theta = max_q sum_{J-slots} 1(q in W_s)/H  ((F1) in the toy),
A_top = sup over histories and slots u of Eu_s(u) 1(G_{<u}), Eu_s over the R-primes decided before u
(the realised primes that can be free columns), Eu_rat = 1 (no tails).
"""
from fractions import Fraction as Fr
from itertools import product, combinations
import sys

H = Fr(2)


def make_slots(s0, kinds):
    return [(Fr(s0 + i), k) for i, k in enumerate(kinds)]


def overlap(a, b, c, d):
    lo, hi = max(a, c), min(b, d)
    return hi - lo if hi > lo else Fr(0)


# ---------------- decision rules and good events ----------------
def rule_always(i, slots, hist):
    return Fr(1)


def rule_half(i, slots, hist):
    return Fr(1, 2)


def rule_Rhalf(i, slots, hist):
    return Fr(1) if slots[i][1] == 'J' else Fr(1, 2)


def rule_adv(i, slots, hist):
    # R-slots decided surely after a J-prime in its lower half, else with prob 1/3;
    # J-slots decided with prob 2/3 if the number of decided R-primes so far is even, else surely.
    pos, kind = slots[i]
    lastJ = [h for h in hist if h[1] == 'J' and h[2] == 1]
    nR = sum(1 for h in hist if h[1] == 'R' and h[2] == 1)
    if kind == 'R':
        return Fr(1) if (lastJ and lastJ[-1][3] == 0) else Fr(1, 3)
    return Fr(1)


def good_true(hist):
    return True


def good_halves(hist):
    # at most one J-prime in its upper half so far
    return sum(1 for h in hist if h[1] == 'J' and h[2] == 1 and h[3] == 1) <= 1


def histories(slots, rule):
    """yield (prob, hist), hist = list of (index, kind, decided, half)."""
    out = [(Fr(1), [])]
    for i, (pos, kind) in enumerate(slots):
        new = []
        for p, h in out:
            pd = rule(i, slots, h)
            if pd < 1:
                new.append((p * (1 - pd), h + [(i, kind, 0, None)]))
            if pd > 0:
                if kind == 'J':
                    new.append((p * pd / 2, h + [(i, kind, 1, 0)]))
                    new.append((p * pd / 2, h + [(i, kind, 1, 1)]))
                else:
                    new.append((p * pd, h + [(i, kind, 1, None)]))
        out = new
    return out


# ---------------- types ----------------
# A type (E_P = I, k rows): columns latest first, each ('P', row) or ('F', rows-with-exponents dict).
# The value of row i is q_i * prod of free columns with exponent in row i.
def config_sum(slots, hist, Jwin, cols, k):
    """sum over configurations of prod_i E[1(q_i c_i in J) | hist]  (hist fixes halves)."""
    decided = [h for h in hist if h[2] == 1]
    Jd = [h for h in decided if h[1] == 'J']
    Rd = [h for h in decided if h[1] == 'R']
    total = Fr(0)
    m = len(cols)

    def rec(ci, last_index, assign):
        nonlocal total
        if ci == m:
            # evaluate
            cof = [Fr(1)] * k
            piv = [None] * k
            for (kind, data), h in zip(cols, assign):
                if kind == 'P':
                    piv[data] = h
                else:
                    val = slots[h[0]][0]
                    for row, e in data.items():
                        cof[row] *= val ** e
            term = Fr(1)
            for i in range(k):
                h = piv[i]
                pos = slots[h[0]][0]
                lo = pos - H / 2 + (H / 2) * h[3]
                hi = lo + H / 2
                z0, z1 = Jwin[i]
                term *= overlap(lo, hi, z0 / cof[i], z1 / cof[i]) / (H / 2)
                if term == 0:
                    return
            total += term
            return
        kind, data = cols[ci]
        pool = Jd if kind == 'P' else Rd
        for h in pool:
            if last_index is None or h[0] < last_index:
                rec(ci + 1, h[0], assign + [h])

    rec(0, None, [])
    return total


def lhs(slots, rule, good, Jwin, cols, k):
    tot = Fr(0)
    for p, h in histories(slots, rule):
        if not good(h):
            continue
        tot += p * config_sum(slots, h, Jwin, cols, k)
    return tot


def theta_toy(slots):
    # max over q of #J-windows containing q, / H ; windows [s-H/2, s+H/2)
    pts = sorted(set([s - H / 2 for s, k in slots if k == 'J'] + [s + H / 2 for s, k in slots if k == 'J']))
    best = 0
    for a in pts:
        q = a + Fr(1, 1000)
        c = sum(1 for s, k in slots if k == 'J' and s - H / 2 <= q < s + H / 2)
        best = max(best, c)
    return Fr(best) / H


def A_top(slots, rule, good):
    best = Fr(1)
    for p, h in histories(slots, rule):
        E = Fr(1)
        for idx in range(len(slots) + 1):
            # Eu_s(u) for u = slot idx; requires G_{<u}
            if not good(h[:idx]):
                break
            best = max(best, E)
            if idx < len(slots) and h[idx][1] == 'R' and h[idx][2] == 1:
                v = slots[idx][0]
                E = E / (1 - 1 / v)
    return best


def main():
    kinds = ['R', 'J'] * 7
    slots = make_slots(3, kinds)
    th = theta_toy(slots)
    rules = [('always', rule_always), ('R:p=1/2', rule_Rhalf), ('adaptive', rule_adv)]
    goods = [('G=1', good_true), ('G=halves', good_halves)]
    types = [
        ('k1: n=q*f*g', [('P', 0), ('F', {0: 1}), ('F', {0: 1})], 1, [(Fr(150), Fr(151))]),
        ('k1: n=q*f^2', [('P', 0), ('F', {0: 2})], 1, [(Fr(250), Fr(251))]),
        ('k2a: n1=q1 f g, n2=q2 g (g shared)', [('P', 0), ('F', {0: 1}), ('P', 1), ('F', {0: 1, 1: 1})], 2,
         [(Fr(185), Fr(186)), (Fr(12), Fr(13))]),
        ('k2b: passing owner g>h: n1=q1 f g, n2=q2 h', [('P', 0), ('F', {0: 1}), ('P', 1), ('F', {0: 1}), ('F', {1: 1})], 2,
         [(Fr(850), Fr(851)), (Fr(21), Fr(22))]),
        ('k2c: single run n1=q1 g, n2=q2 h', [('P', 0), ('P', 1), ('F', {0: 1}), ('F', {1: 1})], 2,
         [(Fr(66), Fr(67)), (Fr(21), Fr(22))]),
        ('k2d: n1=q1 f f2 g, n2=q2 g', [('P', 0), ('F', {0: 1}), ('F', {0: 1}), ('P', 1), ('F', {0: 1, 1: 1})], 2,
         [(Fr(738), Fr(739)), (Fr(9), Fr(10))]),
    ]
    print(f"slots {[(int(s), k) for s, k in slots]}, H={H}, theta_toy={th}")
    nviol = 0
    ntest = 0
    for tname, cols, k, Jwins in types:
        delta = Jwins[0][1] - Jwins[0][0]
        for rname, rule in rules:
            for gname, good in goods:
                L = lhs(slots, rule, good, Jwins, cols, k)
                At = A_top(slots, rule, good)
                env = th ** k * delta ** k * At ** k
                ntest += 1
                nviol += L > env
                flag = 'OK' if L <= env else 'VIOLATION'
                print(f"  {tname:42s} {rname:9s} {gname:8s} E[X;G]={float(L):.4e}  "
                      f"env={float(env):.4e}  A_top={float(At):.3f} ratio={float(L/env):.4f} {flag}")
    print(f"{ntest} cases, {nviol} violations")


if __name__ == "__main__":
    main()
