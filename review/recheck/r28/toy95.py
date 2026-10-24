"""Toy check of eq:bookkeeping (slot windows, exact) and eq:edge (physical windows) for correction 94.

Slots j = 0..n-1 with starts s_j (non-decreasing; an empty continuous slot has s_j = s_{j+1} and is followed by a jump
slot). Jump slots carry one jump element at s_j; jittered composites (C_jit) are placed at random values in the cells.
Greedy rule: P_j = max(0, 1 - Q_{j-1} - A_j), Q_j = Q_{j-1} + A_j + P_j - 1, with Q_{-1} = 0.
"""
import random
from fractions import Fraction as Fr


def build(rng, n):
    kinds = []
    j = 0
    while j < n:
        r = rng.random()
        if r < 0.15 and j + 1 < n:
            kinds += ['empty', 'jump']
            j += 2
        elif r < 0.45:
            kinds.append('jump')
            j += 1
        else:
            kinds.append('cont')
            j += 1
    kinds = kinds[:n]
    if kinds[-1] == 'empty':
        kinds[-1] = 'cont'
    s = [Fr(0)]
    for j in range(n):
        if kinds[j] == 'empty':
            s.append(s[-1])
        else:
            s.append(s[-1] + Fr(rng.randint(1, 40), 10))
    # s has n+1 entries: s[0..n]; cell j = [s[j], s[j+1])
    jit = []
    for j in range(n):
        if s[j + 1] > s[j]:
            for _ in range(rng.choice([0, 0, 0, 1, 1, 2, 3])):
                jit.append(s[j] + (s[j + 1] - s[j]) * Fr(rng.randint(0, 999), 1000))
    A, P, Q = [], [], []
    q = 0
    for j in range(n):
        a = sum(1 for v in jit if s[j] <= v < s[j + 1]) + (1 if kinds[j] == 'jump' else 0)
        p = max(0, 1 - q - a)
        q = q + a + p - 1
        A.append(a)
        P.append(p)
        Q.append(q)
    return kinds, s, jit, A, P, Q


def check(seed):
    rng = random.Random(seed)
    n = 200
    kinds, s, jit, A, P, Q = build(rng, n)
    Qm = lambda i: 0 if i < 0 else Q[i]
    Am = lambda i: 0 if i < 0 else A[i]
    cjit = lambda lo, hi, lo_closed=True, hi_closed=False: sum(
        1 for v in jit if (v >= lo if lo_closed else v > lo) and (v <= hi if hi_closed else v < hi))
    # slot windows (k, j]
    for _ in range(300):
        k = rng.randint(-1, n - 2)
        j = rng.randint(k, n - 2)
        sig = sum(P[k + 1:j + 1])
        cont = sum(1 for i in range(k + 1, j + 1) if kinds[i] in ('cont', 'empty'))
        assert sig == cont - cjit(s[k + 1], s[j + 1]) + Qm(j) - Qm(k), (seed, k, j)
    # physical closed windows [a, b]
    hits = 0
    for _ in range(600):
        a = s[0] + (s[n - 1] - s[0]) * Fr(rng.randint(0, 10000), 10000)
        if rng.random() < 0.2:
            a = s[rng.randint(0, n - 2)]  # endpoints on slot starts, including empty slots
        b = a + Fr(rng.randint(0, 400), 10)
        if rng.random() < 0.2:
            b = s[rng.randint(0, n - 2)]
        if b < a or b >= s[n - 1]:
            continue
        inW = [i for i in range(n) if a <= s[i] <= b]
        before = [i for i in range(n) if s[i] < a]
        k = before[-1] if before else -1
        j = inW[-1] if inW else k
        assert inW == list(range(k + 1, j + 1)), (seed, a, b)
        sig = sum(P[i] for i in inW)
        cont = sum(1 for i in inW if kinds[i] in ('cont', 'empty'))
        cW = cjit(a, b, True, True)
        dQ = Qm(j) - Qm(k)
        E = sig - cont + cW - dQ
        lo, hi = s[k + 1], s[j + 1]  # W° = [lo, hi)
        if j == k:
            second = cW
        else:
            second = cjit(a, lo, True, False) - cjit(b, hi, False, False)
        assert E == second, (seed, a, b, E, second)
        assert -Am(j) <= E <= Am(k), (seed, a, b)
        assert abs(E) <= 1 + max(Qm(k), Qm(j))
        if E != 0:
            hits += 1
    return hits


tot = 0
for seed in range(40):
    tot += check(seed)
print('all checks passed; windows with nonzero E_edge:', tot)
