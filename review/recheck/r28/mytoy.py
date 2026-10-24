"""Independent toy (R28) for eq:bookkeeping, eq:edge, the ±2 granularity, and E_box.

Unlike toy95.py, T itself is modelled: a piecewise-linear continuous part with rational slopes plus unit jumps
(rigid / Abs elements). Slots are the hitting times s_j = min{x : T(x) >= j + th}; jump slots, continuous slots and
empty continuous slots (a jump starting exactly on a level) are derived from T, not drawn. Jittered non-absorbed
composites (C_jit) are placed at random values >= s_{j0}, some exactly at continuous-slot starts. Windows have random
closure types and endpoints snapped to slot starts, jump points and composite values. Everything is exact (Fractions).
"""
import random
import sys
from fractions import Fraction as Fr


class Interval:
    def __init__(self, a, b, lc, rc):
        self.a, self.b, self.lc, self.rc = a, b, lc, rc

    def __contains__(self, v):
        return (v >= self.a if self.lc else v > self.a) and (v <= self.b if self.rc else v < self.b)

    def before(self, v):  # v lies strictly to the left of every point of the interval
        return v < self.a or (v == self.a and not self.lc)

    def __repr__(self):
        return ('[' if self.lc else '(') + f'{self.a},{self.b}' + (']' if self.rc else ')')


def build(rng, n_jumps, th, cj_choices=(0, 0, 0, 1, 1, 2, 3, 4)):
    # continuous part C: slope on [i, i+1) is slopes[i] (rational), C(0) = 0; T(0) = 0 (the jump at "X_0" included)
    span = 4 * n_jumps + 50
    slopes = [Fr(rng.choice([1, 2, 3, 4, 5, 6]), 5) for _ in range(span + 5)]
    pref = [Fr(0)]
    for s in slopes:
        pref.append(pref[-1] + s)

    def C(x):
        i = int(x)  # floor for x >= 0
        return pref[i] + slopes[i] * (x - i)

    def Cinv(level):  # min x with C(x) >= level (C continuous, strictly increasing)
        lo = 0
        while pref[lo + 1] < level:
            lo += 1
        return lo + (level - pref[lo]) / slopes[lo]

    jumps = []
    x = Fr(0)
    nj = 0  # jumps so far (all at positions > 0)
    while len(jumps) < n_jumps:
        # next level above T(x) = C(x) + nj, reached by the continuous part at time h
        Tx = C(x) + nj
        lev = int(Tx - th) + 1 + th if Tx - th >= 0 else th
        if lev <= Tx:
            lev += 1
        h = Cinv(lev - nj)
        r = rng.random()
        if r < 0.25:
            d = h  # tie: a jump starts exactly on the level -> empty continuous slot
        elif r < 0.6:
            d = x + (h - x) * Fr(rng.randint(1, 99), 100)  # jump before the level is reached
        else:
            d = h + Fr(rng.randint(1, 300), 100)  # after it
        if d <= x:
            continue
        jumps.append(d)
        nj += 1
        x = d
    xmax = jumps[-1] + 3
    jset = sorted(jumps)

    def T(x):
        return (C(x) if x >= 0 else Fr(0)) + sum(1 for d in jset if d <= x)

    def Tminus(x):
        return (C(x) if x >= 0 else Fr(0)) + sum(1 for d in jset if d < x)

    # slots
    s = []
    j = 0
    while True:
        level = j + th
        # candidate: a jump point d with Tminus(d) < level <= T(d), or continuous hit between jumps
        best = None
        pts = [Fr(0)] + jset
        for idx, p in enumerate(pts):
            nxt = pts[idx + 1] if idx + 1 < len(pts) else None
            base = sum(1 for d in jset if d <= p)
            if T(p) >= level:
                best = p
                break
            # on [p, nxt): T = C + base
            hit = Cinv(level - base)
            if nxt is None or hit < nxt:
                best = hit
                break
        if best is None or best > xmax:
            break
        s.append(best)
        j += 1
    n = len(s) - 1  # slots 0..n-1 have cells [s_j, s_{j+1})
    s = s[:n + 1]
    kinds = []
    for i in range(n):
        if Tminus(s[i]) < i + th:
            kinds.append('jump')
        else:
            kinds.append('empty' if s[i] == s[i + 1] else 'cont')
    # sanity: jump slot iff a jump at s_i; each jump in exactly one jump slot; empty slots followed by jump slots
    for i in range(n):
        assert (kinds[i] == 'jump') == (s[i] in jset and s[i] < s[i + 1] and Tminus(s[i]) < i + th)
        if kinds[i] == 'empty':
            assert i + 1 < n and kinds[i + 1] == 'jump', (i, kinds[i:i + 2])
        if kinds[i] == 'cont':
            assert Tminus(s[i]) == i + th
    for d in jset:
        if s[0] <= d < s[n]:
            assert sum(1 for i in range(n) if kinds[i] == 'jump' and s[i] == d) == 1
    # C_jit composites: values >= s[0]; some exactly at nonempty continuous-slot starts
    cj = []
    for i in range(n):
        if s[i + 1] > s[i]:
            for _ in range(rng.choice(cj_choices)):
                if kinds[i] == 'cont' and rng.random() < 0.15:
                    cj.append(s[i])
                else:
                    v = s[i] + (s[i + 1] - s[i]) * Fr(rng.randint(1, 999), 1000)
                    if v not in jset:
                        cj.append(v)
    # greedy queue
    A, P, Q = [], [], []
    q = 0
    for i in range(n):
        a = sum(1 for v in cj if s[i] <= v < s[i + 1]) + (1 if kinds[i] == 'jump' else 0)
        p = max(0, 1 - q - a)
        q = q + a + p - 1
        assert q >= 0 and p in (0, 1) and a <= q + 1
        A.append(a)
        P.append(p)
        Q.append(q)
    return dict(C=C, T=T, jumps=jset, s=s, n=n, kinds=kinds, cj=cj, A=A, P=P, Q=Q, th=th)


def Qm(m, i):
    return 0 if i < 0 else m['Q'][i]


def Am(m, i):
    return 0 if i < 0 else m['A'][i]


def slot_window_check(m):
    s, n, kinds, P, cj = m['s'], m['n'], m['kinds'], m['P'], m['cj']
    for k in range(-1, n):
        for j in range(k, n):
            sig = sum(P[k + 1:j + 1])
            cont = sum(1 for i in range(k + 1, j + 1) if kinds[i] != 'jump')
            lo = s[k + 1] if j > k else None
            cjw = 0 if j == k else sum(1 for v in cj if s[k + 1] <= v < s[j + 1])
            assert sig == cont - cjw + Qm(m, j) - Qm(m, k), ('slot window', k, j)
    return True


def edge(m, W):
    """k, j, E_edge (definition), its second form, and the checks of eq:edge for a physical interval W."""
    s, n, kinds, P, cj = m['s'], m['n'], m['kinds'], m['P'], m['cj']
    inW = [i for i in range(n) if s[i] in W]
    if inW:
        assert inW == list(range(inW[0], inW[-1] + 1)), ('not contiguous', W)
        k, j = inW[0] - 1, inW[-1]
        if k >= 0:
            assert W.before(s[k]), ('k not before W', W, k)
    else:
        bef = [i for i in range(n) if W.before(s[i])]
        k = bef[-1] if bef else -1
        j = k
    sig = sum(P[i] for i in inW)
    cont = sum(1 for i in inW if kinds[i] != 'jump')
    cW = sum(1 for v in cj if v in W)
    dQ = Qm(m, j) - Qm(m, k)
    E = sig - cont + cW - dQ
    Wo = Interval(s[k + 1], s[j + 1], True, False) if j > k else None
    inWo = (lambda v: v in Wo) if Wo else (lambda v: False)
    plus = [v for v in cj if v in W and not inWo(v)]
    minus = [v for v in cj if inWo(v) and v not in W]
    assert E == len(plus) - len(minus), ('second form', W, E, len(plus), len(minus))
    # localisation of the two cut parts
    for v in plus:
        assert k >= 0 and s[k] <= v < s[k + 1], ('W minus Wo not in J_k', W, v, k)
    for v in minus:
        assert s[j] <= v < s[j + 1] and not W.before(v), ('Wo minus W not in J_j', W, v, j)
    assert -Am(m, j) <= E <= Am(m, k), ('bounds', W, E)
    assert abs(E) <= 1 + max(Qm(m, k), Qm(m, j))
    assert abs(dQ) <= max(Qm(m, k), Qm(m, j))
    return k, j, E, dQ, sig, cont, cW


def rand_point(rng, m, lo, hi):
    r = rng.random()
    s, jumps, cj = m['s'], m['jumps'], m['cj']
    if r < 0.25:
        return rng.choice(s)
    if r < 0.35:
        return rng.choice(jumps)
    if r < 0.45 and cj:
        return rng.choice(cj)
    return lo + (hi - lo) * Fr(rng.randint(0, 100000), 100000)


def physical_checks(rng, m, trials):
    s, n = m['s'], m['n']
    lo, hi = Fr(-3), s[n] - Fr(1, 1000)
    nz = 0
    for _ in range(trials):
        a = rand_point(rng, m, lo, hi)
        b = rand_point(rng, m, lo, hi)
        if b < a:
            a, b = b, a
        if b >= s[n]:
            continue
        lc, rc = rng.random() < 0.5, rng.random() < 0.5
        if a == b and not (lc and rc):
            continue
        W = Interval(a, b, lc, rc)
        k, j, E, dQ, *_ = edge(m, W)
        nz += E != 0
        # additivity of dQ + E_edge over a split
        c = a + (b - a) * Fr(rng.randint(0, 1000), 1000)
        if rng.random() < 0.3:
            cand = [x for x in s + m['cj'] if a <= x <= b]
            if cand:
                c = rng.choice(cand)
        side = rng.random() < 0.5  # c belongs to the left or right piece
        W1 = Interval(a, c, lc, side and (c < b or rc))  # W1 = W cap {x <= c} or {x < c}
        W2 = Interval(c, b, (not side) and (c > a or lc), rc)  # W2 = W minus W1
        pieces = []
        for Wi in (W1, W2):
            if Wi.a == Wi.b and not (Wi.lc and Wi.rc):
                continue
            if Wi.a > Wi.b:
                continue
            pieces.append(Wi)
        tot = sum(edge(m, Wi)[2] + edge(m, Wi)[3] for Wi in pieces)
        assert tot == E + dQ, ('additivity', W, W1, W2)
    # slot-window physical intervals: W° = W and E_edge = 0
    for k in range(-1, n - 1):
        for j in range(k + 1, n):
            if s[j + 1] == s[k + 1]:
                continue
            W = Interval(s[k + 1], s[j + 1], True, False)
            kk, jj, E, *_ = edge(m, W)
            assert E == 0, ('slot interval', k, j)
            assert s[kk + 1] == s[k + 1] and s[jj + 1] == s[j + 1]
    return nz


def granularity_check(rng, m, trials):
    s, n, kinds, C = m['s'], m['n'], m['kinds'], m['C']
    worst = 0
    for _ in range(trials):
        a = rand_point(rng, m, Fr(-3), s[n] - 1)
        b = rand_point(rng, m, Fr(-3), s[n] - 1)
        if b < a:
            a, b = b, a
        W = Interval(a, b, rng.random() < 0.5, rng.random() < 0.5)
        cont = sum(1 for i in range(n) if kinds[i] != 'jump' and s[i] in W)
        integral = (C(b) if b > 0 else 0) - (C(a) if a > 0 else 0)
        worst = max(worst, abs(cont - integral))
        assert abs(cont - integral) <= 2, ('granularity', W, cont, integral)
    return worst


def ebox_check(rng, m, H0, c1, trials):
    """E_box = sigma(W_y) - H(y) rho~(y), W_y closed, boxes half-open of width H(s_q)."""
    s, n, P = m['s'], m['n'], m['P']
    H = lambda x: H0 + c1 * x
    primes = [s[i] for i in range(n) if P[i] == 1]
    gaps = [b - a for a, b in zip(primes, primes[1:])]
    worst = Fr(0)
    for _ in range(trials):
        r = rng.random()
        if r < 0.5:
            q = rng.choice(primes)
            # put y so that a prime sits at (or just inside/outside) an edge of W_y or of its box
            sgn = rng.choice([-1, 1])
            y = q - sgn * H(q) / 2 + Fr(rng.randint(-2, 2), 10 ** 6)
        else:
            y = s[0] + (s[n] - s[0]) * Fr(rng.randint(0, 10 ** 6), 10 ** 6)
        Hy = H(y)
        if y - Hy / 2 < s[0] + 0 or y + 2 * Hy > s[n]:
            continue
        sigW = sum(1 for q in primes if y - Hy / 2 <= q <= y + Hy / 2)
        box = [q for q in primes if -H(q) / 2 <= y - q < H(q) / 2]
        Hrho = sum(Hy / H(q) for q in box)
        Eb = sigW - Hrho
        lo_extra = sum(1 for q in primes if y - Hy / 2 <= q <= y + Hy / 2 and q not in box)
        hi_extra = sum(1 for q in box if not (y - Hy / 2 <= q <= y + Hy / 2))
        assert lo_extra <= 1 and hi_extra <= 1, ('ends', y, lo_extra, hi_extra)
        wdev = sum(abs(Hy / H(q) - 1) for q in box)
        assert abs(Eb) <= 1 + wdev + 0, ('E_box', y, Eb, wdev)
        worst = max(worst, abs(Eb))
    return worst, min(gaps)


def margin_algebra(rng, trials=2000):
    """Random reals: check rho~ + BKrho = T~' - NT - nu with nu as in eq:margin-identity (signs only)."""
    for _ in range(trials):
        Hy = Fr(rng.randint(5, 50))
        cont, Cjit, dQ, Eedge = [Fr(rng.randint(-20, 20)) for _ in range(4)]
        BK, BKA, NT, C2 = [Fr(rng.randint(-50, 50), 7) for _ in range(4)]
        sigma = cont - Cjit + dQ + Eedge  # eq:edge for W_y
        rho = Fr(rng.randint(0, 100), 9)
        Ebox = sigma - Hy * rho
        Comp = Hy * (BK - BKA + NT)
        Mart = Cjit - Comp - C2
        nu = (Mart - dQ - Eedge + C2 + Ebox) / Hy
        Ttil = cont / Hy + BKA
        assert rho + BK == Ttil - NT - nu
    return True


def main(seeds):
    tot_nz = 0
    worst_g = 0
    worst_b = 0
    ngap = None
    for seed in seeds:
        rng = random.Random(seed)
        th = rng.choice([Fr(1, 2), Fr(1, 3), Fr(1, 7), Fr(1, 1000)])
        dens = rng.choice([(0, 0, 0, 1, 1, 2, 3, 4), (0, 0, 0, 0, 0, 1, 1, 2), (0, 0, 0, 0, 0, 0, 0, 1)])
        m = build(rng, rng.randint(15, 45), th, dens)
        slot_window_check(m)
        tot_nz += physical_checks(rng, m, 400)
        worst_g = max(worst_g, granularity_check(rng, m, 300))
        m = build(rng, 120, th, (0,) * 12 + (1,))
        if sum(m['P']) >= 5:
            wb, g = ebox_check(rng, m, Fr(rng.randint(8, 25)), Fr(1, rng.choice([200, 1000, 5000])), 300)
            worst_b = max(worst_b, wb)
            ngap = g if ngap is None else min(ngap, g)
    margin_algebra(random.Random(1))
    kinds_count = {}
    print('seeds', len(seeds), 'windows with E_edge != 0:', tot_nz)
    print('max |#cont - int T_cont| over windows:', float(worst_g))
    print('max |E_box| observed:', float(worst_b), ' min gap between decided-prime slot starts:', float(ngap))
    print('all checks passed')


if __name__ == '__main__':
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    main(range(k))
