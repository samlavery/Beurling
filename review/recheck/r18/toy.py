# Exact-rational toy for correction #77: slots of a right-continuous non-decreasing T with unit jumps,
# forced ties T(d-) = j + theta, runs of jump slots; checks every slot fact claimed in the repaired text.
import random, sys
from fractions import Fraction as F
from bisect import bisect_left, bisect_right

class Path:
    """T(x) = floor(x) below X0; T(X0) = X0; then consecutive linear pieces (slope > 0) and jumps at piece ends."""
    def __init__(self, X0):
        self.X0 = X0
        self.a, self.b, self.sl, self.C = [], [], [], []   # pieces and continuous mass at piece start
        self.jpos, self.jsz = [F(X0)], [1]                 # jump positions (sorted) and sizes
        self.x, self.T, self.cm = F(X0), F(X0), F(0)
    def run(self, length, slope):
        self.a.append(self.x); self.b.append(self.x + length); self.sl.append(slope); self.C.append(self.cm)
        self.x += length; self.T += slope * length; self.cm += slope * length
    def run_to_level(self, level, slope):
        assert level > self.T
        self.run((level - self.T) / slope, slope)
    def jump(self, size=1):
        if self.jpos[-1] == self.x: self.jsz[-1] += size
        else: self.jpos.append(self.x); self.jsz.append(size)
        self.T += size
    def finish(self):
        self.jcum = [0]
        for z in self.jsz: self.jcum.append(self.jcum[-1] + z)
        # monotone list of (value, kind, piece) for hitting times
        self.mono = []
        for i in range(len(self.a)):
            ts = self.Tval(self.a[i]); te = ts + self.sl[i] * (self.b[i] - self.a[i])
            self.mono.append((ts, 0, i)); self.mono.append((te, 1, i))
        self.monov = [m[0] for m in self.mono]
        assert all(x <= y for x, y in zip(self.monov, self.monov[1:]))
    def cmass(self, x):
        i = bisect_right(self.a, x) - 1
        if i < 0: return F(0)
        return self.C[i] + self.sl[i] * (min(x, self.b[i]) - self.a[i])
    def Tval(self, x, left=False):
        if x < self.X0: return F(x.__floor__())
        if left and x == self.X0: return F(self.X0 - 1)
        k = bisect_left(self.jpos, x) if left else bisect_right(self.jpos, x)
        return F(self.X0 - 1) + self.jcum[k] + self.cmass(x)
    def hit(self, c):
        k = bisect_left(self.monov, c)
        v, kind, i = self.mono[k]
        if kind == 0: return self.a[i]                      # reached at a piece start (by a jump, or exactly)
        ts = self.mono[k - 1][0]
        return self.a[i] + (c - ts) / self.sl[i]
    def jumps_in(self, lo, hi, lo_closed=True):
        i = bisect_left(self.jpos, lo) if lo_closed else bisect_right(self.jpos, lo)
        j = bisect_left(self.jpos, hi)
        return list(zip(self.jpos[i:j], self.jsz[i:j]))

def build_random(seed, X0=20, theta=F(1, 3), nsteps=600, p_tie=0.25, p_jump=0.35, p_double=0.0):
    rnd = random.Random(seed)
    P = Path(X0)
    P.run(F(rnd.randint(1, 9), 10) * theta / 2, F(1, 2))  # start-up: rise below the first level
    def next_level():
        nxt = (P.T - theta).__floor__() + 1 + theta
        return nxt if nxt > P.T else nxt + 1
    for _ in range(nsteps):
        slope = F(rnd.randint(1, 12), 10)          # slopes in [0.1, 1.2]
        r = rnd.random()
        if r < p_tie:                              # tie: continuous approach to a level, jump starts on it
            P.run_to_level(next_level(), slope); P.jump(2 if rnd.random() < p_double else 1)
            if rnd.random() < 0.3:                 # back-to-back jump right after the tie
                P.run(F(1, rnd.randint(50, 500)), slope); P.jump(1)
        elif r < p_tie + p_jump:                   # generic jump, possibly a run of near-coincident jumps
            P.run(F(rnd.randint(1, 40), 37), slope); P.jump(2 if rnd.random() < p_double else 1)
            while rnd.random() < 0.4:
                P.run(F(1, rnd.randint(50, 500)), slope); P.jump(1)
        else:                                      # continuous stretch, sometimes touching a level exactly
            if rnd.random() < 0.5: P.run_to_level(next_level(), slope)
            P.run(F(rnd.randint(1, 60), 23), slope)
    P.run(F(5), F(1)); P.finish()
    return P

def check(P, theta, strict_unit=True):
    X0 = P.X0
    jmax = int(P.T) - 3
    s = [P.hit(j + theta) for j in range(X0, jmax + 2)]          # s[j - X0]
    S = lambda j: s[j - X0]
    st = dict(jump=0, cont=0, empty=0, runs=0, land_on_level=0)
    kind = {}
    for j in range(X0, jmax + 1):
        sj, sj1 = S(j), S(j + 1)
        assert sj <= sj1 and sj >= X0
        assert P.Tval(sj) >= j + theta and P.Tval(sj, left=True) <= j + theta      # minimum
        if sj < sj1:                                                                 # J_j = [s_j, s_{j+1})
            for t in (sj, (sj + sj1) / 2, sj1 - (sj1 - sj) / 997):
                v = P.Tval(t); assert j + theta <= v < j + 1 + theta, (j, t, v)
            assert P.Tval(sj1) >= j + 1 + theta
        Tl = P.Tval(sj, left=True)
        if Tl < j + theta:
            kind[j] = 'jump'; st['jump'] += 1
            assert sj < sj1, ("empty jump slot", j)
            js = P.jumps_in(sj, sj1)
            assert len(js) == 1 and js[0][0] == sj and js[0][1] == 1, ("jump slot content", j, js)
            if P.Tval(sj) == j + theta: st['land_on_level'] += 1
        else:
            assert Tl == j + theta
            kind[j] = 'cont'; st['cont'] += 1
            if sj == sj1:
                st['empty'] += 1
                js = P.jumps_in(sj, sj + F(1, 10**9))
                assert js and js[0][0] == sj and P.Tval(sj, left=True) == j + theta     # a tie
            else:
                assert not P.jumps_in(sj, sj1), ("jump inside continuous slot", j)
    # every jump at or after s_{X0} lies in exactly one jump slot, at its start
    for d, z in zip(P.jpos, P.jsz):
        if d < S(X0) or d >= S(jmax + 1): continue
        k = bisect_right(s, d) - 1; j = X0 + k
        assert S(j) <= d < S(j + 1) and kind[j] == 'jump' and S(j) == d
    # an empty continuous slot is followed by a jump slot
    for j in range(X0, jmax):
        if kind[j] == 'cont' and S(j) == S(j + 1): assert kind[j + 1] == 'jump'
    # counting fact
    conts = [j for j in range(X0, jmax + 1) if kind[j] == 'cont']
    for a, b in zip(conts, conts[1:]):
        m = P.cmass(S(b)) - P.cmass(S(a))
        assert m == 1, ("counting fact fails", a, b, m)
        if b - a > 2: st['runs'] += 1
    cs = [S(j) for j in conts]
    assert all(x < y for x, y in zip(cs, cs[1:]))                                    # distinct starts
    ms = max(P.sl)
    assert all((y - x) * ms >= 1 for x, y in zip(cs, cs[1:]))                       # spacing >= 1/max T'_cont
    # slot length: continuous mass on J_j < 1
    for j in range(X0, jmax + 1):
        assert P.cmass(S(j + 1)) - P.cmass(S(j)) <= 1
    rnd = random.Random(7)
    top = S(jmax)
    for _ in range(2000):                                                            # physical windows
        a = S(X0) + (top - S(X0)) * F(rnd.randint(0, 10**6), 10**6)
        if rnd.random() < 0.3: a = rnd.choice(cs)                                    # endpoints on starts
        b = min(top, a + F(rnd.randint(0, 4000), 89))
        n_ho = bisect_left(cs, b) - bisect_left(cs, a)                               # starts in [a, b)
        n_cl = bisect_right(cs, b) - bisect_left(cs, a)                              # starts in [a, b]
        m = P.cmass(b) - P.cmass(a)
        assert m - 1 <= n_ho <= m + 1 and n_cl <= m + 1, (a, b, n_ho, n_cl, m)
    for _ in range(2000):                                                            # slot windows (k, j]
        k = rnd.randint(X0, jmax - 2); j = rnd.randint(k + 1, jmax - 1)
        n = sum(1 for i in conts if k < i <= j)
        m = P.cmass(S(j + 1)) - P.cmass(S(k + 1))
        assert m - 1 <= n <= m + 1, (k, j, n, m)
        # Lemma excess (the rigid/Abs part): jumps with value in [s_{k+1}, s_{j+1}) = jump slots of (k, j]
        nj = sum(z for _, z in P.jumps_in(S(k + 1), S(j + 1)))
        assert nj == sum(1 for i in range(k + 1, j + 1) if kind[i] == 'jump')
        # sandwich: continuous starts in I = [floor s_{k+1}, ceil s_{j+1}) not indexed in (k, j]
        lo, hi = F(S(k + 1).__floor__()), F(S(j + 1).__ceil__())
        extra = [i for i in conts if lo <= S(i) < hi and not (k < i <= j)]
        left = [i for i in extra if i <= k]; right = [i for i in extra if i > j]
        assert all(lo <= S(i) <= S(k + 1) for i in left) and all(S(j + 1) <= S(i) < hi for i in right)
        if ms <= 1: assert len(left) <= 2 and len(right) <= 2, (k, j, left, right)
    return st

if __name__ == "__main__":
    nseed = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    tot = dict(jump=0, cont=0, empty=0, runs=0, land_on_level=0)
    for seed in range(nseed):
        for theta in (F(1, 2), F(1, 3), F(1, 7), F(5, 11)):
            for capped in (False, True):
                P = build_random(seed, theta=theta) if not capped else None
                if capped:   # slopes <= 1, so the 0.99-spacing edge count applies
                    rnd = random.Random(seed)
                    P = build_random(seed + 1000, theta=theta)
                    if max(P.sl) > 1: continue
                st = check(P, theta)
                for k in tot: tot[k] += st[k]
    print("OK", tot)
