# Greedy rule on the toy target: Lemma count, Lindley, and the exact decomposition of Cor lag, with empty slots.
import random, sys
from fractions import Fraction as F
from bisect import bisect_left, bisect_right
sys.path.insert(0, sys.argv[1])
from toy import build_random

def run(seed, theta, H=F(6)):
    rnd = random.Random(seed)
    P = build_random(seed, theta=theta)
    ms = max(P.sl)
    X0 = P.X0; jmax = int(P.T) - 3
    s = {j: P.hit(j + theta) for j in range(X0, jmax + 2)}
    kind = {j: ('jump' if P.Tval(s[j], left=True) < j + theta else 'cont') for j in range(X0, jmax + 1)}
    # composites: one at each jump point (rigid / absorbed), plus jittered composites at random non-jump values
    comps = list(P.jpos)
    jset = set(P.jpos)
    for _ in range(int((s[jmax] - s[X0]) / 3)):
        v = s[X0] + (s[jmax] - s[X0]) * F(rnd.randint(1, 10**6 - 1), 10**6)
        if v not in jset: comps.append(v)
    # also put some exactly at continuous-slot starts that are not jump points
    for j in range(X0, jmax + 1):
        if kind[j] == 'cont' and s[j] < s[j + 1] and rnd.random() < 0.1: comps.append(s[j])
    comps.sort()
    Q = {X0 - 1: 0}; primes = []   # (slot j, value)
    for j in range(X0, jmax + 1):
        A = bisect_left(comps, s[j + 1]) - bisect_left(comps, s[j])
        if kind[j] == 'jump': assert A >= 1
        if s[j] == s[j + 1]: assert A == 0
        Pj = max(0, 1 - Q[j - 1] - A)
        Q[j] = Q[j - 1] + A + Pj - 1
        assert Q[j] == max(0, Q[j - 1] + A - 1)                          # Lindley form
        if Pj:
            assert kind[j] == 'cont'
            primes.append((j, s[j] + H * (F(rnd.randint(0, 10**6 - 1), 10**6) - F(1, 2))))
    # Lindley closed form at a few j
    for j in list(range(X0, jmax + 1))[::37]:
        best = 0
        acc = 0
        for i in range(j, X0 - 2, -1):          # windows (i, j]
            if i < j:
                acc += bisect_left(comps, s[i + 2]) - bisect_left(comps, s[i + 1]) - 1
            best = max(best, acc)
        assert Q[j] == best, (j, Q[j], best)
    nempty_prime = sum(1 for j, _ in primes if s[j] == s[j + 1])
    # Lemma count: V_j = j + 1 + Q_j, with V counting composites < s_{j+1}, decided primes <= j, the rational
    # primes and composites below X0 (the X0 - 1 elements of [1, X0)), and 1 for the element 1 -- here folded in.
    for j in range(X0 - 1, jmax + 1):
        ncomp = bisect_left(comps, s[j + 1])                 # composites of value in [X0, s_{j+1})
        npr = sum(1 for (i, _) in primes if i <= j)
        V = (X0 - 1) + ncomp + npr                           # (X0 - 1) = #N cap [1, X0) incl. 1
        assert V == j + 1 + Q[j], (j, V, j + 1 + Q[j])
    # exact lag decomposition and the bounds of Cor lag
    pv = sorted(v for _, v in primes)
    cs = [s[j] for j in range(X0, jmax + 1) if kind[j] == 'cont']
    worst = [F(10**9), F(-10**9)]
    xs = [s[X0] + 2 * H + (s[jmax] - s[X0] - 4 * H) * F(rnd.randint(0, 10**6), 10**6) for _ in range(3000)]
    xs += [s[j] for j in range(X0, jmax) if s[X0] + 2 * H <= s[j] <= s[jmax] - 2 * H]
    svals = [s[j] for j in range(X0, jmax + 2)]
    for x in xs:
        j = X0 + bisect_right(svals, x) - 1
        assert s[j] <= x < s[j + 1]
        N = (X0 - 1) + bisect_right(comps, x) + bisect_right(pv, x)
        D = N - P.Tval(x)
        C = bisect_left(comps, s[j + 1]) - bisect_right(comps, x)
        Ep = sum(1 for (i, v) in primes if i > j and v <= x)
        Em = sum(1 for (i, v) in primes if i <= j and v > x)
        assert D == (j - P.Tval(x)) + Q[j] + 1 - C + Ep - Em
        # slots counted by E_- start in (x - H/2, x], those by E_+ in (x, x + H/2]
        for (i, v) in primes:
            if i <= j and v > x: assert x - H / 2 < s[i] <= x
            if i > j and v <= x: assert x < s[i] <= x + H / 2
        nm = bisect_right(cs, x) - bisect_right(cs, x - H / 2)
        npl = bisect_right(cs, x + H / 2) - bisect_right(cs, x)
        assert Em <= nm <= P.cmass(x) - P.cmass(x - H / 2) + 1
        assert Ep <= npl <= P.cmass(x + H / 2) - P.cmass(x) + 1
        mq = max(Q[i] for i in range(X0, j + 1))
        assert D <= mq + ms * H / 2 + 3 and D >= -ms * H / 2 - 3, (x, D)
        worst[0] = min(worst[0], D + ms * H / 2); worst[1] = max(worst[1], D - mq - ms * H / 2)
    return len(primes), nempty_prime, worst

if __name__ == "__main__":
    tot = [0, 0]; lo, hi = F(10**9), F(-10**9)
    for seed in range(int(sys.argv[2])):
        for theta in (F(1, 2), F(1, 3), F(1, 7)):
            r = run(seed + 1000, theta)
            if r is None: continue
            tot[0] += r[0]; tot[1] += r[1]; lo = min(lo, r[2][0]); hi = max(hi, r[2][1])
    print("OK primes=%d placed-at-empty-slots=%d  min(D+H/2)=%s  max(D-maxQ-H/2)=%s" % (tot[0], tot[1], float(lo), float(hi)))
