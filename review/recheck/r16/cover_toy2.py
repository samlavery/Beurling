# Toy check of the covering arguments of #75 (Corollary increment, Lemma P(iv)).
# Heights z_k = Z0*2^k (k >= -1); grid step d(k) decreasing in k; windows at height z_k are
# [g, g+2d) with g = j*d(k) in [z_k, 2 z_k). Exact rationals.
from fractions import Fraction as F
import random, math
random.seed(1)
Z0 = 64
def z(k): return F(Z0) * (F(2)**k)
def d(k): return F(2, (k+12)**2) * F(9973, 10007)   # decreasing step, misaligned with z
def windows_at(k, lo, hi):
    """windows at height k whose span meets [lo,hi]"""
    st = d(k); zk = z(k)
    jmin = math.ceil(zk/st); jmax = math.ceil(2*zk/st) - 1   # left ends in [zk, 2zk)
    a = max(jmin, math.floor((lo - 2*st)/st)); b = min(jmax, math.ceil(hi/st))
    return [(j*st, j*st + 2*st, k) for j in range(a, b+1)]
def height_of(w):
    k = -1
    while not (z(k) <= w < 2*z(k)): k += 1
    return k
def min_cover(I_lo, I_hi, wins):
    # greedy cover of closed [I_lo, I_hi] by half-open windows [a,b), windows sorted by left end
    wins = sorted(wins); pos = I_lo; n = 0; used = []; i = 0; best = None
    while True:
        while i < len(wins) and wins[i][0] <= pos:
            if wins[i][1] > pos and (best is None or wins[i][1] > best[1]): best = wins[i]
            i += 1
        if best is None or best[1] <= pos: return None, used
        n += 1; used.append(best)
        if best[1] > I_hi: return n, used
        pos = best[1]
fails = 0; worst_inc = 0; worst_P = F(-10**9)
for trial in range(20000):
    k0 = random.randint(0, 8)
    # place w near the dyadic point z(k0) or 2 z(k0)
    base = z(k0) if random.random() < 0.5 else 2*z(k0)
    w = base + F(random.randint(-3000, 13000), 10000) * d(k0)
    if w < z(-1) + 1: continue
    kz = height_of(w)
    # Corollary increment: length <= d(kz)
    l1 = F(random.randint(1, 1000), 1000) * d(kz)
    wins = windows_at(kz-1, w, w+l1) if kz-1 >= -1 else []
    wins += windows_at(kz, w, w+l1)
    n, used = min_cover(w, w+l1, wins)
    if n is None or n > 2: fails += 1; print("INC FAIL", w, l1, kz, n)
    worst_inc = max(worst_inc, n or 99)
    # the specific windows named in the proof
    st = d(kz); g = math.floor(w/st)*st
    if g >= z(kz):
        ok = g <= w and w + l1 < g + 2*st
    else:
        zp = math.ceil(z(kz)/st)*st; s2 = d(kz-1); gpp = (math.ceil(z(kz)/s2)-1)*s2
        ok = (kz >= 0) and gpp >= z(kz-1) and gpp < w and gpp + 2*s2 >= zp and w + l1 < zp + 2*st
    if not ok: fails += 1; print("NAMED FAIL", w, l1, kz)
    # Lemma P(iv): interval of length < 1 starting at w, heights kz-1, kz, kz+1
    l2 = F(random.randint(1, 9999), 10000)
    wins = []
    for kk in (kz-1, kz, kz+1):
        if kk >= -1: wins += windows_at(kk, w, w+l2)
    n2, used2 = min_cover(w, w+l2, wins)
    if n2 is None: fails += 1; print("P FAIL cover", w, l2); continue
    # bound l/(2 d(kz+1)) + 5 (the paper: (log 2z)^6/4 + 5 with delta_1 = 2(log)^-6)
    bound = l2/(2*d(kz+1)) + 5
    worst_P = max(worst_P, F(n2) - bound)
    if n2 > bound: fails += 1; print("P FAIL count", n2, float(bound))
print("fails", fails, "max windows (increment)", worst_inc, "max (count - bound) P(iv)", float(worst_P))
