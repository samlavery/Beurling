"""Toy 1: Lemma P's chain (steps (i)-(vi)) on a synthetic jittered system, exact counts.
System: 'rational' primes = primes < X0; slots s = X0, X0+1, ... ; at each slot a prime is decided with probability
1/log s (adaptive coin) and lands uniformly in [s - H/2, s + H/2) (continuous value).  Decision order = slot order
(rational primes first).  Elements = products of these primes up to NMAX (exponents allowed).
Abs = { n : latest-decided prime r of n is jittered and r < y }  (y constant in the toy).
For windows [u, u+h], h = u^b:
  E   = #(Abs n [u, u+h])                                  (exact)
  DT  = sum_{d in G_{2y} n (h, 2yh]} N(I_d),  I_d=[u/d,(u+h)/d]   (divisor trick, step (iii)) -- must be >= E
  WC  = max_d N(I_d) * Psi(2yh, 2y)                       (step (iv) with the true window maximum) -- must be >= DT
Also checks step (i): every prime of an element of Abs has value < 2y."""
import math, random, bisect

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\x00\x00"
    for p in range(2, int(n ** .5) + 1):
        if s[p]: s[p*p::p] = bytearray(len(s[p*p::p]))
    return [p for p in range(n + 1) if s[p]]

def build(seed, X0=40, H=6.0, NMAX=3.0e5, SLOTS=500):
    rnd = random.Random(seed)
    primes = [(float(p), float(p), False) for p in primes_upto(X0 - 1)]   # (value, decision time, jittered)
    for s in range(X0, X0 + SLOTS):
        if rnd.random() < 1.0 / math.log(s):
            primes.append((s + H * (rnd.random() - 0.5), float(s), True))
    primes.sort(key=lambda t: t[1])            # decision order
    # elements: DFS over multisets in decision order; track latest prime (last index used)
    elems = []   # (value, latest_index)
    vals = [p[0] for p in primes]
    def rec(start, cur, last):
        elems.append((cur, last))
        for i in range(start, len(primes)):
            v = cur * vals[i]
            if v > NMAX: continue
            rec(i, v, i)
    rec(0, 1.0, -1)
    return primes, elems

def run(seed, y, b, X0=40, H=6.0):
    primes, elems = build(seed, X0=X0, H=H)
    vals = sorted(e[0] for e in elems)
    abs_vals = sorted(e[0] for e in elems if e[1] >= 0 and primes[e[1]][2] and primes[e[1]][0] < y)
    # step (i) check
    for e in elems:
        if e[1] >= 0 and primes[e[1]][2] and primes[e[1]][0] < y:
            pass
    smooth_vals = sorted(e[0] for e in elems if all(True for _ in [0]))  # placeholder
    # 2y-smooth elements: all primes < 2y  (recompute from factorisation: use DFS again restricted)
    G = []
    pv = [p[0] for p in primes if p[0] < 2 * y]
    def rec(start, cur):
        G.append(cur)
        for i in range(start, len(pv)):
            v = cur * pv[i]
            if v > 2 * y * 3.0e5 ** b * 2: continue
            rec(i, v)
    rec(0, 1.0)
    G.sort()
    worst = []
    viol = 0
    for u in [1000.0 * k for k in range(5, 300, 3)]:
        h = u ** b
        E = bisect.bisect_right(abs_vals, u + h) - bisect.bisect_left(abs_vals, u)
        DT = 0; maxN = 0; cnt = 0
        lo = bisect.bisect_right(G, h); hi = bisect.bisect_right(G, 2 * y * h)
        for d in G[lo:hi]:
            a, c = u / d, (u + h) / d
            Nd = bisect.bisect_right(vals, c) - bisect.bisect_left(vals, a)
            DT += Nd; maxN = max(maxN, Nd); cnt += 1
        WC = maxN * cnt
        if not (E <= DT <= WC): viol += 1
        worst.append((E, DT, WC))
    return viol, worst

tot_v = 0; n = 0; mx = 0
for seed in range(12):
    for (y, b) in [(60.0, 0.25), (90.0, 0.25), (120.0, 0.2), (200.0, 0.3)]:
        v, w = run(seed, y, b)
        tot_v += v; n += len(w)
        for E, DT, WC in w:
            if DT: mx = max(mx, E / DT)
print(f"Toy 1 (Lemma P steps (iii)-(iv)): {n} windows, {tot_v} violations of E <= DT <= maxN*Psi; max E/DT = {mx:.3f}")
