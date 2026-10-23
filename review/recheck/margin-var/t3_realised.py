# T3: realised-versus-rational toy.
#   * Lemma M in the realised system (decision order t = slot) against the direct recursion of the Neumann series;
#   * D(u) := (K'_Q - K_pt) g (u), its vanishing for u < 2 X0 X0m/(1+k);
#   * the identity rho_edge - g = (1+K_pt)^{-1} D, with rho_edge computed directly as (1+K_pt)^{-1} mu_edge;
#   * |rho_edge - g|(x) <= (sum_{n<=x/X0m} 1/n) sup_{u<=x}|D(u)|   (the Lemma M step);
#   * |D(u)| against the Step-3 bound with measured constants (k=2 and k=3 cofactors, ordered telescoping).
import sys, math, random, bisect, itertools, json
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from toy_common import Toy, System


def make_realised(toy, variant, eps, seed, vmax):
    rnd = random.Random(seed)
    H = toy.H
    out = []
    rp = [p for p in toy.large_rat if p <= vmax + 10]
    for i, p in enumerate(rp):
        if variant == 'del' and rnd.random() < eps:
            continue
        out.append((p + rnd.uniform(-H / 2, H / 2), float(p)))
        if variant == 'add' and rnd.random() < eps:
            nxt = rp[i + 1] if i + 1 < len(rp) else p + 2
            s = rnd.uniform(p, nxt)
            out.append((s + rnd.uniform(-H / 2, H / 2), s))
        if variant == 'drift':
            # extra primes at rate eps per unit length on [p, next p): models the +(k/2)Psi drift
            nxt = rp[i + 1] if i + 1 < len(rp) else p + 2
            t = p
            while True:
                t += rnd.expovariate(eps)
                if t >= nxt:
                    break
                out.append((t + rnd.uniform(-H / 2, H / 2), t))
    out = [(v, s) for v, s in out if v >= toy.X0m]
    return out


class Model:
    def __init__(self, X0, kappa, H, umax, variant, eps, seed):
        self.toy = toy = Toy(X0, kappa, H, LIM=max(200000, int(umax / X0) * 2))
        self.kappa = kappa
        self.Wmax = (1 + kappa) * umax / (2 * X0) + 5
        self.real = System(toy, make_realised(toy, variant, eps, seed, self.Wmax))
        self.rat = System(toy, [(float(p), float(p)) for p in toy.large_rat if p <= self.Wmax + 10])
        self.Er = self.real.elements_with_large(self.Wmax)
        self.Eq = self.rat.elements_with_large(self.Wmax)
        self.Erv = [e[0] for e in self.Er]
        self.Eqv = [e[0] for e in self.Eq]
        self.Dcache = {}

    def g(self, v):
        return self.toy.g_formula(v)

    def D(self, u, value_order=False):
        key = (round(u, 9), value_order)
        if key in self.Dcache:
            return self.Dcache[key]
        toy = self.toy
        W = (1 + self.kappa) * u / (2 * toy.X0)
        s = 0.0
        j = bisect.bisect_right(self.Eqv, W)
        for (w, d, idx, tau) in self.Eq[:j]:
            if tau * w < u:
                s += self.g(u / w) / w
        j = bisect.bisect_right(self.Erv, W)
        for (w, d, idx, tau) in self.Er[:j]:
            t = max(self.real.vals[i] for i in idx) if value_order else tau
            if t * w < u:
                s -= self.g(u / w) / w
        self.Dcache[key] = s
        return s

    # ---- (1+K_pt)^{-1} h at x via Lemma M (realised) ----
    def resolvent_real(self, h, x, nmin_value=0.0):
        toy = self.toy
        s = 0.0
        # rigid n (rational, t = value)
        nmax = int(x / toy.X0m)
        for n in toy.smooth:
            if n > nmax:
                break
            if toy.mu[n] == 0 or not toy.chi_rat(n, x):
                continue
            hv = h(x / n)
            if hv:
                s += toy.mu[n] * hv / n
        j = bisect.bisect_right(self.Erv, x / toy.X0m)
        for el in self.Er[:j]:
            c = self.real.c_lemmaM(el, x)
            if c:
                hv = h(x / el[0])
                if hv:
                    s += c * hv / el[0]
        return s

    def resolvent_rat(self, h, x):
        toy = self.toy
        s = 0.0
        nmax = int(x / toy.X0)
        for n in range(1, nmax + 1):
            if toy.mu[n] == 0 or not toy.chi_rat(n, x):
                continue
            hv = h(x / n)
            if hv:
                s += toy.mu[n] * hv / n
        return s

    # ---- direct Neumann recursion of the realised resolvent coefficient (no Lemma M) ----
    def c_recursive(self, el, x):
        """c_n(x) = - sum_{d | n, d < n} 1[tau_{n/d} n < x] 1[x/n >= X0m] c_d(x), over divisors in NN."""
        toy = self.toy
        value, dd, idx, tau = el
        fd = toy.factor(dd)
        small = []
        for p, e in fd:
            small += [p] * e
        large = list(idx)
        if x / value < toy.X0m:
            return 0
        prim = [('s', p) for p in small] + [('l', i) for i in large]
        n_items = len(prim)
        memo = {}

        def val_t(items):
            v = 1.0
            t = 0.0
            for kind, a in items:
                if kind == 's':
                    v *= a
                    t = max(t, a)
                else:
                    v *= self.real.large[a][0]
                    t = max(t, self.real.large[a][1])
            return v, t

        def c_of(mask):
            if mask in memo:
                return memo[mask]
            if mask == 0:
                return 1
            items = [prim[i] for i in range(n_items) if mask >> i & 1]
            nv, _ = val_t(items)
            tot = 0
            seen = set()
            sub = (mask - 1) & mask
            while True:
                # divisor d = sub (as multiset); avoid double counting equal multisets
                key = tuple(sorted(prim[i] for i in range(n_items) if sub >> i & 1))
                if key not in seen:
                    seen.add(key)
                    comp = [prim[i] for i in range(n_items) if (mask & ~sub) >> i & 1]
                    _, tq = val_t(comp)
                    if tq * nv < x:
                        tot -= c_of(sub)
                if sub == 0:
                    break
                sub = (sub - 1) & mask
            memo[mask] = tot
            return tot

        # canonical: equal multisets share value; compute on the full mask
        return c_of((1 << n_items) - 1)


def run(X0, kappa, H, umax, variant, eps, seed, n_ident, n_D, tag):
    M = Model(X0, kappa, H, umax, variant, eps, seed)
    toy = M.toy
    print(f"== {tag}: X0={X0} k={kappa} H={H} variant={variant} eps={eps}; |Er|={len(M.Er)} |Eq|={len(M.Eq)} Me={toy.Me:.4f}")
    rnd = random.Random(seed + 100)
    u0 = 2 * X0 * toy.X0m / (1 + kappa)
    # (1) Lemma M in the realised system
    bad = 0
    tot = 0
    for xr in [(u0, 3 * u0)] * 3 + [(1.5e6, umax)] * 3:
        x = rnd.uniform(*xr)
        j = bisect.bisect_right(M.Erv, x / toy.X0m)
        els = M.Er[:j]
        if len(els) > 4000:
            els = [e for e in els if len(e[2]) >= 2] + rnd.sample(els, 3000)
        for el in els:
            a = M.real.c_lemmaM(el, x)
            b = M.c_recursive(el, x)
            tot += 1
            if a != b:
                bad += 1
    print(f"  Lemma M (realised, decision order) vs recursion: {tot} coefficients, {bad} mismatches")
    # (2) D vanishes below u0
    mx = 0.0
    for _ in range(40):
        u = rnd.uniform(2 * X0, u0 * 0.999)
        mx = max(mx, abs(M.D(u)))
    print(f"  max |D(u)| for u < 2 X0 X0m/(1+k) = {u0:.0f}: {mx:.2e}")
    # (3) identity and Lemma M step
    worst_id = 0.0
    worst_lm = 0.0
    rows = []
    for _ in range(n_ident):
        x = math.exp(rnd.uniform(math.log(u0), math.log(umax)))
        re = M.resolvent_real(toy.mu_edge, x)
        gx = M.g(x)
        rD = M.resolvent_real(M.D, x)
        worst_id = max(worst_id, abs(re - gx - rD))
        # Lemma M step: |rho_edge - g| <= (sum 1/n) sup_{u<=x}|D|
        Hsum = sum(1.0 / n for n in toy.smooth if n <= x / toy.X0m) + sum(1.0 / e[0] for e in M.Er if e[0] <= x / toy.X0m)
        rows.append((x, re, gx, rD, Hsum))
    print(f"  identity rho_edge - g - (1+K_pt)^-1 D : max abs error {worst_id:.2e} over {n_ident} points")
    # (4) D on a log grid: value, value-order part, decision mismatch
    us = sorted(math.exp(rnd.uniform(math.log(u0), math.log(umax))) for _ in range(n_D))
    supD = 0.0
    Dvals = []
    for u in us:
        d = M.D(u)
        dv = M.D(u, value_order=True)
        Dvals.append((u, d, dv))
        supD = max(supD, abs(d))
    print(f"  sup|D| on {n_D} points in [{u0:.0f},{umax:.3g}]: {supD:.4e}; max |D - D_valueorder| = "
          f"{max(abs(a-b) for _, a, b in Dvals):.3e}")
    for (x, re, gx, rD, Hs) in rows[:12]:
        # sup over u <= x of |D| from the grid (lower estimate of the sup)
        sD = max([abs(d) for (u, d, _) in Dvals if u <= x] + [0.0])
        print(f"   x={x:11.1f} rho_edge*log x={re*math.log(x):+.5f}  g*log x={gx*math.log(x):+.5f}  "
              f"(rho_edge-g)*log x={(re-gx)*math.log(x):+.3e}  Hsum*supD*log x={Hs*sD*math.log(x):.3e}")
    return M, Dvals


if __name__ == '__main__':
    import pickle
    res = {}
    for variant, eps in [('jitter', 0.0), ('add', 0.15), ('del', 0.15), ('drift', 0.1)]:
        M, Dvals = run(100, 0.2, 2, 4.0e6, variant, eps, 7, 14, 60, f"toyA-{variant}")
        res[variant] = Dvals
    with open('/tmp/rhscratch/margin-var-check/out/t3_D.json', 'w') as f:
        json.dump(res, f)
