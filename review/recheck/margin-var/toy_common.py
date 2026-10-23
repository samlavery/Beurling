# Common code for the scaled-down toy of Lemma margin (b) Step 3 and (d)(iii).
# Two prime systems that agree below X0m := X0 - H/2:
#   rational:  all rational primes; "large" = rational primes >= X0 (slot = value)
#   realised:  rational primes < X0 plus a list of large primes (value, slot) with value >= X0m
# Operators (cut-offs irrelevant for functions supported on (2X0/(1+k), oo)):
#   K'_Q h(u) = sum_{m in N, m>=2} 1/m 1[P+(m) m < u] 1[u/m >= X0] h(u/m)
#   K_pt h(u) = sum_{w in NN, w>=2} 1/w 1[tau_w w < u] 1[u/w >= X0m] h(u/w)
import math, bisect, random
from fractions import Fraction


def sieve_spf(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


class Toy:
    def __init__(self, X0, kappa, H, LIM):
        self.X0, self.k, self.H, self.LIM = X0, kappa, H, LIM
        self.X0m = X0 - H / 2.0
        self.spf = sieve_spf(LIM)
        spf = self.spf
        self.primes = [p for p in range(2, LIM + 1) if spf[p] == p]
        self.large_rat = [p for p in self.primes if p >= X0]
        self.Lam = math.log(X0)
        # Moebius and P+ up to LIM
        mu = [0] * (LIM + 1)
        Pp = [1] * (LIM + 1)
        mu[1] = 1
        for n in range(2, LIM + 1):
            p = spf[n]
            m = n // p
            mu[n] = 0 if m % p == 0 else -mu[m]
            Pp[n] = max(Pp[m], p)
        self.mu, self.Pp = mu, Pp
        # X0-smooth integers up to LIM
        self.smooth = [n for n in range(1, LIM + 1) if Pp[n] < X0]
        # edge constant: sup over q in edge of MA[P](q)
        self.Me = self.edge_sup()

    def factor(self, n):
        f = []
        while n > 1:
            p = self.spf[n]
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f.append((p, e))
        return f

    def npr(self, lo, hi):
        """number of rational primes in [lo, hi] (real bounds, closed)."""
        a = bisect.bisect_left(self.primes, math.ceil(lo - 1e-12))
        b = bisect.bisect_right(self.primes, math.floor(hi + 1e-12))
        return max(0, b - a)

    def in_edge(self, q):
        return self.X0 / (1 + self.k) < q < self.X0

    def MA_lo(self, q, lo):
        """MA_{kq}[rational primes >= lo](q) = #{p in [max(q,lo),(1+k)q]}/(k q)."""
        return self.npr(max(q, lo), (1 + self.k) * q) / (self.k * q)

    def edge_sup(self):
        # MA[P](q) on the edge: #{p in [X0,(1+k)q]}/(kq); sup attained at q with (1+k)q a prime, from below
        best = 0.0
        X0, k = self.X0, self.k
        for p in self.primes:
            if p < X0:
                continue
            if p > (1 + k) * X0:
                break
            q = p / (1 + k)
            if X0 / (1 + k) < q < X0:
                best = max(best, self.npr(X0, p) / (k * q))
        # also the left limit at q -> X0
        best = max(best, self.npr(X0, (1 + k) * X0 - 1e-9) / (k * X0))
        return best

    # ---------- mu_edge ----------
    def mu_edge(self, v):
        X0, k = self.X0, self.k
        s = 0.0
        Mlo = max(2, int(v / X0) + 1)
        Mhi = int((1 + k) * v / X0) + 1
        for M in range(Mlo, Mhi + 1):
            q = v / M
            if not self.in_edge(q):
                continue
            lo = max(self.Pp[M], X0)
            s += self.MA_lo(q, lo) / M
        return s

    # ---------- rational chi (Lemma M, t = value) ----------
    def chi_rat(self, n, x):
        f = self.factor(n)
        if any(e > 1 for _, e in f):
            return 0
        ps = sorted((p for p, _ in f), reverse=True)
        prod = 1
        for p in ps:
            prod *= p
            if not (p * prod < x):
                return 0
        return 1

    def g_direct(self, v):
        """g(v) = sum_n c^Q_n(v) mu_edge(v/n)/n, c^Q_n = mu(n) chi_v(n) 1[v/n >= X0] (Lemma M, rational)."""
        X0, k = self.X0, self.k
        s = 0.0
        nmax = int((1 + k) * v / (2 * X0)) + 1
        for n in range(1, nmax + 1):
            if self.mu[n] == 0 or v / n < X0:
                continue
            if not self.chi_rat(n, v):
                continue
            me = self.mu_edge(v / n)
            if me:
                s += self.mu[n] * me / n
        return s

    # ---------- g by the N-term coefficient formula (paper (d)(iii)) ----------
    def chi_ell(self, ell_primes, v):
        """ell_primes sorted descending, squarefree; condition r * prod_{q>=r} q < v."""
        prod = 1
        for r in ell_primes:
            prod *= r
            if not (r * prod < v):
                return 0
        return 1

    def Nterm(self, N, v):
        X0, k = self.X0, self.k
        q = v / N
        if not self.in_edge(q):
            return 0.0
        if self.mu[N] == 0:
            return 0.0
        f = sorted((p for p, _ in self.factor(N)), reverse=True)
        a = bisect.bisect_left(self.primes, X0)
        b = bisect.bisect_right(self.primes, math.floor((1 + k) * q + 1e-12))
        cnt = 0
        for p in self.primes[a:b]:
            ell = [r for r in f if r > p]
            s_gt1 = len(ell) < len(f)  # s > 1 iff some prime of N is <= p
            if s_gt1 and self.chi_ell(ell, v):
                cnt += 1
        return -self.mu[N] * cnt / (k * v)

    def g_formula(self, v):
        X0, k = self.X0, self.k
        s = 0.0
        Nlo = max(2, int(v / X0) + 1)
        Nhi = int((1 + k) * v / X0) + 1
        for N in range(Nlo, Nhi + 1):
            s += self.Nterm(N, v)
        return s


class System:
    """A prime system: rational primes < X0 plus large primes given as (value, slot)."""

    def __init__(self, toy, large):
        self.toy = toy
        self.large = sorted(large)  # list of (value, slot)
        self.vals = [v for v, _ in self.large]

    def elements_with_large(self, W):
        """all elements w = d * P_1...P_r (r>=1, multiset, value <= W).
        returns list of (value, d, idx_tuple, tau) sorted by value. tau = max slot (slots >= X0 > P+(d))."""
        toy = self.toy
        out = []
        vals = self.vals
        L = self.large
        sm = toy.smooth

        def rec(start, prod, idxs, tau):
            # extend with large index >= start (non-decreasing indices -> multiset)
            for i in range(start, len(vals)):
                P = vals[i]
                np_ = prod * P
                if np_ > W:
                    break
                nidx = idxs + (i,)
                ntau = max(tau, L[i][1])
                # times smooth d
                dmax = W / np_
                j = bisect.bisect_right(sm, dmax)
                for d in sm[:j]:
                    out.append((d * np_, d, nidx, ntau))
                rec(i, np_, nidx, ntau)

        rec(0, 1.0, (), 0.0)
        out.sort()
        return out

    def c_lemmaM(self, el, x):
        """c_n(x) = mu(n) chi^t_x(n) 1[x/n >= X0m] for element el=(value,d,idx,tau)."""
        toy = self.toy
        value, d, idx, tau = el
        if x / value < toy.X0m:
            return 0
        if len(set(idx)) < len(idx):
            return 0
        fd = toy.factor(d)
        if any(e > 1 for _, e in fd):
            return 0
        pr = [(p, p) for p, _ in fd] + [self.large[i][::-1] for i in idx]  # (t, value)
        pr.sort(reverse=True)
        prod = 1.0
        for t, val in pr:
            prod *= val
            if not (t * prod < x):
                return 0
        return (-1) ** (len(pr))
