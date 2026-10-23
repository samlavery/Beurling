# T4: |D_val(u)| (value-order part of (K'_Q - K_pt) g) against the Step-3 telescoping bounds, toy-scaled.
#  (a) actual |D_val(u)|                         [value order in both systems: what Step 3 telescopes]
#  (b) sum over replacements of the exact Abel bound with the global Delta_theta
#  (c) sum over replacements of the paper-form bound with measured constants:
#        (C_D/m_j)[2 Ginf log b + Ginf((log^2 b - log^2 a)/2 + log(b/a)) + log b * T1 (log(b/a)+1)]
#      C_D = sup_{t<=u}|Delta_theta(t)|/(t log^2 t), Ginf = sup|g|, T1 = (3.1/1.0001) Me  (TV(g) bound of (d)(iii))
#  (d) the closed form  c_rep(u) * Dsum * (1+l)e^l,  c_rep with b<=u, log(b/a)<=log u  (paper's last step)
import sys, math, random, bisect, json
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from t3_realised import Model


class Bounds:
    def __init__(self, M):
        self.M = M
        toy = M.toy
        self.toy = toy
        self.A = sorted(M.real.vals)            # realised large primes (values)
        self.B = [float(p) for p in toy.large_rat if p <= M.Wmax + 10]
        # global theta-difference at merged points
        pts = sorted([(v, 0) for v in self.A] + [(v, 1) for v in self.B])
        self.pts = [v for v, _ in pts]
        acc = 0.0
        self.Dth = []  # Delta_theta(t) right-continuous, at each merged point
        for v, s in pts:
            acc += math.log(v) if s == 0 else -math.log(v)
            self.Dth.append(acc)
        # C_D(u) prefix sup of |Dth|/(t log^2 t)
        self.CD = []
        m = 0.0
        for v, dt in zip(self.pts, self.Dth):
            m = max(m, abs(dt) / (v * math.log(v) ** 2))
            self.CD.append(m)
        self.T1 = (3.1 / 1.0001) * toy.Me
        # Dsum over all X0-smooth d (Euler product over p < X0)
        self.Dsum = 1.0
        for p in toy.primes:
            if p >= toy.X0:
                break
            self.Dsum /= (1 - 1 / p)

    def C_D(self, u):
        j = bisect.bisect_right(self.pts, u)
        return self.CD[j - 1] if j else 0.0

    def Dth_at(self, t, left=False):
        j = (bisect.bisect_left if left else bisect.bisect_right)(self.pts, t)
        return self.Dth[j - 1] if j else 0.0

    def abel(self, phi, a, b):
        """exact Abel bound for sum_{t in [a,b]} phi(t) (dpi_A - dpi_B)(t), with the global Delta_theta;
        also returns the actual value."""
        i0 = bisect.bisect_left(self.pts, a)
        i1 = bisect.bisect_right(self.pts, b)
        if i1 <= i0:
            return 0.0, 0.0
        ts = self.pts[i0:i1]
        psi = [phi(t) / math.log(t) for t in ts]
        Dt = self.Dth[i0:i1]
        Dleft = self.Dth[i0 - 1] if i0 > 0 else 0.0
        val = 0.0
        prev = Dleft
        for p_, d_ in zip(psi, Dt):
            val += p_ * (d_ - prev)
            prev = d_
        bnd = abs(psi[-1] * Dt[-1]) + abs(psi[0] * Dleft)
        for i in range(len(ts) - 1):
            bnd += abs(Dt[i]) * abs(psi[i + 1] - psi[i])
        return val, bnd

    def paper_rep(self, u, mj, a, b, Ginf):
        CD = self.C_D(u)
        lb, la = math.log(b), math.log(a)
        return CD / mj * (2 * Ginf * lb + Ginf * ((lb * lb - la * la) / 2 + (lb - la)) + lb * self.T1 * ((lb - la) + 1))

    def run_u(self, u, Ginf):
        M, toy = self.M, self.toy
        g = M.g
        X0m = toy.X0m
        W = (1 + M.kappa) * u / (2 * toy.X0)
        res = dict(u=u, val2=0.0, abel2=0.0, paper2=0.0, val3=0.0, abel3=0.0, paper3=0.0)
        for d in toy.smooth:
            if d * X0m > W:
                break
            # k = 2: cofactor d p, p large; filter p * d p < u
            b = min(math.sqrt(u / d), W / d)
            if b >= X0m:
                phi = lambda t, d=d: g(u / (d * t)) / (d * t) if t * t * d < u else 0.0
                v, bd = self.abel(phi, X0m, b)
                res['val2'] += v
                res['abel2'] += bd
                res['paper2'] += self.paper_rep(u, d, X0m, b, Ginf)
            # k = 3: cofactor d p2 p3, p2 >= p3; ordered telescoping
            if d * X0m * X0m > W:
                continue
            # i=1: replace p2 (B -> A), p3 in B fixed
            for p3 in self.B:
                if d * p3 * p3 > W or d * p3 ** 3 >= u:
                    break
                b2 = min(math.sqrt(u / (d * p3)), W / (d * p3))
                if b2 < p3:
                    continue
                phi = lambda t, d=d, p3=p3: g(u / (d * t * p3)) / (d * t * p3) if t * t * d * p3 < u else 0.0
                v, bd = self.abel(phi, p3, b2)
                res['val3'] += v
                res['abel3'] += bd
                res['paper3'] += self.paper_rep(u, d * p3, p3, b2, Ginf)
            # i=2: replace p3 (B -> A), p2 in A fixed
            for p2 in self.A:
                if d * p2 * X0m > W:
                    break
                b3 = min(p2, u / (d * p2 * p2), W / (d * p2))
                if b3 < X0m:
                    continue
                phi = lambda t, d=d, p2=p2: g(u / (d * t * p2)) / (d * t * p2) if p2 * p2 * d * t < u else 0.0
                v, bd = self.abel(phi, X0m, b3)
                res['val3'] += v
                res['abel3'] += bd
                res['paper3'] += self.paper_rep(u, d * p2, X0m, b3, Ginf)
        # closed form (paper's last step), toy constants
        lu = math.log(u)
        CD = self.C_D(u)
        crep = CD * (2 * Ginf * lu + Ginf * (lu * lu / 2 + lu) + lu * self.T1 * (lu + 1))
        ell = max(sum(1 / p for p in self.A if p <= u), sum(1 / p for p in self.B if p <= u))
        res['closed'] = crep * self.Dsum * (1 + ell) * math.exp(ell)
        res['CD'] = CD
        res['ell'] = ell
        return res


def main():
    out = {}
    for variant, eps in [('jitter', 0.0), ('add', 0.15), ('del', 0.15), ('drift', 0.1)]:
        M = Model(100, 0.2, 2, 4.0e6, variant, eps, 7)
        Bd = Bounds(M)
        toy = M.toy
        rnd = random.Random(11)
        # Ginf: sup |g| (sampled densely + the paper-type bound Me(k + (1+k)/2))
        Ginf = toy.Me * (toy.k + (1 + toy.k) / 2)
        u0 = 2 * toy.X0 * toy.X0m / (1 + toy.k)
        us = sorted(math.exp(rnd.uniform(math.log(u0), math.log(4.0e6))) for _ in range(40))
        print(f"== {variant} eps={eps}: Ginf(bound)={Ginf:.4f} T1={Bd.T1:.4f} Dsum={Bd.Dsum:.3f}")
        worst = {'b/a': 0, 'c/b': 0, 'd/c': 0}
        rows = []
        for u in us:
            r = Bd.run_u(u, Ginf)
            Dv = M.D(u, value_order=True)
            tel = r['val2'] + r['val3']
            assert abs(tel + Dv) < 1e-12, (u, tel, Dv)
            a = abs(Dv)
            b = r['abel2'] + r['abel3']
            c = r['paper2'] + r['paper3']
            d = r['closed']
            rows.append((u, a, b, c, d, r['CD']))
            if b > 0:
                worst['b/a'] = max(worst['b/a'], a / b)
            worst['c/b'] = max(worst['c/b'], b / c if c else 0)
            worst['d/c'] = max(worst['d/c'], c / d if d else 0)
        for (u, a, b, c, d, CD) in rows[::5]:
            print(f"   u={u:10.0f} |D_val|={a:.3e}  Abel={b:.3e}  paper-form={c:.3e}  closed={d:.3e}  C_D={CD:.3e}")
        print(f"   max ratios: |D_val|/Abel={worst['b/a']:.3f}  Abel/paper-form={worst['c/b']:.3f}  paper-form/closed={worst['d/c']:.3f}")
        out[variant] = rows
    json.dump(out, open('/tmp/rhscratch/margin-var-check/out/t4.json', 'w'))


if __name__ == '__main__':
    main()
