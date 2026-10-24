"""R25: independent check of correction #91 (truncated ramps at X_0) with arb.

Toy parameters kappa = 1/10, X_0 = 100.  The rigid ramp of n is the density
1/(kappa u) on [n/(1+kappa), n], entering T with a minus sign; for u < X_0 the
density rho_det is not defined, so ramps of n in [X_0, X_0(1+kappa)) are cut at X_0.
"""
from flint import arb, acb, ctx

ctx.prec = 200

kap = arb(1) / 10
X0 = arb(100)
one = arb(1)


def ramp_int(lo, hi, s):
    """Direct numerical value of int_lo^hi u^{-s} du/(kappa u) (no closed form used)."""
    f = lambda u, analytic: acb(u) ** (-s - 1) / kap
    return acb.integral(f, lo, hi)


def W(s):
    return ((1 + kap) ** s - 1) / (s * kap)


samples = [acb(2, 3), acb(0.5, 10), acb(1.5, -7), acb(3, 0), acb(0.75, 50),
           acb(1, 1000), acb(2, 0.5), acb(100, 0), acb(100, 5)]

print("== 1. per-n transform change ==")
worst_closed = arb(0)
for n in [arb(100), arb(105)]:
    lo = n / (1 + kap)
    for s in samples:
        full = ramp_int(lo, n, s)              # transform of the whole ramp (as + density)
        kept = ramp_int(X0, n, s)              # the part with u >= X_0, present in rho_det
        omitted = ramp_int(lo, X0, s)          # the part on [n/(1+kappa), X_0)
        # Z_B carries -kept; the formula eq:ZBformula carries -W(s) n^{-s} = -full.
        change = (-kept) - (-full)             # Z_B minus formula, for this n
        new = (lo ** (-s) - X0 ** (-s)) / (s * kap)
        old = (X0 ** (-s) - n ** (-s)) / (s * kap)
        wfull = W(s) * n ** (-s)
        sig = s.real
        bound_zb = 2 * (1 + kap) ** sig * X0 ** (-sig) / (kap * abs(s))
        bound_zblow = (one + kap).log() / kap * (X0 / (1 + kap)) ** (-sig)
        d1 = abs(change - new)
        d2 = abs(full - wfull)
        d3 = abs(omitted - new)
        d4 = abs(kept - old)
        worst_closed = max(worst_closed.upper(), max(d1, d2, d3, d4).upper())
        m = abs(new)
        print(f"n={int(float(n.mid()))} s={s.real.mid().str(5)}+{s.imag.mid().str(5)}i "
              f"|change|={m.str(6, radius=False)} |old|={abs(old).str(6, radius=False)} "
              f"ZBbnd/|chg|={(bound_zb / m).str(4, radius=False) if m > 0 else 'inf'} "
              f"ZBlowbnd/|chg|={(bound_zblow / m).str(4, radius=False) if m > 0 else 'inf'}")
        assert m <= bound_zb, "ZB modulus bound fails"
        assert m <= bound_zblow, "ZBlow modulus bound fails"
print("max |direct - closed form| over all checks:", worst_closed.str(5))

print()
print("== 1b. does the factor 2 need both terms? (real s, n = X_0) ==")
for sig in [arb('0.5'), arb(1), arb(2)]:
    s = acb(sig, 0)
    n = X0
    lo = n / (1 + kap)
    m = abs((lo ** (-s) - X0 ** (-s)) / (s * kap))
    one_term = (1 + kap) ** sig * X0 ** (-sig) / (kap * abs(s))
    print(f"sigma={sig.str(3)}: |change| / [(1+k)^s X0^-s/(k|s|)] = {(m / one_term).str(6, radius=False)}")
# worst case for the two-term bound: s with phases making the two terms add
import math
best = 0.0
for k in range(1, 4000):
    t = arb(k) / 20
    s = acb(1, t)
    n = X0
    lo = n / (1 + kap)
    m = abs((lo ** (-s) - X0 ** (-s)) / (s * kap))
    one_term = (1 + kap) ** 1 * X0 ** (-1) / (kap * abs(s))
    r = float((m / one_term).mid())
    best = max(best, r)
print(f"sigma=1, t in (0,200]: sup |change| / one-term bound = {best:.6f}  (so the constant must be > 1; 2 suffices)")

print()
print("== 1c. old ZBlow bound 3 n^-sigma at n = X_0, sigma = 10/kappa ==")
for kv in [arb(1) / 10, arb(1) / 1000, arb(1) / 10**6]:
    sig = 10 / kv
    s = acb(sig, 0)
    n = X0
    lo = n / (1 + kv)
    m = (lo ** (-sig) - X0 ** (-sig)) / (sig * kv)
    ratio = m / n ** (-sig)
    print(f"kappa={kv.str(3, radius=False)}: |change| / n^-sigma = {ratio.str(8, radius=False)}  "
          f"(e^10-1)/10 = {((arb(10).exp() - 1) / 10).str(8, radius=False)}")

print()
print("== 2. whole-set toy: Z_B piece vs eq:ZBformula + boundary terms ==")
# toy 'rigid set': the 100-smooth integers in [100, 160]; d = 100 = X_0 included
def smooth(m, B=100):
    p = 2
    while p * p <= m:
        while m % p == 0:
            m //= p
        p += 1
    return m < B
D = [d for d in range(100, 161) if smooth(d)]
print("toy D =", D)
for s in [acb(2, 3), acb(0.5, 10), acb(1, 40), acb(5, -2)]:
    # direct: -int_{X_0}^infty u^{-s} rho_det(u) du, rho_det(u) = #{d: u <= d <= (1+k)u}/(k u)
    pts = sorted(set([100.0] + [float(d) for d in D] + [float(d) / 1.1 for d in D if d / 1.1 > 100]))
    direct = acb(0)
    for a, b in zip(pts[:-1], pts[1:]):
        mid = (a + b) / 2
        cnt = sum(1 for d in D if mid <= d <= 1.1 * mid)
        if cnt:
            aa = arb(a) if a != 100.0 else X0
            # exact endpoints: d or d/(1+kappa)
            def exact(x):
                for d in D:
                    if abs(x - d) < 1e-9:
                        return arb(d)
                    if abs(x - d / 1.1) < 1e-9:
                        return arb(d) / (1 + kap)
                return arb(x)
            direct += cnt * ramp_int(exact(a), exact(b), s)
    zb_piece = sum((arb(d) ** (-s) for d in D), acb(0)) - direct
    formula = (1 - W(s)) * sum((arb(d) ** (-s) for d in D), acb(0))
    bdry = sum((((arb(d) / (1 + kap)) ** (-s) - X0 ** (-s)) / (s * kap) for d in D if arb(d) < X0 * (1 + kap)), acb(0))
    oldb = sum(((X0 ** (-s) - arb(d) ** (-s)) / (s * kap) for d in D if arb(d) < X0 * (1 + kap)), acb(0))
    print(f"s={s.str(4, radius=False)}: |ZB - (formula + new bdry)| = {abs(zb_piece - formula - bdry).str(4)}, "
          f"|ZB - (formula + old bdry)| = {abs(zb_piece - formula - oldb).str(4, radius=False)}, "
          f"|ZB - (formula - new bdry)| = {abs(zb_piece - formula + bdry).str(4, radius=False)}")
