# Numerical checks of the constants of Section 8 (Theorem A', Follow-up S2). Standard library only.
# Every quantity is handled in logarithms: at the scales of the zeros, ell_k >= 2*Lambda >= 2e8, so L_k = e^{ell_k} is
# not a float. The checks are elementary inequalities in ell (and in t = log ell for the floors); this script guards the
# constants quoted in the text, it is not a step of the proof.
# Usage: python3 -I -B certificates/onezero/s2_check.py
import math

LAMS = [1e8, 1e9, 1e10, 1e12, 1e16, 1e20, 1e30, 1e50, 1e70, 1e100]
fails = 0


def check(name, ok, detail=''):
    global fails
    if not ok:
        fails += 1
        print('FAIL', name, detail)


def ell_grid(lo, hi=1e300, n=4000):
    a, b = math.log(lo), math.log(hi)
    return [max(lo, math.exp(a + (b - a) * i / n)) for i in range(n + 1)]   # clamp the rounding of exp(log(lo))


for lam in LAMS:
    l1 = 2 * lam                                  # ell_k >= 2 Lambda (log x_k^+ >= X_0^2)
    # eq:thetastar: theta_k <= theta_* = 36 Lambda^2 X_0^{-2}; log theta_k = log 9 + 2 log ell - ell, decreasing for ell > 2
    log_theta_star = math.log(36) + 2 * math.log(lam) - 2 * lam
    worst = {}
    for l in ell_grid(l1):
        log_theta = math.log(9) + 2 * math.log(l) - l
        check('theta_k <= theta_*', log_theta <= log_theta_star + 1e-12, (lam, l))
        theta = math.exp(log_theta)                # underflows to 0 here: theta_k is astronomically small
        delta = 9 * l * math.exp(-l)               # delta_k = 9 ell / L
        # step 6: 2 delta_k <= theta_k  <=>  18 ell <= 9 ell^2
        check('2 delta_k <= theta_k', 18 * l <= 9 * l * l, (lam, l))
        check('Re w >= 0.49', 1 - theta - delta >= 0.49, (lam, l))
        # Lemma onezero-osc(b): 2 x^{theta_k} <= 2.01 e^{18 ell(x)^2} on (x_k^+, e y_k): theta_k (2L+1) = 18 ell^2 + theta_k
        check('R size', math.log(2) + theta <= math.log(2.01), (lam, l))
        # late noise: 171 Lambda e^{8 ell^2 - theta_k L_k} = 171 Lambda e^{-ell^2} <= 171 Lambda e^{-4 Lambda^2}
        check('late noise', -l * l <= -4 * lam * lam, (lam, l))
        # o_R: 6.2 e^{2 ell - ell^2} <= e^{-ell^2/2}
        check('o_R per k', math.log(6.2) + 2 * l - l * l <= -l * l / 2, (lam, l))
    # o_R constants: 2.04 * 1.01 * 2^2 * 3 <= 26 (with (u/2)^{theta-2} <= 4 u^{theta-2}, (x/u)^{2-theta} <= 3 x/u)
    check('o_R constant 26', 2.04 * 1.01 * 4 * 3 <= 26)
    check('o_R constant 6.2', 3 * 1.01 / 0.49 <= 6.2)
    # dyadic ratio of log^2(3u) H(u) x/u: (1 + log2/log 3u)^2 2^{4e-6} / 2 at log u >= X_0^2 / 2
    check('dyadic ratio 0.51', 0.5 * (1 + math.log(2) / lam) ** 2 * 2 ** 4e-6 <= 0.51)
    # sum over k: sum_k e^{-ell_k^2/2} <= 2 e^{-ell_1^2/2} <= e^{-Lambda^2} (ell_{k+1} >= ell_k + 1)
    check('o_R sum over k', math.log(2) - l1 * l1 / 2 <= -lam * lam)
    # Lemma onezero-osc(c): 2 kappa_0 (2 + 1/X_0^2) <= 4.01 kappa_0, and 4.01 Lambda^{-5} <= kappa_+ = 0.8
    check('R prime', 4.01 * lam ** -5 <= 0.8)
    # transform: sum_k 10 |s| x_k^{-0.4} <= |s| e^{-0.39 X_0^2}: log(10.01) - 0.4 X_0^2 <= -0.39 X_0^2 (X_0^2 = e^{2 Lambda})
    check('Rhatbound', math.log(10.01) <= 0.01 * math.exp(min(2 * lam, 700)))
    # off-term on the Rouche circle: |M_k| <= 2 Lambda e (1 + 5/log x_k) <= 5.5 Lambda; 5.5 Lambda x_k^{-0.98} <= e^{-0.49 X_0^2}
    check('M_k bound', 2 * math.e * (1 + 5 * math.exp(-min(2 * lam, 700))) <= 5.5)
    check('M_off', math.log(5.5 * lam) <= 0.49 * math.exp(min(2 * lam, 700)))
    # Rouche tally: 7 e^{-0.49 X_0^2} + 1/16 + 171 Lambda e^{-4 Lambda^2} + e^{-1e10} < 1/4
    tally = 7 * math.exp(-0.49 * math.exp(min(2 * lam, 700))) + 1 / 16 + math.exp(math.log(171 * lam) - 4 * lam * lam) \
        + math.exp(-1e10)
    check('Rouche tally', tally < 0.25, tally)
    # Lemma goodheights, R' part: 2 * 2.02 e^{-X_0^2/4} <= 4.04 e^{-X_0^2/4}, and 0.1 X_0^{-3/16} room (log scale)
    check('goodheights R part', math.log(4.04) - math.exp(min(2 * lam, 700)) / 4 <= math.log(0.1) - 3 * lam / 16)

# Remark onezero-floors: the window floor. (12.2) needs 0.9 u0 log u0 >= (16+o(1)) ell^2 with u0 = log h / (12 ell^2):
# log h = K ell^4 / log ell gives 0.9 u0 log u0 -> 0.15 K ell^2, so K > 320/3; at K = 120 the ratio tends to 1.125.
check('window floor', abs(0.15 * 120 / 16 - 1.125) < 1e-12 and 320 / 3 < 120)

# Theorem A'(i): the four terms at Lambda = 1e8, in logarithms, as functions of t = log ell. The rigid term is
# Psi(2x, X_0) <= (2 log x)^{pi(X_0)} = exp(pi(X_0)(ell + log 2)), with pi(X_0) <= 1.26 X_0/log X_0 (Rosser-Schoenfeld).
lam = 1e8
log_pi = lam + math.log(1.26) - math.log(lam)          # log pi(X_0) (upper bound)
ell_std = math.sqrt((7.5 * lam + math.log(4)) / 4)


def loglog_terms(t):
    """log of the log of each term of Theorem A'(i) at ell = e^t, ell >= ell_std, log x >= 400 Lambda^2."""
    # log(8 ell^2 + log 3.01), log(18 ell^2 + log 2.01), log(log h - 8 log Lambda), log(pi (ell + log 2))
    ell2 = 2 * t
    lag = math.log(8) + ell2
    osc = math.log(18) + ell2
    a120 = math.log(120) + 4 * t - math.log(t)
    a27 = math.log(27 * lam) + ell2
    a50 = math.log(50 * lam * lam)
    absn = max(a120, a27, a50)                        # log(log h); the factor Lambda^{-8} is dropped (upper bound)
    rigid = log_pi + t + math.log1p(math.log(2) * math.exp(-t))
    return {'lag': lag, 'osc': osc, 'absorption': absn, 'rigid': rigid}


# crossover t_x where the absorption term overtakes the rigid term: log120 + 4t - log t = log pi + t
lo, hi = math.log(ell_std), 1e9
for _ in range(200):
    mid = (lo + hi) / 2
    d = loglog_terms(mid)
    if d['absorption'] >= d['rigid']:
        hi = mid
    else:
        lo = mid
t_x = hi
print('Theorem A\'(i) at Lambda = 1e8: absorption overtakes rigid at log ell = %.6g' % t_x)
print('  (from ell^3 = pi(X_0) log ell/120: log ell = %.6g)' % ((log_pi - math.log(120) + math.log(t_x)) / 3))
for t in [math.log(ell_std), 12, 20, t_x * 0.999, t_x * 1.001, 2 * t_x, 1e3 * t_x]:
    d = loglog_terms(t)
    dom = max(d, key=d.get)
    print('  log ell = %-12.6g dominant: %-10s  loglog of terms: %s' % (t, dom, ', '.join(
        '%s %.4g' % (k, v) for k, v in d.items())))
    if t > t_x * 1.0001:
        # beyond t_x the sum of the four terms is at most 2 exp(120 ell^4/log ell): every other log-term is smaller by
        # a margin that is itself huge, so the sum is (1 + o(1)) times the absorption term
        others = max(v for k, v in d.items() if k != 'absorption')
        check('absorption dominates', d['absorption'] > others, t)
        gap = math.exp(d['absorption']) - math.exp(others) if d['absorption'] < 700 else float('inf')
        check('absorption gap', gap > math.log(4), (t, gap))

# eventual check, in t only: for log ell >= t_x, 120 ell^4/log ell exceeds each of 8 ell^2, 18 ell^2, 27 Lambda ell^2 and
# pi(X_0)(ell + log 2) (monotone differences); spot-check on a grid
for i in range(2001):
    t = t_x * (1 + 1e-4) * (1 + i * 1e-2)
    d = loglog_terms(t)
    check('eventual dominance', d['absorption'] >= max(d['lag'], d['osc'], d['rigid']), t)

print('TOTAL FAILURES:', fails)
