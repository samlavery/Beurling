# Independent check of the one-variable inequalities of bs-cert (paper 04c (ii) "Positivity of c(u)" and
# 04a Lemma smooth-v "one-step inequality"), from the paper text only. Ball arithmetic; cells cover the ranges.
import sys, time, math
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from flint import arb, ctx
import dick
from dick import rlow, rup, lo, hi
ctx.prec = 80
t0 = time.time()
dick.build()
print('tables built %.1f s' % (time.time() - t0))
# sanity: enclosures vs known values r(3)=2.1043, r(4)=2.4745, r(5)=2.7689 (from rho(2..5))
for v, rv in ((3, 2.1043), (4, 2.4745), (5, 2.7689)):
    assert rlow(v) <= rv <= rup(v), (v, rlow(v), rup(v))
for v in (2.5, 10, 100, 1000, 10 ** 4, 10 ** 5, 4 * 10 ** 5, 10 ** 6):
    print('  r(%g) in [%s, %s]' % (v, rlow(v).str(6), rup(v).str(6)))
print('  r_up(100) via R4 =', rup(100.0).str(5), '(paper: 7.66)')

def cells(a, b, rel, minw):
    x = a
    while x < b:
        y = min(b, x + max(minw, rel * x))
        yield x, y
        x = y

# (i) c_0(u)/(K'u^2) - log(1+u) >= 0 on [27, 4e5]:
#  F = 5 L1 [3(1-1/r(u)) - (1+u)^3 L2/(u^3 L1) - 144 (1+u)^2 L2/(u^3 r0^2 L1)] - 2 r(u-1) - (u+1)/u^2 - L1
def F_c0(a, b):
    u = arb(a).union(arb(b))
    L1 = (1 + u).log(); L2 = (2 + u).log()
    ru = rlow(a); r0 = rlow(a - 1); r0up = rup(b - 1)
    br = 3 * (1 - 1 / ru) - (1 + u) ** 3 * L2 / (u ** 3 * L1) - 144 * (1 + u) ** 2 * L2 / (u ** 3 * r0 ** 2 * L1)
    return 5 * L1 * br - 2 * r0up - (u + 1) / u ** 2 - L1

def run(name, a, b, f, rel, minw):
    n = 0; fails = 0; mn = None; stack = list(cells(a, b, rel, minw))[::-1]
    while stack:
        x, y = stack.pop(); n += 1
        v = f(x, y)
        if not (v > 0):
            if y - x < 1e-9: fails += 1; print('FAIL', name, x, y, v); continue
            m = 0.5 * (x + y); stack += [(m, y), (x, m)]; continue
        if mn is None or v.lower() < mn[0]: mn = (v.lower(), x, y)
    print('%s: cells=%d fails=%d min certified value=%s on [%g,%g]' % (name, n, fails, mn[0].str(5), mn[1], mn[2]))
    return mn

run('c_0/(K\'u^2) - log(1+u) on [27,4e5]', 27.0, 4e5, F_c0, 1e-3, 0.01)
def F_c0_ratio(a, b):   # same, relative to log(1+u) (in case the script's "margin" is a ratio)
    u = arb(a).union(arb(b))
    return F_c0(a, b) / (1 + u).log()
run('(c_0/(K\'u^2) - log(1+u)) / log(1+u) on [27,4e5]', 27.0, 4e5, F_c0_ratio, 1e-3, 0.01)

# (ii) Lemma V one-step: L(1-e^{-alpha}) E - 2 K_M r(u) - 15 e^{-0.4 L} > 0 on [1, 1e6], L = max(100, u),
#  alpha = 4K(log(u+1) + (u-1)/(u+1))/L, E = max(1/2, 1 - 1/r(u-1)) (the second only for u >= 2), K=3.2, K_M=1.01.
#  L(1-e^{-c/L}) increases in L and in c; c and L are nondecreasing in u: lower bound at u = a.
K = arb('3.2'); KM = arb('1.01')
def F_V(a, b, extra=False):
    A = arb(a); L = arb(max(100.0, a))
    c = 4 * K * ((A + 1).log() + (A - 1) / (A + 1))
    main = L * (-(-c / L).expm1())
    E = arb('0.5')
    if a > 2:
        e2 = 1 - 1 / rlow(a - 1)
        if e2 > E: E = e2
    rU = rup(b)                    # exact formula when b <= 2
    val = main * E - 2 * KM * rU
    if not extra:
        return val - 15 * (arb('-0.4') * L).exp()
    # (iii) on [1,2]: with X(u) and 22 e^{-0.4L} and the allowance 2 K_M r(u)(e^{0.141}-1); L = 100 here
    val = val - 22 * (arb('-0.4') * L).exp() - 2 * KM * rU * (arb('0.141').exp() - 1)
    thr = 1 + arb(72).log() / 100
    if a < thr.upper():
        B = arb(b)
        val = val - arb('0.7627') / (arb('0.70') * (1 - B.log()) * B)   # u(1-log u) decreasing on [1, e]
    return val
run('Lemma V one-step [1,1e6]', 1.0, 1e6, F_V, 1e-3, 1e-3)
run('Lemma V one-step [1,2] with X(u), 22e^{-0.4L} and allowance', 1.0, 2.0, lambda a, b: F_V(a, b, True), 1e-3, 1e-3)
print('runtime %.1f s' % (time.time() - t0))
