# Analytic Theorem 4.17 (Lambda-uniform): gamma(s), s = loglog z - 2 log Lambda. Sanity checks against the precise model.
import math, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import capl_model
from capl_model import *
L0 = 1e8
def A_of(lam, s):
    l = 2*math.log(lam) + s
    return math.log(2) + 3*math.log(lam) + 2*s - math.log(l)
def G(lam, s):
    A = A_of(lam, s)
    return 2*math.sqrt(A*(A+1))*math.exp(s/2)/math.sqrt(lam - A - 1)
def gstar(s): return 1.3*G(max(L0, math.exp(-s)), s)
# s_H: gstar(s_H) = 1/3 - 1e-5
lo, hi = 0.0, 10.0
for _ in range(100):
    mid = (lo+hi)/2
    if gstar(mid) <= 1/3 - 1e-5: lo = mid
    else: hi = mid
sH = lo
GMAX = 7.5
def gamma(s):
    if s <= sH: return gstar(s)
    if s <= sH + 1: return gstar(sH) + (GMAX - gstar(sH))*(s - sH)
    return GMAX
print(f"s_H = {sH:.4f}, gstar(s_H) = {gstar(sH):.5f}; at Lambda=1e8 this is loglog z = {sH + 2*math.log(L0):.3f}")
# monotonicity of G in Lambda at fixed s
for s in (-15, -5, 0, 3, 5.9):
    vals = [G(lam, s) for lam in (1e8, 1e9, 1e10, 1e12, 1e16, 1e24, 1e40)]
    print(f"s={s}: G(Lam,s) for Lam=1e8..1e40:", ["%.3e" % v for v in vals], "decreasing" if all(a >= b for a, b in zip(vals, vals[1:])) else "NOT decreasing")
# cross-check with precise model at several Lambda: precise criteria with c = max(std, gamma(s)*Lam)
def check(lam, s_lo, s_hi, h):
    capl_model.LAM = lam
    fails = 0; n = 0
    s = s_lo
    while s < s_hi:
        l = 2*math.log(lam) + s
        logc = max(4*l*l - math.log(4), gamma(s)*lam)
        okC = (l <= 700 and routeH_ok(logc, l, l, lam)) or dickman_ok(logc, l, l, lam)
        okP = lemmaP_ok(logc, l, l, lam)
        if not (okC and okP): fails += 1
        n += 1; s += h
    return n, fails
for lam in (1e8, 1e9, 1e10, 1e12, 1e16, 1e20):
    n, f = check(lam, -math.log(lam) + 0.01, 30.0, 0.01)
    print(f"Lambda={lam:.0e}: precise-model check on s in [-log Lam, 30]: {n} points, {f} failures")
