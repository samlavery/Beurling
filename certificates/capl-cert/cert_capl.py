# Numerical cross-check for Theorem caplw (Section 6 of the paper): for every cell [l1, l2] of a partition of [log Lam, l_T], with
# gamma(l) := log c_ramp / Lam piecewise linear and non-decreasing, c(l) := max(H_std^{1/2}/4, c_ramp(l)):
#  (C1) counting criterion holds (high-degree rows, Step 2, or Dickman rows, Step 3) with c = c(l1) at worst corners;
#  (C2) A empty or Lemma lemmaP, criterion (eq:twelvetwo), holds with c = c(l2) at worst corners;
#  (C3) ramp slope 2*Lam*dgamma/dL <= 1e-6.
import math, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from capl_model import *
KNOTS = [(18.0, 0.0), (24.0, 0.0), (26.0, 0.00006), (28.0, 0.00025), (30.0, 0.0008), (32.0, 0.0022), (34.0, 0.006),
         (36.0, 0.015), (38.0, 0.034), (40.0, 0.08), (41.0, 0.125), (42.0, 0.20), (42.3, 0.24), (43.3, 5.95)]
GMAX = 5.95
def gamma(l):
    if l >= KNOTS[-1][0]: return GMAX
    for (a, ga), (b, gb) in zip(KNOTS, KNOTS[1:]):
        if a <= l <= b: return ga + (gb - ga)*(l - a)/(b - a)
    return 0.0
def logc_of(l):
    return max(4*l*l - math.log(4), gamma(l)*LAM)
def cert(l_start, l_end, h):
    fails = []; maxslope = 0.0; n = 0
    l1 = l_start
    while l1 < l_end:
        l2 = min(l1 + h(l1), l_end)
        c1, c2 = logc_of(l1), logc_of(l2)
        ok1 = (l2 <= 60 and highdeg_ok(c1, l2, l1)) or dickman_ok(c1, l2, l1)
        ok2 = lemmaP_ok(c2, l2, l1)
        if not (ok1 and ok2): fails.append((l1, l2, ok1, ok2))
        if l2 < 700:
            dL = math.exp(l2) - math.exp(l1)
            slope = 2*(c2 - c1)/dL
            maxslope = max(maxslope, slope)
        n += 1; l1 = l2
    return n, fails, maxslope
lstart = math.log(LAM)
n, fails, ms = cert(lstart, 60.0, lambda l: 0.002)
print(f"cells {n} on [{lstart:.3f}, 60]: failures {len(fails)}; max slope dlogH/dL = {ms:.2e}")
for f in fails[:10]: print("  FAIL", f)
n2, fails2, ms2 = cert(60.0, 2.0e4, lambda l: 0.05)
print(f"cells {n2} on [60, 2e4]: failures {len(fails2)}; max slope = {ms2:.2e}")
for f in fails2[:10]: print("  FAIL", f)
print("gamma at knots:", [(a, round(gamma(a), 4)) for a, _ in KNOTS])
print("std overtakes ramp at l =", math.sqrt((GMAX*LAM + math.log(4))/4))
