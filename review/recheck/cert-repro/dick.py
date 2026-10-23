# Rigorous enclosures of the Dickman ratio r(v) = -rho'(v)/rho(v), written from the paper's (R1)-(R4) only.
#  * exact on (1,2]: r(v) = 1/(v (1 - log v)); r increasing on (1, oo)  (R2)
#  * lower: r(v) >= g(r(v-1)), g(x) = x/(1-e^{-x}) increasing  (R3); tables on a dyadic grid, monotonicity between
#  * upper: r(x) <= log((x+1-delta)/delta)/(1-delta) for 0 < delta <= min(x,1)  (R4, in the slightly sharper form
#    with x+1-delta in place of x+1; see the derivation in R4: v rho(v) >= delta rho(v-1+delta), v = x+1-delta)
import math
from fractions import Fraction
from flint import arb, ctx

def lo(x):  return x.lower()
def hi(x):  return x.upper()
def pos(x):
    """(x)_+ as a ball"""
    if x.lower() >= 0: return x
    if x.upper() <= 0: return arb(0)
    return arb(0).union(x.upper())
def hull(a, b):  return a.union(b)
def g(x):   return x / (-(-x).expm1())

FINE = 256           # grid step 1/256 on [1, FINE_TOP]
FINE_TOP = 1100
_fine = None; _coarse = None; _ctop = None

def build(top=10 ** 6 + 5):
    global _fine, _coarse, _ctop
    saved = ctx.prec; ctx.prec = 80
    n = (FINE_TOP - 1) * FINE
    T = [None] * (n + 1)
    T[0] = arb(1)                                  # r(v) > r(1+) = 1 for v > 1
    for i in range(1, n + 1):
        if i <= FINE:                              # v = 1 + i/FINE in (1, 2]: exact formula, lower endpoint
            v = 1 + arb(i) / FINE
            T[i] = lo(1 / (v * (1 - v.log())))
        else:
            T[i] = lo(g(T[i - FINE]))
    C = [arb(0), arb(1), T[FINE]]                  # integer grid: C[k] <= r(k)
    for k in range(3, top + 1): C.append(lo(g(C[-1])))
    _fine, _coarse, _ctop = T, C, top
    ctx.prec = saved

def rlow(v):
    """an exact arb <= r(w) for every w >= v (v > 1, v a float or Fraction)"""
    v = Fraction(v)
    assert v > 1
    k = math.floor(v)
    if v < FINE_TOP:
        i = math.floor((v - 1) * FINE)
        a = _fine[i]
        if k >= 2 and _coarse[k] > a: a = _coarse[k]   # both are valid lower bounds at points <= v; r is increasing
        return a
    assert k <= _ctop
    return _coarse[k]

def r_exact12(x):
    x = arb(x)
    return 1 / (x * (1 - x.log()))

def rup(x):
    """an arb >= r(w) for every w <= x (x >= 1 float)"""
    if x <= 2:
        return hi(r_exact12(arb(x)))
    f = lambda d: math.log((x + 1 - d) / d) / (1 - d)
    a, b = 1e-9, 0.999
    for _ in range(80):                            # golden section on a convex-ish function
        m1 = a + 0.382 * (b - a); m2 = a + 0.618 * (b - a)
        if f(m1) < f(m2): b = m2
        else: a = m1
    d = arb(0.5 * (a + b))                         # exact double, 0 < d < 1 <= x
    X = arb(x)
    return hi(((X + 1 - d) / d).log() / (1 - d))

def renc(a, b):
    """ball containing r(u) for all u in [a, b], 1 < a"""
    return hull(rlow(a), rup(b))
