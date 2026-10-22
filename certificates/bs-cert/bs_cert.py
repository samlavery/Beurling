# Closed-form lower bound S(l,u) <= Sigma(l,u) for Lemma BS, canonical regime tau >= 1e8, l1 = 30 tau
# (gap-localPNT §6.9.3′(H⁗)).  Works with plain floats or with the Interval class below (outward rounding).
# Uses only: (R1) exact identities, (R2) log-concavity, r_low (R3 recursion), r_up (R4), and elementary bounds.
import math
B, KP, KMIN, S1 = 11.0, 2.20, 4.0e8, 60.0
# ---------- outward-rounded interval arithmetic ----------
def _dn(x, k=1):
    for _ in range(k): x = math.nextafter(x, -math.inf)
    return x
def _up(x, k=1):
    for _ in range(k): x = math.nextafter(x, math.inf)
    return x
class I:
    __slots__ = ("lo", "hi")
    def __init__(s, lo, hi=None):
        if hi is None: hi = lo
        s.lo, s.hi = float(lo), float(hi)
    def __add__(s, o):
        o = o if isinstance(o, I) else I(o); return I(_dn(s.lo + o.lo), _up(s.hi + o.hi))
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o):
        o = o if isinstance(o, I) else I(o); return I(_dn(s.lo - o.hi), _up(s.hi - o.lo))
    def __rsub__(s, o): return I(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        p = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(_dn(min(p)), _up(max(p)))
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0, "division by interval containing 0"
        p = [s.lo / o.lo, s.lo / o.hi, s.hi / o.lo, s.hi / o.hi]
        return I(_dn(min(p)), _up(max(p)))
    def __rtruediv__(s, o): return I(o) / s
    def __repr__(s): return f"[{s.lo:.6g},{s.hi:.6g}]"
# monotone elementary functions; libm assumed accurate to < 1 ulp, we widen by 2 ulps
def iexp(x): return I(_dn(math.exp(x.lo), 2), _up(math.exp(x.hi), 2)) if isinstance(x, I) else math.exp(x)
def iexpm1(x): return I(_dn(math.expm1(x.lo), 2), _up(math.expm1(x.hi), 2)) if isinstance(x, I) else math.expm1(x)
def ilog(x): return I(_dn(math.log(x.lo), 2), _up(math.log(x.hi), 2)) if isinstance(x, I) else math.log(x)
def isqrt(x): return I(_dn(math.sqrt(x.lo), 2), _up(math.sqrt(x.hi), 2)) if isinstance(x, I) else math.sqrt(x)
def ipos(x): return I(max(x.lo, 0.0), max(x.hi, 0.0)) if isinstance(x, I) else max(x, 0.0)
def isq(x):
    if not isinstance(x, I): return x * x
    lo, hi = x.lo, x.hi
    if lo >= 0: return I(_dn(lo * lo), _up(hi * hi))
    if hi <= 0: return I(_dn(hi * hi), _up(lo * lo))
    return I(0.0, _up(max(lo * lo, hi * hi)))
def lo_(x): return x.lo if isinstance(x, I) else x
def hi_(x): return x.hi if isinstance(x, I) else x
# ---------- r bounds ----------
NR = 400000
_rl = [0.0] * (NR + 1)
# r(2) = 1/(2 - 2 log 2), rounded down; recursion r(v) >= g(r(v-1)), g(r) = r/(1 - e^{-r}) increasing,
# evaluated with directed rounding (denominator rounded up, quotient rounded down) => a certified lower bound.
_rl[2] = _dn(1.0 / _up(2.0 - _dn(2.0 * _dn(math.log(2.0), 2)), 1), 1)
for v in range(3, NR + 1):
    r = _rl[v - 1]; _rl[v] = _dn(r / _up(-math.expm1(-r), 2), 1)
def r_low(x):  # rigorous lower bound for r on [x, inf), x >= 1
    if x < 2: return 1.0 / (x * (1 - math.log(x))) * (1 - 1e-12) if x >= 1 else 0.0  # exact on [1,2], increasing
    return _rl[min(int(math.floor(x)), NR)]
def r_up(x):   # rigorous upper bound for r on (1, x], via (R4) with the best of a few deltas (+ exact on [1,2])
    if x <= 2: return 1.0 / (x * (1 - math.log(x))) * (1 + 1e-12)
    return min(math.log((x + 1) / d) / (1 - d) for d in (0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5)) * (1 + 1e-12)
def r_enc(ua, ub):  # enclosure of r(u) for u in [ua, ub]
    return I(r_low(ua), r_up(ub))
# ---------- the bound ----------
def Ubar(l): return l ** 0.25 * (1 + math.sqrt(2 * math.log(l / 1e8) + 4))
def S_cell(la, lb, ua, ub, vmode=False):
    """Rigorous lower bound for Sigma over l in [la,lb] and u in [ua,ub] (u-mode, 2 <= ua),
    or u = u0(l) + v, v in [ua,ub] (v-mode; removes the u - u0 dependency near the onset),
    valid for every tau >= 1e8 with l >= 30 tau."""
    l = I(la, lb)
    Ub = _up(Ubar(lb), 4)                     # >= U(l; tau) for all l in cell, tau >= 1e8
    u0 = I(_dn(la ** 0.25, 2), _up(lb ** 0.25, 2))
    if vmode:
        dv = I(ua, ub); u = u0 + dv
        if lo_(u) < 2: return -math.inf, "u<2 in v-cell"
        ua, ub = lo_(u), hi_(u)
    else:
        u = I(ua, ub); dv = u - u0
    q4 = isqrt(isqrt(l))                      # l^{1/4}
    sl = isqrt(l)
    r = r_enc(ua, ub); r0 = r_enc(ua - 1, ub - 1)
    cu = u0 / (3 * u); ku = 1 + 1 / (2 * (u - 1))
    L1u, L2u = ilog(1 + u), ilog(2 + u)
    A = B * (1 + u) * (1 + u) * (1 + u) * L2u / l
    betaA = A / u
    alphaA = (B / l) * (u * u * u) * (3 * u - 4) * L1u / isq(u - 1)
    dpos = ipos(dv)
    # (x+c)_+^2 - x_+^2 <= c(2x_+ + c), and = 0 when x + c <= 0
    shift = I(0.0) if hi_(dv + cu) <= 0 else cu * (2 * dpos + cu) / (2 * sl)
    betaa = (ku - 1) * isq(ipos(dv + cu)) / (2 * sl) + shift
    alphaa = ku * ipos(dv - 1 + cu) / sl
    betaI = betaA + betaa - KMIN / (u * l)
    betaII = betaA + betaa
    alpha = alphaA + alphaa
    w1 = u + S1
    gam1 = (B / l) * 8 * isq(1 + w1) * ilog(2 + w1) + ku * ipos(dv + S1 + cu) / sl
    UbMu0 = q4 * isqrt(2 * ilog(l / 1e8) + 4)   # Ubar(l) - u0(l), exact form
    gmax = (B / l) * 8 * (1 + Ub) ** 2 * math.log(2 + Ub) * (1 + 1e-12) + ku * ipos(UbMu0 + cu) / sl
    if lo_(r0) <= hi_(gmax): return -math.inf, "r0<=gamma_max"
    if lo_(r0) <= hi_(gam1): return -math.inf, "r0<=gamma_1"   # explicit (referee B §21); never binds on the domain
    ur = u * r
    tailII = gam1 / (r0 * (r0 - gam1)) + iexp(-(r0 - gmax) * S1) / (r0 - gmax)
    Mm1 = iexpm1(betaI) * (1 - 1 / ur) + iexpm1(betaII) / ur - iexp(betaI) * (-iexpm1(-alpha)) * (1 - 1 / r) \
          + iexp(betaII) / u * tailII
    E1 = 2 * KP * u * u * r0 * iexp(betaI - alpha) / l
    E2 = (KP / l) * (u / (u - 1)) * (iexp(betaI) * (u - 1) + iexp(betaII) * (1 / (r0 - gam1) + iexp(-(r0 - gmax) * S1) / (r0 - gmax)))
    kmax = 4 * l / 30 + 1500
    def eta(w, dw):
        d = ipos(dw + cu)
        A0 = B * (1 + w) * (1 + w) * (1 + w) * ilog(2 + w) / l
        phi = isq(d) / (2 * sl)
        return 4 * kmax / (l * l) + 4 * A0 / l + d / (4 * (l / 2) * isqrt(isqrt(l / 2))) + ku * phi / l \
               + (isq(1 + w) / l) * (2 * B * isq(1 + w) * (3 * ilog(2 + w) + 1) / l + 1.4142135623730951 * (1 + 1e-15) * d / sl)
    E3 = 2 * KP * (eta(u, dv) * iexp(betaI) + iexp(betaII) / u * (eta(w1, dv + S1) / (r0 - gam1) + eta(I(Ub), UbMu0) * iexp(-(r0 - gmax) * S1) / (r0 - gmax)))
    # tail T (Lemma V), tau-free form
    us = Ub + 0.5
    aV = 12.8 * us * us * math.log(us + 2) / la * (1 + 1e-12)
    U30mu0 = q4 * (math.sqrt(2 * math.log(30) + 4) * (1 + 1e-15))   # U_30(l) - u0(l)
    a_lu = isq(dpos) / (2 * sl)
    rr0 = r_low(ua - 1)
    # E_T = max over admissible y of [y - a(l,u) - r(u-1)(U_y - u + 3/2)]:
    #   u <= U30: log30 - a - r0 (U30 - u + 3/2);   u >= U30: -2 - 1.5 r0.
    gap = U30mu0 - dv                        # U30 - u
    E1f = hi_(math.log(30) - a_lu - rr0 * (ipos(gap) + 1.5))
    if lo_(gap) >= 0: ET = E1f
    elif hi_(gap) <= 0: ET = -2 - 1.5 * rr0
    else: ET = max(E1f, -2 - 1.5 * rr0)
    T = math.exp(min(hi_(kmax / l) + aV + ET, 700)) * (1 + 1e-12)
    tot = Mm1 + E1 + E2 + E3 + T
    return -hi_(tot), dict(Mm1=hi_(Mm1), E1=hi_(E1), E2=hi_(E2), E3=hi_(E3), T=T)
