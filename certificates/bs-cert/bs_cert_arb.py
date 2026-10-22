# Arb version of bs_cert.py (same bound S, same cells); interval layer from ivarb.py (python-flint arb balls).
import math
from flint import arb
from ivarb import I, iexp, iexpm1, ilog, isqrt, ipos, isq, lo_, hi_, _fdn, _fup
B, KP, KMIN, S1 = 11.0, 2.20, 4.0e8, 60.0
# ---------- r bounds ----------
NR = 400000
_rl = [0.0] * (NR + 1)
# r(2) = 1/(2 - 2 log 2), rounded down; recursion r(v) >= g(r(v-1)), g(r) = r/(1 - e^{-r}) increasing,
# evaluated with directed rounding (denominator rounded up, quotient rounded down) => a certified lower bound.
_rl[2] = _fdn((1 / (2 - 2 * arb(2).log())).lower())
for v in range(3, NR + 1):
    r = arb(_rl[v - 1]); _rl[v] = _fdn((r / (-(-r).expm1())).lower())
def r_low(x):  # rigorous lower bound for r on [x, inf), x >= 1
    if x < 2: return _fdn((1 / (arb(x) * (1 - arb(x).log()))).lower()) if x >= 1 else 0.0  # exact on [1,2]
    return _rl[min(int(math.floor(x)), NR)]
def r_up(x):   # rigorous upper bound for r on (1, x], via (R4) with the best of a few deltas (+ exact on [1,2])
    if x <= 2: return _fup((1 / (arb(x) * (1 - arb(x).log()))).upper())
    return min(_fup(((arb(x) + 1) / arb(d)).log().upper() / (1 - d)) * (1 + 2**-50) for d in (0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5))
def r_enc(ua, ub):  # enclosure of r(u) for u in [ua, ub]
    return I(r_low(ua), r_up(ub))
# ---------- the bound ----------
def Ubar(l): return l ** 0.25 * (1 + math.sqrt(2 * math.log(l / 1e8) + 4))      # float, for cell layout only
def Ubar_up(l):
    a = arb(l); return _fup((a.root(4) * (1 + (2 * (a / arb(10) ** 8).log() + 4).sqrt())).upper())
def S_cell(la, lb, ua, ub, vmode=False):
    """Rigorous lower bound for Sigma over l in [la,lb] and u in [ua,ub] (u-mode, 2 <= ua),
    or u = u0(l) + v, v in [ua,ub] (v-mode; removes the u - u0 dependency near the onset),
    valid for every tau >= 1e8 with l >= 30 tau."""
    l = I(la, lb)
    Ub = Ubar_up(lb)                          # >= U(l; tau) for all l in cell, tau >= 1e8
    u0 = I(arb(la).root(4), arb(lb).root(4))
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
    UbMu0 = q4 * isqrt(2 * ilog(l / arb(10) ** 8) + 4)   # Ubar(l) - u0(l), exact form
    gmax = (B / l) * 8 * isq(1 + I(Ub)) * ilog(2 + I(Ub)) + ku * ipos(UbMu0 + cu) / sl
    if lo_(r0) <= hi_(gmax): return -math.inf, "r0<=gamma_max"
    if lo_(r0) <= hi_(gam1): return -math.inf, "r0<=gamma_1"   # explicit (seam-safe, directed rounding); never binds on the domain
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
               + (isq(1 + w) / l) * (2 * B * isq(1 + w) * (3 * ilog(2 + w) + 1) / l + isqrt(2) * d / sl)
    E3 = 2 * KP * (eta(u, dv) * iexp(betaI) + iexp(betaII) / u * (eta(w1, dv + S1) / (r0 - gam1) + eta(I(Ub), UbMu0) * iexp(-(r0 - gmax) * S1) / (r0 - gmax)))
    # tail T (Lemma V), tau-free form
    us = Ub + 0.5
    aV = (arb(12.8) * arb(us) ** 2 * (arb(us) + 2).log() / la)
    U30mu0 = q4 * isqrt(2 * ilog(30) + 4)   # U_30(l) - u0(l)
    a_lu = isq(dpos) / (2 * sl)
    rr0 = r_low(ua - 1)
    # E_T = max over admissible y of [y - a(l,u) - r(u-1)(U_y - u + 3/2)]:
    #   u <= U30: log30 - a - r0 (U30 - u + 3/2);   u >= U30: -2 - 1.5 r0.
    gap = U30mu0 - dv                        # U30 - u
    E2f = _fup((-2 - arb(1.5) * arb(rr0)).upper())
    E1f = hi_(ilog(30) - a_lu - rr0 * (ipos(gap) + 1.5))
    if lo_(gap) >= 0: ET = E1f
    elif hi_(gap) <= 0: ET = E2f
    else: ET = max(E1f, E2f)
    T = _fup((arb(hi_(kmax / l)) + aV + arb(ET)).exp().upper()) if hi_(kmax / l) + float(aV.upper()) + ET < 700 else math.inf
    tot = Mm1 + E1 + E2 + E3 + I(T)
    return -hi_(tot), dict(Mm1=hi_(Mm1), E1=hi_(E1), E2=hi_(E2), E3=hi_(E3), T=T)
