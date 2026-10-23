# Independent re-derivation and check of region Z2 of Theorem bs (paper 04c, Step 7 (iii)):
#   Sigma(l, u) >= 0 for 30 tau <= l < 1e18, 2 <= u <= U(l), uniformly in tau >= 1e8,
# written from the paper text (Steps 2-7, (R1)-(R4)), not from the bs-cert scripts. Ball arithmetic throughout.
# The lower bound S of Sigma is my own derivation (see the notes in the report): Part I chord bounds on [u-1,u];
# Part II with a piecewise-linear majorant of D on [u, Ubar] (my breakpoints, finite upper end, no convergence
# condition needed); E1, E2, E3 bounded with the same majorants and an explicit enclosure of l*eta_f; T from Step 6.
import sys, os, time, math
from fractions import Fraction
from multiprocessing import get_context
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
import dick
from dick import rlow, rup, pos

PREC = 96
B = arb(11); KP = arb('2.2'); KV = arb('3.2'); KMIN = arb(4) * arb(10) ** 8; TAU0 = arb(10) ** 8
LOG30 = arb(30).log(); SQ30 = (2 * LOG30 + 4).sqrt()

def frac(x):                      # exact arb -> Fraction
    m, e = x.mid().man_exp(); m = int(m); e = int(e)
    return Fraction(m) * (Fraction(2) ** e)
def fdown(x):                     # Fraction <= x.lower()
    return frac(x.lower())
def fup_float(x):                 # float >= x.upper()
    q = frac(x.upper()); f = float(q)
    if Fraction(f) < q: f = math.nextafter(f, math.inf)
    return f

def hprime(w):                    # h(w) = (1+w)^4 log(2+w)/w ; h' increasing on [1, oo) (shown in the report)
    return (1 + w) ** 3 * (2 + w).log() * (3 * w - 1) / w ** 2 + (1 + w) ** 4 / (w * (2 + w))

def I_exp(c, D):                  # upper bound of int_0^D e^{ct} dt
    if c.upper() < 0:
        return (-(c * D).expm1()) / (-c)
    cu = max(arb(0), arb(c.upper()))
    return D * (cu * D).exp()
def K_texp(c, D):                 # upper bound of int_0^D t e^{ct} dt
    if c.upper() < 0:
        return 1 / (c * c)
    cu = max(arb(0), arb(c.upper()))
    return D * D / 2 * (cu * D).exp()

def l_eta(wlo, whi, l, kmax_l, Yhi):
    """upper bound of l*eta_f(m, w) for w in [wlo, whi] (1 <= wlo), m = l w/(1+w), y = (w - m^{1/4})_+ <= Yhi.
    Each factor is monotone in w (see the report), so it is evaluated at its worst endpoint; wlo, whi are exact."""
    Y = pos(Yhi)
    ml = l * wlo / (1 + wlo)                        # m is increasing in w: m >= ml
    T1 = kmax_l * (1 + 1 / wlo) ** 2                # (1+w)^2/w^2 decreasing
    Lh = (2 + whi).log()
    T2 = B * (1 + whi) ** 5 * Lh / (l * whi ** 2)   # (1+w)^5/w^2 and log(2+w) increasing (w >= 1)
    T3 = l * Y / (4 * ml ** arb('1.25')) + l * Y * Y / (4 * ml ** arb('1.5'))
    T4 = B * (1 + whi) ** 3 * (3 * (1 + whi) ** 2 * Lh + (1 + whi) ** 3 / (2 + whi)) / (l * whi)
    T5 = (1 + whi) ** 2 * Y / ml.sqrt()
    return T1 + T2 + T3 + T4 + T5

def breakpoints(stop):
    top = arb(stop.upper())
    s = [arb(0)]
    for x in ('0.125', '0.25', '0.5', '0.75', '1', '1.5', '2', '3', '4', '6', '8', '12', '16', '24', '32', '48', '64'):
        if arb(x) < top: s.append(arb(x))
    x = 64
    while True:
        x = x * 3 // 2
        if not (arb(x) < top): break
        s.append(arb(x))
    s.append(top)
    return s

def lS(la, lb, ua, ub, vmode, dbg=False):
    """lower bound (ball) of l*Sigma over the cell. vmode: (ua, ub) are v = u - u0 bounds, else u bounds."""
    ctx.prec = PREC
    l = arb(la).union(arb(lb))
    u0 = l.root(4)
    sl = l.sqrt()
    if vmode:
        v = arb(ua).union(arb(ub)); u = u0 + v
    else:
        u = arb(ua).union(arb(ub)); v = u - u0
    if vmode:
        ulo_f = fdown(u); uhi_f = fup_float(u); ulo_a = arb(u.lower())
        if ulo_f < 2: return None
    else:
        ulo_f = Fraction(ua); uhi_f = ub; ulo_a = arb(ua)    # exact cell ends (the ball u may overshoot them by rounding)
        assert ulo_f >= 2
    ru = dick.hull(rlow(ulo_f), rup(uhi_f))
    r0 = dick.hull(rlow(ulo_f - 1) if ulo_f > 2 else arb(1), rup(uhi_f - 1))
    ru_lo = arb(ru.lower()); r0_lo = arb(r0.lower())
    ku = 1 + 1 / (2 * (u - 1))
    cu = u0 / (3 * u)
    hA = (1 + u) ** 3 * (2 + u).log() / u
    # beta_a >= k_u phi(u) - a(l,u)
    t = pos(v + cu)
    ba = (ku - 1) * t * t
    if (v + cu).upper() > 0: ba = ba + cu * (2 * pos(v) + cu)
    ba = ba / (2 * sl)
    betaII = B * hA / l + ba
    betaI = betaII - KMIN / (u * l)
    # alpha: (B/l) h'(u-1) + k_u phi'(u-1), lower endpoint as a single valid value
    alpha = B * hprime(arb(u.lower()) - 1) / l + ku * pos(v - 1 + cu) / sl
    alpha = arb(alpha.lower())
    piI = arb(1).union(1 - 1 / (u * ru_lo))
    M1 = l * (betaI.expm1() * piI - betaI.exp() * (-(-alpha).expm1()) * (1 - 1 / ru_lo))
    M1I = M1
    E1 = 2 * KP * u * u * r0 * (betaI - alpha).exp()
    E2 = KP * (1 + u) * betaI.exp()
    kmax_l = arb(4) / 30 + 1500 / l
    E3 = 2 * KP * betaI.exp() * l_eta(ulo_a - 1, arb(uhi_f), l, kmax_l, arb((v + cu).upper()))
    # Part II: w = u + s, s in [0, Ubar - u]
    Ub = l.root(4) * (1 + (2 * (l / TAU0).log() + 4).sqrt())
    stop = Ub - u
    if stop.upper() > 0:
        S = breakpoints(stop)
        Gam = arb(0)
        for j in range(len(S) - 1):
            s0, s1 = S[j], S[j + 1]; D = s1 - s0
            wtop = arb(u.upper()) + s1
            gam = B * hprime(wtop) / l + ku * pos(v + s1 + cu) / sl
            gam = arb(gam.upper())
            c = betaII + Gam
            dens = (-r0_lo * s0).exp() / (u + s0)
            Ie = I_exp(gam - r0_lo, D)
            M1 += l * dens * (c.expm1() * Ie + gam * K_texp(gam - r0_lo, D))
            E2 += KP * (1 + u + s0) * dens * c.exp() * Ie
            E3 += 2 * KP * dens * c.exp() * Ie * l_eta(ulo_a + s0, arb(uhi_f) + s1, l, kmax_l, arb((v + s1 + cu).upper()))
            Gam = Gam + gam * D
    # T (Step 6): l T <= exp(log l + kappa_max/l + a_V(u*) + E_T)
    ustar = Ub + arb('0.5')
    aV = 4 * KV * ustar ** 2 * (ustar + 2).log() / l
    a_lu = pos(v) ** 2 / (2 * sl)
    lim = u0 * SQ30                      # u <= U_30  <=>  v <= u0 sqrt(2 log 30 + 4)
    ET2 = -2 - arb('1.5') * r0_lo
    if v.lower() > lim.upper():
        ET = ET2
    else:
        fac = lim - v + arb('1.5')                    # >= 1.5 wherever case 1 applies (u <= U_30)
        fac = arb(max(fac.lower(), arb('1.5')))
        ET1 = LOG30 - a_lu - r0_lo * fac
        ET = ET1 if v.upper() <= lim.lower() else arb(max(ET1.upper(), ET2.upper()))
    T = (l.log() + kmax_l + aV + ET).exp()
    if dbg:
        f = lambda x: '[%.4g, %.4g]' % (float(x.lower()), float(x.upper()))
        print({'M1': f(M1), 'E1': f(E1), 'E2': f(E2), 'E3': f(E3), 'T': f(T), 'betaI': f(betaI), 'alpha': f(alpha), 'r0': f(r0), 'ru': f(ru), 'M1I': f(M1I)})
    return -(M1 + E1 + E2 + E3 + T)

def band_cells(la, lb, du_small, rel_u, wf):
    cells = []
    u0a = float(arb(la).root(4).lower()); u0b = fup_float(arb(lb).root(4))
    X = u0a / 2
    x = 2.0
    while x < X:
        y = min(X, x + du_small if x < 40 else x * (1 + rel_u))
        cells.append((la, lb, x, y, False)); x = y
    va = math.floor(X - u0b) - 1.0                      # u0(l) + va <= X for all l in the band
    Ubb = arb(lb).root(4) * (1 + (2 * (arb(lb) / TAU0).log() + 4).sqrt())
    vtop = math.ceil(fup_float(Ubb - arb(la).root(4))) + 1.0   # u0(l) + vtop >= Ubar(lb) >= Ubar(l)
    nv = max(8, math.ceil((vtop - va) / (wf * u0a)))     # v-cells of width about wf * u0
    step = (vtop - va) / nv
    e = [va + k * step for k in range(nv)] + [vtop]
    cells += [(la, lb, e[k], e[k + 1], True) for k in range(nv)]
    return cells

def work(args):
    dick.build(top=300000) if dick._fine is None else None
    la, lb, du, rel, wf = args
    stack = band_cells(la, lb, du, rel, wf)[::-1]
    n = 0; fails = []; mn = None; depth_max = 0
    while stack:
        c = stack.pop(); n += 1
        la_, lb_, a, b, vm = c[:5]; dep = c[5] if len(c) > 5 else 0
        val = lS(la_, lb_, a, b, vm)
        if val is not None and val.lower() > 0:
            if mn is None or val.lower() < mn[0]: mn = (val.lower(), c)
            continue
        if dep >= 30:
            fails.append((c, None if val is None else val.str(5))); continue
        depth_max = max(depth_max, dep + 1)
        if (b - a) > 1e-6 * max(1.0, abs(a)) and (dep % 3 != 2):
            m = 0.5 * (a + b); stack += [(la_, lb_, m, b, vm, dep + 1), (la_, lb_, a, m, vm, dep + 1)]
        else:
            lm = math.sqrt(la_ * lb_); stack += [(lm, lb_, a, b, vm, dep + 1), (la_, lm, a, b, vm, dep + 1)]
    if mn is not None:
        q = frac(mn[0]); f = float(q)
        if Fraction(f) > q: f = math.nextafter(f, -math.inf)
        mn = (f, mn[1])
    return (la, lb), n, fails, mn, depth_max

if __name__ == '__main__':
    q = float(sys.argv[1]) if len(sys.argv) > 1 else 1.05
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    du = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    rel = float(sys.argv[4]) if len(sys.argv) > 4 else 0.05
    nv = float(sys.argv[5]) if len(sys.argv) > 5 else 0.005
    LMIN, LMAX = 3e9, 1e18
    bands = []; x = LMIN
    while x < LMAX:
        y = min(x * q, LMAX); bands.append((x, y, du, rel, nv)); x = y
    t0 = time.time()
    with get_context('fork').Pool(nproc, initializer=dick.build, initargs=(300000,)) as P:
        res = P.map(work, bands, chunksize=1)
    tot = sum(r[1] for r in res); fails = [f for r in res for f in r[2]]
    mn = min((r[3] for r in res if r[3] is not None), key=lambda z: z[0])
    print('Z2 independent: q=%g bands=%d cells=%d failed=%d min certified l*S=%.4g at %s  max depth=%d  time=%.0fs' % (
        q, len(bands), tot, len(fails), float(mn[0]), mn[1], max(r[4] for r in res), time.time() - t0))
    for f in fails[:20]: print('  FAIL', f)
