# "True" components of Sigma(l,u;tau) (Step 5/6 definitions), computed directly with the exact Dickman rho
# (power-series table), the exact profile Q, the exact indicator 1[w <= U(m)], exact eta_f, by Gauss-Legendre
# quadrature on unit subintervals with breakpoints at integers, at the kink w = m^{1/4}, and at w*.
import math, pickle, sys
sys.path.insert(0, "/tmp/rhscratch/r30/indep")
from dickman import Rho
Bf, KPf, C0 = 11.0, 2.2, 0.70
R = None
def load():
    global R
    R = Rho.__new__(Rho); R.logrho, R.C = pickle.load(open("/tmp/rhscratch/r30/indep/rho270k.pkl", "rb")); R.K = len(R.logrho) - 1
def gl_nodes(n):
    xs, ws = [], []
    for i in range(1, n + 1):
        x = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, x
            for k in range(2, n + 1): p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = n * (x * p1 - p0) / (x * x - 1); dx = p1 / dp; x -= dx
            if abs(dx) < 1e-16: break
        xs.append(x); ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws
GX, GW = gl_nodes(24)
def U(x, tau): return x ** 0.25 * (1 + math.sqrt(2 * math.log(x / tau) + 4))
def bisect(f, a, b):
    fa = f(a)
    for _ in range(200):
        m = 0.5 * (a + b); fm = f(m)
        if (fm > 0) == (fa > 0): a, fa = m, fm
        else: b = m
    return 0.5 * (a + b)
def components(l, u, tau):
    kap = 4 * tau + 1500
    u0 = l ** 0.25
    def Q(x, w):
        X = max(w - x ** 0.25, 0.0)
        return Bf * (1 + w) ** 3 * math.log(2 + w) / x + X * X / (2 * math.sqrt(x))
    Qlu = Q(l, u)
    def mof(w): return l * w / (1 + w)
    def D(w): m = mof(w); return Q(m, w) - Qlu - kap / (w * l)
    def etaf(w):
        m = mof(w); X = max(w - m ** 0.25, 0.0)
        Am = Bf * (1 + w) ** 3 * math.log(2 + w) / m
        dmQ = Am / m + X / (4 * m ** 1.25) + X * X / (4 * m ** 1.5)
        dwQ = Bf * (3 * (1 + w) ** 2 * math.log(2 + w) + (1 + w) ** 3 / (2 + w)) / m + X / math.sqrt(m)
        return kap / m ** 2 + dmQ + (1 + w) ** 2 / l * dwQ
    lr_u1 = R.logrho_at(u - 1)
    def ratio(w): return math.exp(R.logrho_at(w - 1) - lr_u1)    # rho(w-1)/rho(u-1)
    # w*: w = U(m(w);tau); the indicator 1[w <= U(m)] is 1 exactly on [u-1, w*]
    g = lambda w: w - U(mof(w), tau)
    hiw = U(l, tau) + 2
    assert g(u - 1) < 0 < g(hiw)
    wst = bisect(g, u - 1, hiw)
    gk = lambda w: w - mof(w) ** 0.25                            # kink of a(m,w)
    wk = bisect(gk, 1.0, 2 * u0) if gk(1.0) < 0 < gk(2 * u0) else None
    bps = sorted(set([u - 1, wst] + [float(k) for k in range(math.ceil(u - 1), math.floor(wst) + 1)] + ([wk] if wk and u - 1 < wk < wst else [])))
    bps = [b for b in bps if u - 1 <= b <= wst]
    IM, IE2, IE3 = [], [], []
    small = 0
    for a, b in zip(bps, bps[1:]):
        if b <= a: continue
        h = 0.5 * (b - a); c = 0.5 * (a + b)
        sM = sE2 = sE3 = 0.0
        for x, wt in zip(GX, GW):
            w = c + h * x; rt = ratio(w); Dw = D(w); eD = math.exp(Dw)
            sM += wt * rt / w * math.expm1(Dw); sE2 += wt * rt * eD * (1 + w) / w; sE3 += wt * rt / w * eD * etaf(w)
        IM.append(h * sM); IE2.append(h * sE2); IE3.append(h * sE3)
        if a > u + 5 and abs(h * sE2) < 1e-40: small += 1
        if small > 3: break                                       # remaining part of [.., w*] negligible (< 1e-40 each)
    mass_out = math.exp(R.logrho_at(wst) - lr_u1)                # pi(w > w*) = rho(w*)/rho(u-1)  (R1)
    Mm1 = math.fsum(IM) - mass_out
    r0 = R.r(u - 1) if u > 2 else 1.0
    E1 = 2 * KPf * u * u * r0 * math.exp(D(u - 1)) / l
    E2 = KPf / l * math.fsum(IE2)
    E3 = 2 * KPf * math.fsum(IE3)
    # tail (Step 6 / Lemma V bound), divided by G(l,u); Phi_inf exact, and the C0 version used by the certificate
    us = U(l, tau) + 0.5
    aV = 12.8 * us * us * math.log(us + 2) / l
    lr_tail = R.logrho_at(us) - lr_u1
    Tc0 = math.exp(math.log(l / tau) + lr_tail + aV + kap / l - Qlu)
    phifac = max(math.exp(kap / tau), 30 * math.exp(kap / (30 * tau)))
    T = Tc0 / phifac
    return dict(Mm1=Mm1, E1=E1, E2=E2, E3=E3, T=T, Tc0=Tc0, wst=wst, Sigma=-(Mm1 + E1 + E2 + E3 + T), SigmaC0=-(Mm1 + E1 + E2 + E3 + Tc0))
