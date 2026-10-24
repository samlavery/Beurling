# Independent implementation (from the LaTeX of Step 7(iii), not from bs_cert_arb.py) of the bound S at a POINT (l,u),
# in arb at 200 bits, with point values of r(u), r(u-1).  literal=True uses beta_a exactly as displayed in the paper
# (no indicator on the shift term); literal=False adds the indicator [v + c_u > 0] (what the code does).
from flint import arb, ctx
ctx.prec = 200
B, KP, KMIN, S1 = arb(11), arb("2.2"), arb(4) * arb(10)**8, arb(60)
def pos(x):
    if x > 0: return x
    if x < 0: return arb(0)
    return x.nonnegative_part()
def S_point(l, u, r, r0, r0ET, literal=False, parts=False):
    l, u, r, r0, r0ET = map(arb, (l, u, r, r0, r0ET))
    u0 = l.root(4); v = u - u0; sl = l.sqrt(); cu = u0 / (3 * u); ku = 1 + 1 / (2 * (u - 1))
    A = B * (1 + u)**3 * (2 + u).log() / l
    betaA = A / u
    alphaA = (B / l) * u**3 * (3 * u - 4) * (1 + u).log() / (u - 1)**2
    shift = cu * (2 * pos(v) + cu) / (2 * sl)
    if not literal and not (v + cu > 0): shift = arb(0)   # (v+c)_+^2 - v_+^2 = 0 when v + c <= 0
    betaa = (ku - 1) * pos(v + cu)**2 / (2 * sl) + shift
    alpha = alphaA + ku * pos(v - 1 + cu) / sl
    bI = betaA + betaa - KMIN / (u * l); bII = betaA + betaa
    Ubar = u0 * (1 + (2 * (l / arb(10)**8).log() + 4).sqrt())
    g1 = (B / l) * 8 * (1 + u + S1)**2 * (2 + u + S1).log() + ku * pos(v + S1 + cu) / sl
    gm = (B / l) * 8 * (1 + Ubar)**2 * (2 + Ubar).log() + ku * pos(Ubar - u0 + cu) / sl
    assert r0 > g1 and r0 > gm
    q = (-(r0 - gm) * S1).exp() / (r0 - gm)
    Mm1 = bI.expm1() * (1 - 1 / (u * r)) + bII.expm1() / (u * r) - bI.exp() * (-(-alpha).expm1()) * (1 - 1 / r) \
          + bII.exp() / u * (g1 / (r0 * (r0 - g1)) + q)
    E1 = 2 * KP * u**2 * r0 * (bI - alpha).exp() / l
    E2 = KP * u / (u - 1) * ((u - 1) * bI.exp() + bII.exp() * (1 / (r0 - g1) + q)) / l
    kmax = 4 * l / 30 + 1500
    def etab(w, d):
        dp = pos(d + cu)
        return 4 * kmax / l**2 + 4 * B * (1 + w)**3 * (2 + w).log() / l**2 + dp / (4 * (l / 2)**arb(1.25)) \
               + ku * dp**2 / (2 * l**arb(1.5)) + (1 + w)**2 / l * (2 * B * (1 + w)**2 * (3 * (2 + w).log() + 1) / l + arb(2).sqrt() * dp / sl)
    E3 = 2 * KP * (etab(u, v) * bI.exp() + bII.exp() / u * (etab(u + S1, v + S1) / (r0 - g1) + etab(Ubar, Ubar - u0) * q))
    aV = arb("12.8") * (Ubar + arb(0.5))**2 * (Ubar + arb(2.5)).log() / l
    U30 = u0 + u0 * (2 * arb(30).log() + 4).sqrt()
    a_lu = pos(v)**2 / (2 * sl)
    if u <= U30: ET = arb(30).log() - a_lu - r0ET * (U30 - u + arb(1.5))
    elif u > U30: ET = -2 - arb(1.5) * r0ET
    else: ET = arb.union(arb(30).log() - a_lu - r0ET * (pos(U30 - u) + arb(1.5)), -2 - arb(1.5) * r0ET)
    T = (kmax / l + aV + ET).exp()
    S = -(Mm1 + E1 + E2 + E3 + T)
    if parts: return S, dict(Mm1=Mm1, E1=E1, E2=E2, E3=E3, T=T, bI=bI, bII=bII, alpha=alpha, g1=g1, gm=gm)
    return S
