from flint import arb, arb_series, ctx
ctx.prec = 120
# (a) identities of the phi' <= 2 proof at sample points
for s_ in ["0.03", "0.1", "0.218", "0.37", "0.5", "0.77"]:
    t = arb(s_)
    g = 1/t - 1/(1-t); phi = 1/(1+g.exp()); s = t*(1-t); r = (1-2*t)/(2*s)
    print(s_, "r-g/2:", (r - g/2).str(3), " P-1/(4cosh^2 r):", (phi*(1-phi) - 1/(4*r.cosh()**2)).str(3),
          " q-(1-2s)/s^2:", (1/t**2 + 1/(1-t)**2 - (1-2*s)/s**2).str(3), " 1+r^2-(1-2s)^2/(4s^2):", (1 + r**2 - (1-2*s)**2/(4*s**2)).str(3),
          " phi' <= 1/(1-2s):", phi*(1-phi)*(1/t**2+1/(1-t)**2) <= 1/(1-2*s))

# (b) R''(x) for R(x) = a x^th cos(gam log x) phi(log(x/xp)): series in x vs hand formula, and the bound
def phi_ser(z):
    # z an arb_series; phi(z) for 0<z<1 via psi
    psi = lambda w: (-(w.inv())).exp()
    return psi(z) / (psi(z) + psi(1 - z))
def phi_pts(t):
    g = 1/t - 1/(1-t); phi = 1/(1+g.exp()); P = phi*(1-phi)
    q = 1/t**2 + 1/(1-t)**2; dq = -2/t**3 + 2/(1-t)**3
    return phi, P*q, P*((1-2*phi)*q**2 + dq)
a, th, gam, xp = arb("1.7"), arb("0.3"), arb("37.5"), arb("1000")
worst_ratio = arb(0)
for u_ in ["0.05", "0.2", "0.218", "0.5", "0.78", "0.95"]:
    u = arb(u_)
    x0 = xp * u.exp()
    X = arb_series([x0, 1], prec=3)
    L = X.log()
    R = a * (th * L).exp() * (gam * L).cos() * phi_ser(L - xp.log())
    c = R.coeffs()
    Rpp_series = 2 * c[2]
    # hand formula: R'' = a x^{th-2}[(th^2-th-gam^2) C F + (1-2th) gam S F + (2th-1) C F' - 2 gam S F' + C F'']
    lx = x0.log(); C = (gam*lx).cos(); S = (gam*lx).sin()
    F, F1, F2 = phi_pts(u)
    hand = a * x0**(th-2) * ((th**2 - th - gam**2)*C*F + (1-2*th)*gam*S*F + (2*th-1)*C*F1 - 2*gam*S*F1 + C*F2)
    bound = a * x0**(th-2) * (gam**2 + (1+2*2)*gam + th*(1-th) + 2 + 10)
    print("u=%s  R'' series %s  hand %s  diff %s  |R''|<=bound: %s" % (u_, Rpp_series.str(10), hand.str(10), (Rpp_series-hand).str(3), abs(Rpp_series) <= bound))
# the coefficient step: gam^2 + 5 gam + th(1-th) + 12 <= gam^2 + 6 gam  iff gam >= 12 + th(1-th) (<= 12.25)
print("threshold gamma for (1+6/gamma):", 12 + arb(1)/4)
