import sys; sys.path.insert(0, "/tmp/rhscratch/r26"); from arbshim import mp, mpf, log, sqrt, exp, ceil, e


def step9_ratio(Lam, ell):
    # y' = v, log v = ell; log T_v = ell/(51 Lam log ell) - 500; log T_1 = 2 sqrt(ell) + (2/19) log ell
    logTv = ell/(51*Lam*log(ell)) - 500
    logT1 = 2*sqrt(ell) + mpf(2)/19*log(ell)
    return logTv/logT1

def step10_ratio(Lam, Lp, eta, logy=None):
    if logy is None: logy = Lp
    logTy = logy/(51*Lam*log(logy)) - 500
    k = ceil(log(1/eta) + 20*log(Lp))
    L1 = 2*log(Lp) + log(1/eta) + log(k) + mpf('3.08')
    return logTy/L1, logTy, L1

print("== 3a. Step 9 margin ==")
Lam = mpf(10)**8
ell0 = mpf(10)**5*Lam**2*log(Lam)**2
r = step9_ratio(Lam, ell0)
print(" Lam=1e8, log v = log X_LP = %s : logT_v/logT_1 = %s" % (mp.nstr(ell0, 8), mp.nstr(r, 8)))
prev = None; mono = True
for Lexp in [8, 8.5, 9, 10, 12, 15, 20, 30, 50, 100]:
    L = mpf(10)**Lexp
    ell = mpf(10)**5*L**2*log(L)**2
    rr = step9_ratio(L, ell)
    if prev is not None and rr < prev: mono = False
    prev = rr
    print("  Lam=1e%s at threshold: ratio %s" % (Lexp, mp.nstr(rr, 8)))
print("  increasing in Lam along threshold:", mono)
# in v (ell) at fixed Lam
for L in [mpf(10)**8, mpf(10)**20]:
    ell = mpf(10)**5*L**2*log(L)**2
    prev = step9_ratio(L, ell); mono = True; fac = mpf('1.0001')
    pts = [ell*mpf(10)**mpf(j) for j in ["0", "0.001", "0.01", "0.1", 1, 2, 5, 10, 50, 200, 1000]]
    vals = [step9_ratio(L, p) for p in pts]
    mono = all(vals[i] <= vals[i+1] for i in range(len(vals)-1))
    print("  Lam=%s: ratio over log v in [thr, thr*1e1000] monotone: %s; first/last %s %s" % (mp.nstr(L,3), mono, mp.nstr(vals[0],6), mp.nstr(vals[-1],6)))
# derivative sign check: d/d(ell) of ratio > 0 for ell >= threshold, analytic surrogate via finite differences on log grid
import itertools
bad = 0
for L in [mpf(10)**8, mpf(10)**9, mpf(10)**15]:
    ell = mpf(10)**5*L**2*log(L)**2
    x = log(ell)
    for i in range(2000):
        a = exp(x); b = exp(x + mpf('0.01'))
        if step9_ratio(L, b) < step9_ratio(L, a): bad += 1
        x += mpf('0.01')
print("  finite-difference decreases on fine grid:", bad)
# the sufficiency claim: at ell with ell = 1.1e4 Lam^2 (log ell)^2, is log T_v >= log T_1 ?
for L in [mpf(10)**8, mpf(10)**12]:
    ell = mpf(10)**20
    for _ in range(200):
        ell = mpf('1.1e4')*L**2*log(ell)**2
    print("  boundary of 1.1e4 condition, Lam=%s: log v=%s, ratio=%s" % (mp.nstr(L,3), mp.nstr(ell,6), mp.nstr(step9_ratio(L, ell),8)))

print("== 3b. Step 10 margin ==")
Lam = mpf(10)**8
Lp = 76*Lam**3
r, lt, l1 = step10_ratio(Lam, Lp, exp(-2*Lam))
print(" Lam=1e8, Lp=76Lam^3, eta=e^{-2Lam}: logT_y=%s L1=%s ratio=%s" % (mp.nstr(lt,8), mp.nstr(l1,10), mp.nstr(r,8)))
print(" L1+500 =", mp.nstr(l1+500, 12), " vs 2Lam+7logLam+513 =", mp.nstr(2*Lam+7*log(Lam)+513, 12))
print(" RHS Lp/(51 Lam log Lp) =", mp.nstr(Lp/(51*Lam*log(Lp)), 8), ">= Lam^2/(3logLam+5)=", mp.nstr(Lam**2/(3*log(Lam)+5), 8), ">=1e6 Lam:", Lam**2/(3*log(Lam)+5) >= mpf(10)**6*Lam)
vals = []
for Lexp in [8, 9, 10, 15, 30]:
    L = mpf(10)**Lexp
    for mult in [1, 10, mpf(10)**3, mpf(10)**10, mpf(10)**100]:
        Lp = 76*L**3*mult
        rr = step10_ratio(L, Lp, exp(-2*L))[0]
        vals.append((Lexp, mult, rr))
for Lexp in [8, 9, 10, 15, 30]:
    row = [v for v in vals if v[0] == Lexp]
    mono = all(row[i][2] <= row[i+1][2] for i in range(len(row)-1))
    print("  Lam=1e%s: ratios over Lp/76Lam^3 in {1,10,1e3,1e10,1e100}: %s monotone=%s" % (Lexp, [mp.nstr(v[2],5) for v in row], mono))
# eta in [e^{-2Lam}, 1/2]: smaller L1 for bigger eta
for eta in [exp(-2*mpf(10)**8), mpf('1e-100'), mpf('0.5')]:
    print("  Lam=1e8 Lp=76Lam^3 eta=%s ratio=%s" % (mp.nstr(eta,3), mp.nstr(step10_ratio(mpf(10)**8, 76*mpf(10)**24, eta)[0],6)))

print("== 4. Step 9 wording ==")
for Lexp in [8, 8.0001, 9, 12, 20, 50, 100, 1000]:
    L = mpf(10)**Lexp
    ell = mpf(10)**5*L**2*log(L)**2
    print("  Lam=1e%s: loglog v=%s  3logLam=%s  ok=%s ; 9.9e4 Lam^2 log^2 Lam <= log v: %s" % (
        Lexp, mp.nstr(log(ell),8), mp.nstr(3*log(L),8), log(ell) <= 3*log(L), mpf('9.9e4')*L**2*log(L)**2 <= ell))
# log Lam - 2 log log Lam - log(1e5) >= 0 and increasing for Lam>=1e8
L = mpf(10)**8
print("  margin logLam - 2loglogLam - log1e5 at 1e8:", mp.nstr(log(L) - 2*log(log(L)) - log(mpf(10)**5), 8))
# ell/(log ell)^2 increasing for ell > e^2: derivative (log ell - 2)/(log ell)^3
print("  d/dell [ell/log^2 ell] = (log ell - 2)/log^3 ell > 0 iff ell > e^2 =", mp.nstr(e**2, 6))
print("  (1000+4logLam)^2 at 1e8 =", mp.nstr((1000+4*log(mpf(10)**8))**2, 8), "<= 1e5Lam^2log^2Lam:", (1000+4*log(mpf(10)**8))**2 <= mpf(10)**5*mpf(10)**16*log(mpf(10)**8)**2)
