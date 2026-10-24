import sys; sys.path.insert(0, "/tmp/rhscratch/r26"); from arbshim import mp, mpf, log, sqrt, exp, ceil, e


kL = mpf('3.79'); f = mpf('0.9')

def X_of(Lt, Lam): return Lt + 442 + 2*log(Lam)
def Y_of(Lt, Lam):
    X = X_of(Lt, Lam); return X + log(X) + mpf('0.7')

print("== 1. Step 7 extension ==")
for Lam in [mpf(10)**8, mpf(10)**12, mpf(10)**30]:
    Q = mpf(10)**4*Lam
    logTy = Q/51 - 500
    print(" Lam=%s  logT_y(min)=%s  >=1e10? %s" % (mp.nstr(Lam,3), mp.nstr(logTy,8), logTy >= mpf(10)**10))
c = mpf(1)/mpf('50.35') - mpf(1)/51
print(" 1/50.35-1/51 =", mp.nstr(c, 8), ">= 2.53e-4:", c >= mpf('2.53e-4'))
print(" 0.33769*50.35 =", mp.nstr(mpf('0.33769')*mpf('50.35'), 8))
print(" 0.33769/3.79 =", mp.nstr(mpf('0.33769')/kL, 8))
# Inequality 2.53e-4 Q >= 2 log Lam + log Q, minimal at Q=1e4 Lam (increasing in Q for Q>4e3)
for Lam in [mpf(10)**8, mpf(10)**9, mpf(10)**20]:
    Q = mpf(10)**4*Lam
    print(" Lam=%s: 2.53e-4 Q - (2logLam+logQ) = %s" % (mp.nstr(Lam,3), mp.nstr(mpf('2.53e-4')*Q - 2*log(Lam) - log(Q), 6)))
# Full check: for |t| <= T_y+1, Y(t) <= Q/50.35, i.e. at Lt = log(T_y+4) (use log T_y + 4/T_y bound)
for Lam in [mpf(10)**8, mpf(10)**10]:
    for Q in [mpf(10)**4*Lam, mpf(10)**6*Lam, mpf(10)**9*Lam]:
        logTy = Q/51 - 500
        Lt = logTy + 4*exp(-logTy)  # >= log(T_y+4)
        Y = Y_of(Lt, Lam)
        bound = Q/51 - 57 + 2*log(Lam) + log(Q)
        print(" Lam=%s Q=%s: Y=%s <= Q/51-57+..=%s : %s ; Y<=Q/50.35: %s ; X<=Q: %s" % (
            mp.nstr(Lam,3), mp.nstr(Q,3), mp.nstr(Y,15), mp.nstr(bound,15), Y <= bound, Y <= Q/mpf('50.35'), X_of(Lt,Lam) <= Q))

print("== 2. Step 8 discs ==")
Lam = mpf(10)**8
Lt_min = log(mpf(1)/16 + 3)
Ymin = Y_of(Lt_min, Lam)
dmax = mpf('0.0891')/(Lam*Ymin)
R1 = (kL + (1+f)/2)*dmax
print(" X_min =", mp.nstr(X_of(Lt_min, Lam), 8), " Y_min =", mp.nstr(Ymin, 8))
print(" delta_t max =", mp.nstr(dmax, 6), " R1 max =", mp.nstr(R1, 6), "<=1e-9:", R1 <= mpf('1e-9'))
# relative change of delta_zf = 0.0891/(Lam Y(t)) over |t'-t|<=R1, worst at t=1/16
dLt = R1/(mpf(1)/16 - R1 + 3)
X0 = X_of(Lt_min, Lam)
dY = dLt*(1 + 1/X0)
print(" relative change of delta_zf over disc <=", mp.nstr(dY/Ymin, 6), "<= 1e-8:", dY/Ymin <= mpf('1e-8'))
print(" BC constant 4(kL+f)/(1-f) =", mp.nstr(4*(kL+f)/(1-f), 8), "; r1<R1:", kL+f < kL+(1+f)/2)
# leftmost point 1 - 0.95 delta_t vs eq:lp-zf width (weaker form)
for X in [mpf('479.96'), mpf(10)**3, mpf(10)**6, mpf('8.9e7'), mpf(10)**12]:
    Y = X + log(X) + mpf('0.7')
    ratio = mpf('0.0891')*(X+18)/(mpf('0.088')*Y)
    print(" X=%s delta_t/(eq:lp-zf width) = %s ; 0.95*that = %s" % (mp.nstr(X,4), mp.nstr(ratio,8), mp.nstr(mpf('0.95')*ratio,6)))
# |log((s-1)/s)| bound for disc points with |Im s| >= 1/16 - R1
print(" log(1+1/(1/16-R1)) + pi =", mp.nstr(log(1 + 1/(mpf(1)/16 - R1)) + mp.pi, 10))
