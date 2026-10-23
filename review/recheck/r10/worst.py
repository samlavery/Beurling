# Worst case of eq:lp-transfer from the displayed Step-3 bounds, over log y = L >= 1e8 and eta in [eta_y, 1/8].
#  P(eta,L)  := 1/eta + 6 + e^{-eta L/2} e^{4.5} L                     (bound for P_y(sigma); P_y(1) <= e^{4.5} L)
#  D(eta,L)  := 2 e^{-eta L}/eta + e^{-eta L/2} e^{4.5} L               (bound for |Delta|)
#  D1(eta,L) := 2 e^{-eta L}(L/eta + 1/eta^2) + e^{-eta L/2} e^{4.5} L (L+0.43)   (bound for |Delta'|; S(y) <= L+0.43)
#  ratio1 = P/(2/eta) <= 1 ; ratio2 = D*P/1e-2 <= 1 ; ratio3 = eta L (D1*P + D*P*(L+0.43))/(1 - D*P) <= 1
from flint import arb, ctx
ctx.prec = 200
E45 = arb(4.5).exp()
def bounds(eta, L):
    a = (-eta*L).exp(); b = (-eta*L/2).exp()
    P = 1/eta + 6 + b*E45*L
    D = 2*a/eta + b*E45*L
    D1 = 2*a*(L/eta + 1/eta**2) + b*E45*L*(L + arb('0.43'))
    r1 = P*eta/2
    r2 = D*P*100
    r3 = eta*L*(D1*P + D*P*(L+arb('0.43')))/(1 - D*P)
    return r1, r2, r3
def etay(L): return 17*L.log()/L
import math
rows = []
for Lf in [1e8, 1e9, 1e12, 1e20]:
    L = arb(Lf)
    ey = etay(L)
    best = [arb(0)]*3; arg = [None]*3
    # log grid in eta from eta_y to 1/8
    n = 400
    for i in range(n+1):
        eta = ey * (arb('0.125')/ey)**(arb(i)/n)
        r = bounds(eta, L)
        for j in range(3):
            if r[j].upper() > best[j].upper(): best[j] = r[j]; arg[j] = eta
    print(f"log y={Lf:.0e}: eta_y={float(ey.mid()):.4e}; max ratio1={float(best[0].upper()):.6f} at eta={float(arg[0].mid()):.4g}; "
          f"max ratio2={float(best[1].upper()):.3e} at eta={float(arg[1].mid()):.4g}; max ratio3={float(best[2].upper()):.3e} at eta={float(arg[2].mid()):.4g}")
# smallest L for which all three hold at their worst eta (eta_y for 2,3; 1/8 for 1), and eta_y <= 1/8, eps_f >= 1/L
def ok(Lf):
    L = arb(Lf); ey = etay(L)
    if not (ey < arb('0.125')): return False
    n = 200; m = [0,0,0]
    for i in range(n+1):
        eta = ey * (arb('0.125')/ey)**(arb(i)/n)
        r = bounds(eta, L)
        for j in range(3): m[j] = max(m[j], float(r[j].upper()))
    return all(x <= 1 for x in m)
lo, hi = 100.0, 1e8
for _ in range(60):
    mid = math.sqrt(lo*hi)
    if ok(mid): hi = mid
    else: lo = mid
print(f"all three eq:lp-transfer bounds (from the displayed Step-3 bounds) hold for every log y >= {hi:.1f}  (fail just below {lo:.1f})")
print("eta_y <= 1/8 needs log y >=", next(L for L in range(100, 5000) if 17*math.log(L)/L <= 0.125))
print("eps_f = 5e-4 >= 1/log y needs log y >= 2000;  eq:lp-pole's 1e-8 needs log y >= 1e8 (equality at Lambda = 1e8)")
