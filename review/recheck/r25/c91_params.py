"""R25: the numerical side conditions of #91 at the paper's parameters.

kappa = X_0^{-5/12+0.02}, Lambda = log X_0 >= 1e8, 0 < a <= 8.  Everything is in log space;
each inequality only gets easier as Lambda grows (kappa decreases, X_0 increases).
"""
from flint import arb, ctx

ctx.prec = 128
for Lam in [arb(10) ** 8, arb(10) ** 9]:
    ek = arb(-5) / 12 + arb(2) / 100          # log kappa / Lambda
    logk = ek * Lam
    kap = logk.exp()                          # underflows to a tiny ball; fine for comparisons
    print(f"Lambda={Lam.str(3, radius=False)}: log kappa = {logk.str(8, radius=False)}  (exponent {ek.str(8, radius=False)})")
    # (1+kappa)^2 <= 1.01
    c1 = 2 * (1 + kap).log()
    print("  log (1+k)^2 =", c1.str(3), "<= log 1.01 =", arb('1.01').log().str(5), bool(c1 < arb('1.01').log()))
    # 1/(kappa X_0) <= 1e-4  <=> -log kappa - Lambda <= log 1e-4
    c2 = -logk - Lam
    print("  log(1/(kappa X_0)) =", c2.str(8, radius=False), "<= log 1e-4:", bool(c2 < arb('1e-4').log()))
    # 2.01 * (1 + 1/(kappa X_0)) <= 3
    print("  2.01(1+1/(kX_0)) <= 3:", bool(arb('2.01') * (1 + c2.exp()) <= 3))
    # log(1+k)/k <= 1
    print("  log(1+k)/k <= 1:", bool((1 + kap).log() <= kap))
    # (1+k)^{1-a/Lambda} <= 1.01 for 0<a<=8
    print("  (1+k)^(1-a/Lam) <= 1.01:", bool((1 - arb(0) / Lam) * (1 + kap).log() <= arb('1.01').log()))
    # 1.01 (kappa X_0 + 1)/X_0 <= 3 kappa  <=>  1.01 (1 + 1/(kappa X_0)) <= 3
    print("  1.01(kX_0+1)e^a/X_0 <= 3 k e^a:", bool(arb('1.01') * (1 + c2.exp()) <= 3))
    # ZB downstream: 3 X_0^{1/2} + X_0^{1/2} = 4 X_0^{1/2}  (trivial), and the final 12e^{6.9 X0^1/2}+8X0^1/2 vs e^{0.24 X0^2}
    # ZBlow with a: X_0^{a/Lambda} = e^a exactly since Lambda = log X_0.
print("ok")
