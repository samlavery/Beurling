from flint import arb, ctx
ctx.prec = 120
e = arb(1).exp()
Lam = arb(10)**8
logH0 = 8*Lam.log()**2                     # log H(X0) = 8 (log Lam)^2 off the raised range
print("log H(X0) at Lam=1e8 =", logH0)
# Rowweights (b)
q = 1 - 1/(3*e)
print("(2+1/z)/(1-1/(3e)) at z=X0:", 2/q, "(+ 1/(z q) negligible) <= 2.3:", bool(2/q + 1e-100 < arb('2.3')))
# Rowweights (e): (2+1/z)^{3/4} <= 2 iff 2+1/z <= 2^{4/3}
print("2^{4/3} =", arb(2)**(arb(4)/3), " (need 2+1/z <= this; z >= X0/2)")
# Reduction(ii): (2z+delta) theta C' <= 12 L^5.1 z (1+delta/(2z))(1+1/Lam)
print("12*(1+1/Lam)*(1+4e-48) =", 12*(1+1/Lam)*(1+arb('4e-48')))
# s_max: s_max - H(s_max)/2 >= 2z + (0.51 - 0.5*1.001) H(2z) = 2z + 0.0095 H(2z) > 2z+1 iff H(2z) > 1/0.0095
print("0.51-0.5005 =", arb('0.51')-arb('0.5005'), " threshold H >", 1/(arb('0.0095')))
# D relative error: 1/(X0 Lam) + H(X0)/(X0 Lam) vs e^{-0.98 Lam}, in logs
print("log(H(X0)/X0) + 1 =", logH0 - Lam + 1, " vs -0.98 Lam =", -arb('0.98')*Lam)
# Euler product extra factor in Lemma margin(c): paper count of realised primes in an interval of length H is <= 2H+2;
# each factor <= 1 + e^2(1+o(1))/y, so log factor <= 7.4(2H+2)/y <= 15 H/y (H > 200)
print("7.4*(2H+2)/H at H=200:", arb('7.4')*(2*200+2)/200)
print("log(15 H(X0)/X0) =", arb(15).log()+logH0-Lam, " vs log e^{-0.9 Lam} =", -arb('0.9')*Lam)
# Lemma P(iv): 1 + (L^6/4+5) M1 <= M1 L^6/2  iff  L^6/4 >= 5 + 1/M1
print("L^6/4 at L=1e8:", Lam**6/4)
