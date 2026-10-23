# Certified constants for Section 6 with python-flint (arb).
from flint import arb, ctx
ctx.prec = 200
g = arb.const_euler()
eg = g.exp()
# Ein(2) in the paper's convention: int_0^2 (e^t-1)/t dt = Ei(2) - gamma - log 2
Ein2 = arb(2).ei() - g - arb(2).log()
print("Ein(2) [paper conv] =", Ein2, " < 3.69:", Ein2 < 3.69)
c3 = 2 * eg * Ein2.exp()

def integrate(f, a, b, n=20000):
    # composite Simpson on [a,b] in arb arithmetic (numerical; error estimated by doubling)
    a = arb(a); b = arb(b); h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(a + i * h)
    return s * h / 3

I1 = integrate(lambda v: v * (v.log() + arb('1.01')), 1, 4, 2000)
def i2(v):
    U = 1 + 2 * v.log()
    return U ** 3 * (U.log() + arb('1.01')) / v ** 2
def i3(v):
    U = 1 + 2 * v.log()
    return c3 / (v ** 2 * U)
# substitute v = e^s to handle the tail: int_4^inf f(v) dv = int_{log4}^{S} f(e^s) e^s ds + tail
import math
S = 60
I2 = integrate(lambda s: i2(s.exp()) * s.exp(), arb(4).log(), S, 40000)
I3 = integrate(lambda s: i3(s.exp()) * s.exp(), arb(4).log(), S, 40000)
# tails beyond e^S: i2 ~ (1+2s)^3 (log(1+2s)+1.01) e^{-s}, tiny
tail2 = (1 + 2 * arb(S)) ** 3 * ((1 + 2 * arb(S)).log() + 2) * arb(-S).exp() * 2
print("I1 =", I1.mid(), "(paper 14.92)")
print("I2 =", I2.mid(), "+tail<", tail2.mid(), "(paper 214.8)")
print("I3 =", I3.mid(), "(paper 6.7)")
tot = arb('2.02') / arb(2).log() * (I1 + I2 + I3)
print("(2.02/log2)(I1+I2+I3) =", tot.mid(), "(paper <= 690)")
Lam = arb(10) ** 8
print("690/Lambda =", (690 / Lam).mid(), "<= 7e-6")
# Lemma margin (b) Step 3
print("4.1 e^gamma =", (arb('4.1') * eg).mid(), " (paper's 7.4 includes e^{2.2/Lambda}); 4.04 e^g =", (arb('4.04') * eg).mid())
# (d)(iii)
L = arb(79)
for Lb in [arb(79), arb(10) ** 8]:
    val = (arb('5.1') * Lb + arb('1.40') * (Lb ** 2 + 2 * Lb) + arb('15.5') * Lb ** 2) / Lb ** 2
    print("(5.1 log b + 1.40(log^2 b + 2 log b) + 15.5 log^2 b)/log^2 b at log b =", Lb.mid(), ":", val.mid(), "(<= 17)")
print("17 * 1.01 =", (arb(17) * arb('1.01')).mid(), "; 17.2 e^gamma =", (arb('17.2') * eg).mid(), "(<= 31)")
# (d)(ii)
for Lv in [arb(10) ** 8]:
    v = arb('1.0001') / 6 * (1 + 2 / Lv)
    print("(d)(ii) 1.0001/6 (1+2/Lam) =", v.mid(), "(<= 0.167)")
# |g| <= 0.51/Lam: 1.0001 (kappa + (1+kappa)/2)
print("Prop g1: 0.99-0.167-6e-4 =", 0.99 - 0.167 - 6e-4, "; 0.822 - 0.4209 =", 0.822 - 0.4209, "; 0.82-0.4209=", 0.82 - 0.4209)
# Use paragraph: c'/(8 C_S)
print("c'/(8*77) =", 0.15 / (8 * 77), "; /7e-6 =", 0.15 / (8 * 77) / 7e-6)
# kappa exponent: -5/12 + 0.02
print("kappa exponent:", -5 / 12 + 0.02)
# (d)(iii): 4.1 kappa (log x)^5 <= X0^{-0.34} for log x <= X0^{0.01}: exponent -0.39666+0.05 = -0.34666, need 4.1 <= X0^{0.00666}
print("X0^{0.006666} at Lambda=1e8: e^", 0.0066667 * 1e8)
