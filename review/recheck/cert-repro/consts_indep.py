# Ball-arithmetic check of numerical constants that the text states without a certificate script
# (04x-x0band, 04k-kernels, 06-base-range). Not part of App B.
from flint import arb, ctx
ctx.prec = 100
z = lambda s: arb(s).zeta()
A = lambda s: 1 / (2 - z(s)) - 1
def zp(s):                                   # zeta'(s) via arb's derivative series
    from flint import arb_series
    return arb_series([arb(s), 1]).zeta()[1]
s = arb('1.97')
print('zeta(1.97) - 1 =', (z(s) - 1).str(6), ' (paper 0.674)')
print('-zeta\'(1.97) =', (-zp(s)).str(6), ' <= 1.0001:', bool(-zp(s) <= arb('1.0001')))
print('A(1.77) =', A(arb('1.77')).str(6), ' (paper 13.08; used <= 13.1):', bool(A(arb('1.77')) <= arb('13.1')))
print('A(1.8 - 3e-6) =', A(arb('1.8') - arb('3e-6')).str(8), ' <= 7.4915:', bool(A(arb('1.8') - arb('3e-6')) <= arb('7.4915')))
print('zeta(1.8) =', z(arb('1.8')).str(6), ' + X0^-0.7 <= 1.883:', bool(z(arb('1.8')) < arb('1.883')),
      '; sum H m^-1.8 = 1/(2-1.883) =', (1 / (2 - arb('1.883'))).str(5), '<= 8.6')
# rho_0: zeta(rho_0) = 2
lo, hi = arb('1.7'), arb('1.8')
for _ in range(60):
    m = (lo + hi) / 2
    if z(m) > 2: lo = m
    else: hi = m
print('rho_0 in [%s, %s] (paper 1.7286...)' % (lo.str(8), hi.str(8)))
s = 2 - arb('0.03')
A0 = 1 / (2 - z(s)) - 1; A1 = -zp(s) / (2 - z(s)) ** 2
print('A_0(0.03) =', A0.str(6), ' (paper 2.0673; used <= 2.07)', ' A_1(0.03) =', A1.str(6), ' (paper 9.409; used <= 9.42)')
# 06-base-range (c): Ein(2) = int_0^2 (e^w - 1)/w dw = Ei(2) - gamma - log 2, and the integrals I_1, I_2, I_3
Ein2 = arb(2).ei() - arb.const_euler() - arb(2).log()
print('Ein(2) [paper convention (e^w-1)/w] =', Ein2.str(8), ' < 3.69:', bool(Ein2 < arb('3.69')))
import math
def quad(f, a, b, n=200000):                 # composite Simpson in floats (numerical, not rigorous)
    h = (b - a) / n; s_ = f(a) + f(b)
    for k in range(1, n): s_ += (4 if k % 2 else 2) * f(a + k * h)
    return s_ * h / 3
I1 = quad(lambda v: v * (math.log(v) + 1.01), 1, 4)
U = lambda v: 1 + 2 * math.log(v)
# substitute v = e^t to integrate to infinity (tail beyond t = 200 negligible)
I2 = quad(lambda t: math.exp(t) * math.exp(t) * (U(math.exp(t)) / math.exp(t)) ** 3 * (math.log(U(math.exp(t))) + 1.01), math.log(4), 200)
c3 = 2 * math.exp(0.5772156649015329) * math.exp(float(Ein2.mid()))
I3 = quad(lambda t: math.exp(t) * math.exp(t) * c3 * (math.exp(t) / U(math.exp(t))) * math.exp(t) ** -4, math.log(4), 200)
print('I1 = %.4f (14.92)  I2 = %.4f (214.8)  I3 = %.4f (6.7)  (2.02/log2)(I1+I2+I3) = %.2f (<= 690)' % (I1, I2, I3, 2.02 / math.log(2) * (I1 + I2 + I3)))
