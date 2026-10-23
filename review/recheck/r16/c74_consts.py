from flint import arb, acb, ctx
ctx.prec = 200
g = arb.const_euler()
ein2 = arb(2).ei() - g - arb(2).log()
print("Ein(2) =", ein2)
# I1 = int_1^4 v(log v + 1.01) dv
def integ(f, a, b):
    return acb.integral(lambda x, _: f(x), a, b)
I1 = integ(lambda v: v*(v.log()+acb("1.01")), 1, 4)
print("I1 =", I1)
# I2 = int_4^inf U^3 (log U + 1.01)/v^2 dv, U = 1+2 log v ; substitute v = e^t, dv = e^t dt
def f2(t):
    U = 1+2*t
    return U**3*(U.log()+acb("1.01"))*(-t).exp()
I2a = integ(f2, acb(4).log(), 200)
# tail beyond t=200 negligible: bound U^3(logU+1.01)e^{-t} 
print("I2 (t<=200) =", I2a)
C = 2*g.exp()*ein2.exp()
def f3(t):
    U = 1+2*t
    return (-t).exp()/U
I3 = C*integ(f3, acb(4).log(), 200)
print("I3 =", I3)
tot = (arb("2.02")/arb(2).log())*(I1.real+I2a.real+I3.real)
print("(2.02/log2)(I1+I2+I3) =", tot)
print("690/1e8 =", 690/1e8)
# Euler product extra factor: p in (y, y+H(y)], p^{2/log y} <= e^2 (1+eps)
print("e^2 =", arb(2).exp())
