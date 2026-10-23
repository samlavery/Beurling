from flint import arb, acb, ctx
ctx.prec = 200
def rg(z):  # 1/Gamma(z) for acb
    return z.rgamma()
# integrals
f1 = lambda z, a: (1+z)*rg(z+1)       # (1+u)/Gamma(u+1)
g1 = lambda z, a: rg(z+1)             # 1/Gamma(u+1)
T = 80
I1 = acb.integral(f1, 1, T)
I0 = acb.integral(g1, 1, T)
# tail beyond T: (1+u)/Gamma(u+1) <= (1+u)/Gamma(T+1) * ... crude: for u>=T, Gamma(u+1)>=Gamma(T+1)*T^(u-T)
tail = arb(T+2)/arb(T+1).gamma() * 2   # very crude, but negligible
print("int_1^T (1+u)/G(u+1) =", I1.real.str(20), " tail<=", tail.str(5))
print("int_1^T 1/G(u+1)     =", I0.real.str(20))
u0 = 1 - arb("5e-9")
Ib = acb.integral(f1, acb(u0), 1)
print("int_{1-5e-9}^1 f =", Ib.real.str(10))
tot = I1.real + Ib.real + tail
print("int_{u0}^inf f <=", tot.upper().str(15), " <=3.4480?", tot.upper() <= arb("3.4480"))
I0b = acb.integral(g1, acb(u0), 1)
print("int_{u0}^inf 1/G <=", (I0.real+I0b.real+tail).upper().str(12), "<=1.1815?", (I0.real+I0b.real+tail).upper()<=arb("1.1815"))
# max of f on [0,40] by interval subdivision
def fball(a, b):
    m = (arb(a)+arb(b))/2; r = (arb(b)-arb(a))/2
    u = arb(m.mid(), r.upper())
    return (1+u)/ (u+1).gamma()
mx = arb(0)
N = 20000
best = None
for i in range(N):
    a = 0.0 + 40.0*i/N; b = 0.0 + 40.0*(i+1)/N
    v = fball(a, b).upper()
    if v > mx: mx = v; best=(a,b)
print("max f on [0,40] <=", mx.str(12), "at", best, " <=2.007?", mx <= arb("2.007"))
# finer around the max
mx2 = arb(0)
for i in range(20000):
    a = 0.9 + 0.4*i/20000; b = 0.9 + 0.4*(i+1)/20000
    v = fball(a,b).upper()
    if v > mx2: mx2 = v
print("max f on [0.9,1.3] fine <=", mx2.str(12))
# beyond 40: f decreasing (log-concave and f(40) < f(39))
print("f(39),f(40):", fball(39,39).str(5), fball(40,40).str(5))
# psi(1.47)>0 i.e. Gamma increasing from 1.47
print("digamma(1.47) =", arb("1.47").digamma().str(10))
# g(u0) = 1/Gamma(u0+1)
print("1/Gamma(2-5e-9) =", (1/(u0+1).gamma()).str(15))
C = 2*arb("0.70")*arb("0.02").exp()
print("2C0 e^0.02 =", C.str(15))
first = C*arb("3.4480")/arb(2).log()
print("first coeff =", first.str(15), "<=7.1049?", first.upper()<=arb("7.1049"))
lin = C*(arb("2.01") + (arb(4)/3).log()*arb("1.1815")/arb(2).log())
cst = C*(arb(4)/3).log()*arb("1.0001")
print("linear coeff =", lin.str(10), "<=3.58?", lin.upper()<=arb("3.58"), " const=", cst.str(10), "<=0.42?", cst.upper()<=arb("0.42"))
# Y<4v^2 range: 1.2*3/(2 log 2)*(1+1.1/L) with L>=1e8
y1 = arb("1.2")*3/(2*arb(2).log())*(1+arb("1.1e-8"))
print("Y<4v^2 coeff =", y1.str(10), "<=2.7?", y1.upper()<=arb("2.7"))
# check the exact (log16v^2)^2-(log2v)^2 vs 3L^2(1+1.1/L): coefficient of L
# (2L + log16 - 2log3)^2 - (L - log1.5)^2 = 3L^2 + L*(4(log16-2log3) + 2log1.5) + ...
c1 = 4*(arb(16).log()-2*arb(3).log()) + 2*arb("1.5").log()
c0 = (arb(16).log()-2*arb(3).log())**2 - arb("1.5").log()**2
print("coef L:", c1.str(10), " /3 =", (c1/3).str(10), " const:", c0.str(10))
tot2 = arb("2.7")+arb("7.11")+arb("1e-20")
print("total:", tot2.str(10))
# u0 bound: 1 - log1.5/L with L >= Lambda + log1.5 >= 1e8
print("log1.5/1e8 =", (arb("1.5").log()/arb("1e8")).str(5))
# tail u>30: (L/log2) * int_30^inf (1+u)*1.4 e^{-0.9 u log u} du  (per L^2)
h = lambda z,a: (1+z)*1.4*(-(0.9)*z*z.log()).exp()
It = acb.integral(h, 30, 200)
print("tail u>30 coefficient ~", (It.real/arb(2).log()).str(5), "+ boundary term 31*1.4*e^{-0.9*30 log30} =", (31*1.4*(-(arb("0.9"))*30*arb(30).log()).exp()).str(5))
