# Ball-arithmetic checks of the elementary facts used (but not interval-checked) in the derivation of S (Step 7(iii)).
from flint import arb, ctx
ctx.prec = 120
def h(w): return (1+w)**4*(2+w).log()/w
def hp(w):  # h'
    L=(2+w).log(); return (1+w)**3*(3*w-1)*L/w**2 + (1+w)**4/(w*(2+w))
def hpp(w):
    L=(2+w).log(); P=(1+w)**4/w; P1=(1+w)**3*(3*w-1)/w**2; P2=(1+w)**2*(6*w*w-4*w+2)/w**3
    return P2*L + 2*P1/(2+w) - P/(2+w)**2
def Lam(w): return (1+w)**2*(2+w).log()
def cover(f, a, b, n, name, geometric=True):
    bad=0; worst=None
    import math
    for i in range(n):
        if geometric: x0=a*(b/a)**(i/n); x1=a*(b/a)**((i+1)/n)
        else: x0=a+(b-a)*i/n; x1=a+(b-a)*(i+1)/n
        X=arb.union(arb(x0),arb(x1)); v=f(X)
        if not (v>0): bad+=1
        lo=float(v.lower()); worst=lo if worst is None else min(worst,lo)
    print(f"{name}: [{a},{b}] {n} cells, failures={bad}, min lower={worst:.4g}")
# finite-difference check of hp, hpp formulas at a few points
for w in (1.0,2.5,40.0,1e4):
    e=arb(1e-12); W=arb(w)
    print('fd check w=',w, float(((h(W+e)-h(W-e))/(2*e)-hp(W)).mid()), float(((hp(W+e)-hp(W-e))/(2*e)-hpp(W)).mid()))
cover(hpp, 1.0, 1e7, 20000, "h''>0 (h convex on [1,1e7])")
cover(lambda w: 8*Lam(w)-hp(w), 2.0, 1e7, 20000, "h'(w) <= 8 Lambda(w) on [2,1e7]")
cover(lambda u: hp(u-1)-u**3*(3*u-4)*(1+u).log()/(u-1)**2, 2.0, 1e7, 20000, "h'(u-1) >= u^3(3u-4)log(1+u)/(u-1)^2")
cover(lambda x: (1-x).root(4)-(1-x/3), 1e-9, 0.5, 20000, "(1-x)^{1/4} >= 1-x/3 on (0,1/2]", geometric=False)
cover(lambda w: (1+1/(2*w)) - (1+1/w).sqrt(), 1.0, 1e7, 20000, "sqrt((1+w)/w) <= 1+1/(2w), w>=1")
cover(lambda u: (2+1/(u-1)) - (u/(u-1))**arb(1.5), 2.0, 1e7, 20000, "(u/(u-1))^{3/2} <= 2k_u, u>=2")
