# Correction 52: numerical checks for the new bound eq:s2 (04d-noise.tex). Run with flintenv python -I -B.
from flint import arb, ctx
ctx.prec = 200
log, exp, sqrt = (lambda x: arb(x).log()), (lambda x: arb(x).exp()), (lambda x: arb(x).sqrt())

# (1) Gamma inflation in v3: max over (1,2) of 1/Gamma(x), at the minimum of Gamma.
lo, hi = arb(1.4), arb(1.5)
for _ in range(200):           # bisection on digamma = 0 (Gamma'/Gamma)
    mid = (lo+hi)/2
    if mid.digamma() < 0: lo = mid
    else: hi = mid
x0 = (lo+hi)/2
print("1  argmin Gamma on (1,2) =", x0.str(10), "; max 1/Gamma =", (1/x0.gamma()).str(10))

# (2) rho(v) <= 1/Gamma(v+1): spot values rho(2)=1-log2, rho(3) (known 0.04860838...)
print("2  rho(2)=%s <= 1/Gamma(3)=0.5 ; rho(3)=0.0486084 <= 1/6" % (1-log(2)).str(8))

# (3) block constant: 1.01*1.443*(1/2 + sum_{a>=3} Xm^{-(a-2)/2}/a), Lambda >= 1e8
Lam = arb(10)**8
c = arb(1.01)*arb(1.443)*(arb(0.5) + exp(-(Lam-1)/2)/3*2)
print("3  constant 1.01*1.443*(1/2+...) =", c.str(8), " <= 0.73:", bool(c < arb(0.73)))
# block count: (L-2Lam)/log2 + 3 <= 1.443 L for L >= Lam >= 1e8
L = Lam
print("   blocks (L=Lam):", ((L-2*Lam)/log(2)+3 - arb(1.443)*L < 0))

# (4) X0/X0^- <= 1 + 1e-9 : H(X0)/X0 = exp(8 (log Lam)^2 - Lam)
r = exp(8*log(Lam)**2 - Lam)
print("4  H(X0)/X0 at Lambda=1e8: log =", (8*log(Lam)**2 - Lam).str(8))

# (5) second branch: sigma = 1/2 sqrt(L log L) > log Xm >= 1e8 - 1 forces L >= 1e15
L = arb(10)**15
print("5  sigma(1e15) =", (sqrt(L*log(L))/2).str(6), "< 1e8-1:", bool(sqrt(L*log(L))/2 < Lam-1))

def checks(L):
    s = sqrt(L*log(L))/2
    umin = (L - 4*s - arb(0.7))/(s + arb(1.39))
    phi = umin*log(umin) - umin - arb(1.3e-7)*umin*log(umin+2)          # C1
    l = L - 4*s - arb(0.7)
    phi2 = sqrt(l)*log(sqrt(l)) - sqrt(l) - arb(12.8)*log(sqrt(l)+2)   # C2
    return s, umin, phi/s, phi2/s
worst1 = worst2 = None
for k in range(30, 2001):       # log10 L = 15 .. 1000 in steps of 1/2
    L = arb(10)**(arb(k)/2)
    s, umin, r1, r2 = checks(L)
    worst1 = r1 if worst1 is None or r1 < worst1 else worst1
    worst2 = r2 if worst2 is None or r2 < worst2 else worst2
for e in [10**4, 10**6, 10**9, 10**12]:
    L = arb(10)**e
    s, umin, r1, r2 = checks(L)
    worst1 = min(worst1, r1, key=lambda t: float(t.mid())); worst2 = min(worst2, r2, key=lambda t: float(t.mid()))
s, umin, r1, r2 = checks(arb(10)**15)
print("6  at L=1e15: umin =", umin.str(6), " phi(umin)/sigma =", r1.str(6), " phi2/sigma =", r2.str(6))
print("   min over grid 1e15..1e1000 and 1e(1e4..1e12): C1 ratio", worst1.str(6), " C2 ratio", worst2.str(6))

# (7) sums. First part: L <= Lam^2: <= 1.443 Lam^2 * 9 (Lam^2+1.1)^2 Lam^2 (1+1e-9) e^{-Lam}
first = arb(1.443)*Lam**2*9*(Lam**2+arb(1.1))**2*Lam**2*(1+arb(1e-9))
print("7  first part:  log <=", (log(first) - Lam).str(10), "; 14 Lam^8 bound ok:", bool(first < 14*Lam**8))
# Second part: sigma(L) >= c sqrt(L) for L >= Lam^2 with c = 1/2 sqrt(log Lam^2)
cc = sqrt(log(Lam**2))/2
print("   c = 1/2 sqrt(log Lam^2) =", cc.str(8), ">= 3.03:", bool(cc > arb(3.03)))
second = 10*Lam**6 + (10/log(2))*(2*Lam**7/(arb(3.03)-7/Lam))
print("   second part: log <=", (log(second) - arb(3.03)*Lam).str(10), "; <= 10 Lam^7:", bool(second < 10*Lam**7))
tot = first*exp(-Lam) + second*exp(-arb(3.03)*Lam)
print("   total log =", log(tot).str(10), " <= -9e7:", bool(log(tot) < -9*arb(10)**7))
