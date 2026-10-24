# Rigorous, method-independent cover: |phi''(t)| <= |phi''(m)| + h*sup_cell|phi'''| on each cell [m-h, m+h] of [0.02, 0.98].
from flint import arb, ctx
ctx.prec = 80
def parts(t):
    g = 1/t - 1/(1-t)
    phi = 1/(1+g.exp())
    P = phi*(1-phi)
    q = 1/t**2 + 1/(1-t)**2
    dq = -2/t**3 + 2/(1-t)**3
    ddq = 6/t**4 + 6/(1-t)**4
    A = (1-2*phi)*q**2 + dq
    dA = -2*P*q**3 + 2*(1-2*phi)*q*dq + ddq
    return P*q, P*A, P*((1-2*phi)*q*A + dA)

def cover(lo, hi, n, sub=8):
    worst2, worst3 = arb(0), arb(0)
    for i in range(n):
        a = arb(lo) + (arb(hi) - arb(lo))*i/n
        b = arb(lo) + (arb(hi) - arb(lo))*(i+1)/n
        # sub-cells for the phi''' enclosure, to limit dependency blow-up
        for j in range(sub):
            aa = a + (b - a)*j/sub; bb = a + (b - a)*(j+1)/sub
            m = (aa + bb)/2
            h = arb(((bb - aa)/2).upper())
            ball = m + arb(0, h.upper())
            _, _, d3 = parts(ball)
            _, d2m, _ = parts(m)
            bound = abs(d2m) + h*abs(d3)
            u = arb(bound.upper())
            if u > worst2: worst2 = u
            u3 = arb(abs(d3).upper())
            if u3 > worst3: worst3 = u3
    return worst2, worst3
w2, w3 = cover("0.02", "0.98", 2400)
print("cover [0.02,0.98]: sup|phi''| <=", w2.str(8), " (<=10:", w2 <= 10, ")  cell sup|phi'''| <=", w3.str(6))

# small-t analysis: the bound values at t=0.02 and monotonicity of e^{-1/t} t^{-k}
t0 = arb("0.02")
eg = (1/arb("0.98")).exp() * (-1/t0).exp()
q = 1/t0**2 + 1/arb("0.98")**2
dq = 2/t0**3 + 2/arb("0.98")**3
print("t=0.02: e^{-g}q <=", (eg*q).str(5), "  e^{-g}(q^2+|q'|) <=", (eg*(q*q+dq)).str(5))
# direct values at 0.02 for comparison
d1, d2, _ = parts(t0)
print("actual phi'(0.02) =", d1.str(5), " phi''(0.02) =", d2.str(5))
# check that the expansion of the bound uses only k<=4 terms with nonnegative coefficients
# e^{-g}q <= e^{1/.98}(e^{-1/t}t^-2 + e^{-1/t}/.98^2); e^{-g}(q^2+|q'|) <= e^{1/.98}e^{-1/t}(t^-4 + 2t^-2/.98^2 + .98^-4 + 2t^-3 + 2/.98^3)
# d/dt [e^{-1/t} t^{-k}] = e^{-1/t} t^{-k-2} (1 - k t) >= 0 for t <= 1/k
for k in range(0, 7):
    ok = all(((-1/(arb(i)/10000)).exp() * (arb(i)/10000)**(-k-2) * (1 - k*arb(i)/10000)) >= 0 for i in range(1, 201))
    print("k=%d derivative >= 0 on grid of (0,0.02]: %s" % (k, ok))
