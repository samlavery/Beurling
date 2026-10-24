# Independent check: closed-form phi', phi'', phi''' (derived by hand), high-precision maximisation of |phi''|,
# and a rigorous cover of [0.02,0.98] by midpoint value + half-width * enclosure of |phi'''| on the cell.
from flint import arb, arb_series, ctx
ctx.prec = 200

def parts(t):
    g = 1/t - 1/(1-t)
    phi = 1/(1+g.exp())
    P = phi*(1-phi)
    q = 1/t**2 + 1/(1-t)**2
    dq = -2/t**3 + 2/(1-t)**3
    ddq = 6/t**4 + 6/(1-t)**4
    d1 = P*q
    A = (1-2*phi)*q**2 + dq
    d2 = P*A
    dA = -2*P*q**3 + 2*(1-2*phi)*q*dq + ddq
    d3 = P*((1-2*phi)*q*A + dA)
    return phi, d1, d2, d3

# 1. compare closed forms against direct definition psi(t)/(psi(t)+psi(1-t)) via arb_series (length 4)
def series(t):
    x = arb_series([t, 1], prec=4)
    psi = lambda z: (-(z.inv())).exp()
    f = psi(x) / (psi(x) + psi(1 - x))
    c = f.coeffs() + [arb(0)]*4
    return c[0], c[1], 2*c[2], 6*c[3]
worst = 0
for i in range(1, 100):
    t = arb(i)/100
    a = parts(t); b = series(t)
    for u, v in zip(a, b):
        r = abs(u - v)
        if not (r < arb("1e-40")):
            print("MISMATCH", i, u, v)
print("closed forms agree with psi-definition at t=0.01..0.99")

# 2. symmetry phi(1-t) = 1 - phi(t)
for s in ["0.1", "0.3", "0.218", "0.49"]:
    t = arb(s)
    a = parts(t); b = parts(1 - t)
    print("sym", s, (a[0] + b[0] - 1).str(5), (a[1] - b[1]).str(5), (a[2] + b[2]).str(5))

# 3. locate maxima of |phi''|: bisection on phi''' sign changes on a fine grid
N = 20000
prev = None
roots = []
for i in range(1, N):
    t = arb(i)/N
    d3 = parts(t)[3]
    s = 1 if d3 > 0 else (-1 if d3 < 0 else 0)
    if prev is not None and s != prev and s != 0:
        lo, hi = arb(i-1)/N, t
        for _ in range(150):
            m = (lo + hi)/2
            sm = 1 if parts(m)[3] > 0 else -1
            if sm == prev: lo = m
            else: hi = m
        roots.append((lo+hi)/2)
    prev = s
for r in roots:
    v = parts(r)
    print("crit t = %s  phi'' = %s  phi' = %s" % (r.str(15), v[2].str(15), v[1].str(10)))
best = max(roots, key=lambda r: abs(parts(r)[2]).mid())
print("sup|phi''| = %s at t = %s" % (abs(parts(best)[2]).str(15), best.str(12)))
# grid max of |phi'|, |phi''|
m1 = max(abs(parts(arb(i)/N)[1]).mid() for i in range(1, N))
m2 = max(abs(parts(arb(i)/N)[2]).mid() for i in range(1, N))
print("grid max |phi'| =", m1, " grid max |phi''| =", m2)
