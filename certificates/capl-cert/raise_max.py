# Cross-check for Theorem caplw, Step 6 (numerical only; the proof uses the analytic bound <= 1e-6 on the raise, Step 6 last item):
# the raise of H over H_std, max(0, 2 log M1 - 8 l^2)/L with H = max(H_std, M1^2), log H_std = 8 l^2,
# maximised over log10 Lambda in [8, 30] (step 0.05) and s = l - 2 log Lambda in [-log Lambda, 30] (step 0.01).
# Here L = log z, l = log L, M1 = r0 + phi(r0) + 1, phi(u) = c + u c^{1/2} + u(u+1)/2, r0 = ceil(L/(3l)) + 3,
# log c = max(4 l^2 - log 4, gamma(s) Lambda). Standard library only; run with `python3 -I raise_max.py`.
import math

def A(Lam, s):
    l = 2*math.log(Lam) + s
    return math.log(2) + 3*math.log(Lam) + 2*s - math.log(l)

def G(Lam, s):
    a = A(Lam, s)
    return 2*math.sqrt(a*(a + 1))*math.exp(s/2)/math.sqrt(Lam - a - 1)

def gstar(s):
    return 1.3*G(max(1e8, math.exp(-s)), s)

lo, hi = 0.0, 10.0          # s_H: gstar(s_H) = 1/3 - 1e-5
for _ in range(100):
    m = (lo + hi)/2
    if gstar(m) < 1/3 - 1e-5: lo = m
    else: hi = m
sH = lo

def gamma(s):
    if s <= sH: return gstar(s)
    if s <= sH + 1: return gstar(sH) + (7.5 - gstar(sH))*(s - sH)
    return 7.5

best, arg, n = 0.0, None, 0
for i in range(441):
    e = 8 + 0.05*i
    Lam = 10**e
    s = -math.log(Lam) + 0.001
    while s < 30:
        l = 2*math.log(Lam) + s
        L = math.exp(l)
        logc = max(4*l*l - math.log(4), gamma(s)*Lam)
        r0 = math.ceil(L/(3*l)) + 3
        terms = [logc, math.log(r0) + logc/2, math.log(r0*(r0 + 1)/2 + r0 + 1)]
        t = max(terms)
        logM1 = t + math.log(sum(math.exp(x - t) for x in terms))
        v = max(0.0, 2*logM1 - 8*l*l)/L
        if v > best: best, arg = v, (e, s)
        n += 1
        s += 0.01
print(f"s_H = {sH:.4f}; points = {n}")
print(f"max (log H - log H_std)/L = {best:.3e} at log10 Lambda = {arg[0]:.2f}, s = {arg[1]:.2f}; analytic bound 1e-6: "
      + ("OK" if best <= 1e-6 else "FAIL"))
