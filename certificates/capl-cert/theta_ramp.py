# Step 5 of the proof of Theorem caplw and hypothesis (*) of Lemma lemmaP(v) on the raised range, as functions of theta_b
# (paper: Theorem caplw, Step 5; Lemma lemmaP, steps (v)-(vi)). Double precision; a cross-check, not a proof step.
#  (A) the analytic Step 5 inequality e^s log(theta_b Lam e^s/(3.01 gamma)) >= 13.45 gamma^2/theta_b on s in [s_H, s_H + 30],
#      at Lam = 1e8 (its left side increases with Lam), step 1e-5 on the ramp;
#  (B) the constants of the tangent-line proof in the paper (phi(t) = e^{t/2} sqrt(c + t) >= k gamma(s_H + t) on [0, 1]);
#  (C) min of u0/Lam with the precise y of capl_model (u0 = theta_b L/log 2y), for Lam in {1e8, 1e10, 1e12, 1e20}, at every s
#      with y >= X0 (where Abs can be non-empty), s in [-log Lam, 30] at step 1e-3; (*) needs u0 >= 2 Lam.
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    import analytic_capl as AC
from capl_model import logy_of, THETA_B
tb = THETA_B
sH, g0 = AC.sH, AC.gstar(AC.sH); gp = 7.5 - g0
print(f"theta_b = {tb}; s_H = {sH:.6f}, e^s_H = {math.exp(sH):.4f}, gamma(s_H) = {g0:.6f}")
worst, wt = math.inf, None
n = 0
for i in range(3000001):
    t = i*1e-5
    g = AC.gamma(sH + t); es = math.exp(sH + t)
    r = es*math.log(tb*1e8*es/(3.01*g))/(13.45*g*g/tb)
    if r < worst: worst, wt = r, t
    n += 1
print(f"(A) {n} points: min lhs/rhs = {worst:.4f} at t = {wt:.4f}  ->", "OK" if worst > 1 else "FAIL")
c = math.log(1e8*math.exp(sH)/(3.01*7.5)) + math.log(tb)
phi1 = math.sqrt(math.e*(c + 1)); dphi = phi1*(0.5 + 0.5/(c + 1)); k = math.sqrt(13.45/(math.exp(sH)*tb))
ok = phi1 - dphi >= k*g0 and phi1 >= k*7.5
print(f"(B) c = {c:.4f}; tangent at t=1: {phi1:.4f} + {dphi:.4f}(t-1); k*gamma: {k*g0:.4f} at t=0, {k*7.5:.4f} at t=1;"
      f" ratio^2 at t=1 = {(phi1/(k*7.5))**2:.4f} ->", "OK" if ok else "FAIL")
ts = 1 - g0/gp
print(f"    analytic min of e^s/(3.01 gamma) on the ramp: e^(s_H+t*)/(3.01*{gp:.5f}), t* = {ts:.5f}: "
      f"{math.exp(sH + ts)/(3.01*gp):.4f}; times theta_b = {tb*math.exp(sH + ts)/(3.01*gp):.4f}")
for lam in (1e8, 1e10, 1e12, 1e20):
    m, ms, cnt = math.inf, None, 0
    s = -math.log(lam) + 1e-3
    while s < 30:
        l = 2*math.log(lam) + s
        logc = max(4*l*l - math.log(4), AC.gamma(s)*lam)
        logy, _ = logy_of(logc, l)
        if logy > lam:
            u0 = tb*math.exp(l - math.log(logy)) if l < 700 else math.inf
            if u0/lam < m: m, ms = u0/lam, s
            cnt += 1
        s += 1e-3
    print(f"(C) Lam = {lam:.0e}: {cnt} points with y > X0; min u0/Lam = {m:.4f} at s = {ms:.3f} ->", "OK" if m >= 2 else "FAIL")
