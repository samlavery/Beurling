# The theta-free absorption window h of the paper (Section params; Follow-up S1) against every condition that reads it.
#   log h(u) = L/8 for L <= 400 Lam^2;  log h(u) = max(50 Lam^2, 27 Lam l^2, 120 l^4/log l) for L >= 400 Lam^2  (L = log u, l = log L).
# Double precision, log domain; a cross-check of the analytic proofs, not a proof step. Checks, for each Lam in LAMS:
#  (W1) eq:twelvetwo of Lemma lemmaP with the precise y of capl_model (u0 = log h/log 2y), with ratio >= 1.0001 (room for the
#       non-dyadic factors 1 + 1e-5), u0 >= 100, and (*) of Lemma lemmaP(v): u0 >= 2 Lam; at every l with y >= X0^- (Abs may be
#       non-empty), from the onset of Abs to l = 1e70;
#  (W2) log h <= L/8, log h >= 11 l + log 2 (Lemma lemmaP(iv)), log 2y <= log h/100;
#  (W3) 04k-kernels: log(2.1 H(v)/X0) <= log h(v/X0) for log v >= 2 Lam - 1 (H = max(H_std, (2c)^2));
#  (W4) monotonicity and the slope b = d log h/d log u in [0, 1/8] (finite differences), continuity at L = 400 Lam^2;
#  (W5) the analytic bounds of Step 5 of the proof of Theorem caplw (raised range: 0.9 U log U >= 4.02 gamma Lam with
#       U = log h/(3.01 gamma Lam); standard regime: 0.9 v log v >= 16 l^2 + 19 l + 7 with v = 120 l^4/(log l (12 l^2 + 9 l + 8)),
#       and 27 Lam l^2/(12 l^2 + 9 l + 8) >= 2 Lam);
# and once: (W6) the scalar constants quoted in the text (Step 5, Lemma ZA, Lemma latenoise, 04k).
# Grids: step 1e-4 in l over the onset of Abs, the u^{1/8} piece and L = 400 Lam^2; +-2% at step 1e-5 around the crossovers
# 50 Lam^2 = 27 Lam l^2, l_std and 27 Lam l^2 = 120 l^4/log l; geometric beyond, up to l = 1e70.
import math, os, sys, io, contextlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
with contextlib.redirect_stdout(io.StringIO()):
    import analytic_capl as AC
import capl_model
from capl_model import logy_of
assert capl_model.THETA_B is None, "unset CAPL_THETA_B: this script checks the theta-free window"
LAMS = (1e8, 1e9, 1e10, 1e12, 1e16, 1e20, 1e30, 1e50, 1e70, 1e100)

def logh(l, lam):
    return capl_model.logh_of(l, lam)

def params(l, lam):
    s = l - 2*math.log(lam)
    logc = max(4*l*l - math.log(4), AC.gamma(s)*lam)
    log2y, logM1 = logy_of(logc, l)          # logy_of returns log(2y) (it adds log 2) and log M1 <= log c + log 2
    logH = max(8*l*l, 2*logM1)               # H = max(H_std, M1bar^2), M1bar <= 2c
    return s, logc, log2y, logM1, logH

def w1w2(l, lam):
    s, logc, log2y, logM1, logH = params(l, lam)
    if log2y - math.log(2) <= lam - 1: return None      # y < X0^- (conservatively: log y <= Lam - 1): Abs empty here
    K = logh(l, lam); u0 = K/log2y
    rhs = log2y + (logM1 + 6*l - math.log(2)) + 4*l      # log 2y + log C_d + 4 log L, C_d = M1 L^6/2
    r = 0.9*u0*math.log(u0)/rhs
    L = math.exp(l) if l < 700 else math.inf
    ok = (r >= 1.0001 and u0 >= 100 and u0 >= 2*lam and K <= L/8*(1 + 1e-12) and K >= 11*l + math.log(2)
          and log2y <= K/100)
    return ok, r, u0/lam

def crossings(lam):
    lt1 = math.sqrt(50*lam/27)
    a, b = 10.0, 1e160
    for _ in range(400):
        m = math.sqrt(a*b)
        if 120*m*m/math.log(m) >= 27*lam: b = m
        else: a = m
    return lt1, math.sqrt((7.5*lam + math.log(4))/4), b

tot_fail = 0
for lam in LAMS:
    lt1, lstd, lt2 = crossings(lam)
    l0 = 2*math.log(lam) + AC.sH - 0.01
    pts = [l0 + i*1e-4 for i in range(30000)]
    for c in (lt1, lstd, lt2):
        pts += [c*(1 + (i - 2000)*1e-5) for i in range(4001)]
    l = l0 + 3
    while l < 1e70:
        pts.append(l); l *= 1.001 if l < 10*lt2 else 1.1
    n = bad = 0; wr = (math.inf, None); wu = (math.inf, None)
    for l in pts:
        r = w1w2(l, lam)
        if r is None: continue
        n += 1
        if not r[0]: bad += 1
        if r[1] < wr[0]: wr = (r[1], l)
        if r[2] < wu[0]: wu = (r[2], l)
    # (W3) 04k: log v = L >= 2 Lam - 1; h at v/X0 has log = L - Lam
    m3 = (math.inf, None); bad3 = 0; n3 = 0
    L = 2*lam - 1
    while L < 1e300:
        l = math.log(L)
        s = l - 2*math.log(lam)
        logc = max(4*l*l - math.log(4), AC.gamma(s)*lam)
        logH = max(8*l*l, 2*(logc + math.log(2)))
        lp = math.log(L - lam)
        mar = logh(lp, lam) - (math.log(2.1) + logH - lam)
        if mar < 0: bad3 += 1
        if mar < m3[0]: m3 = (mar, L)
        n3 += 1; L *= 1.003
    # (W4) monotone, slope in [0, 1/8], continuity at L = 400 Lam^2
    bad4 = 0; maxb = 0.0
    for l in [math.log(400*lam*lam) + (i - 5000)*1e-4 for i in range(10001)] + [math.log(400*lam*lam)*1.001**i for i in range(1, 20000)]:
        if l > 700: break
        d = 1e-7
        b = (logh(l + d, lam) - logh(l, lam))/(math.exp(l + d) - math.exp(l))
        if b < -1e-12 or b > 0.125*(1 + 1e-6): bad4 += 1
        maxb = max(maxb, b)
    lc = math.log(400*lam*lam)
    jump = abs(logh(lc*(1 + 1e-15), lam) - logh(lc*(1 - 1e-15), lam))/(50*lam*lam)
    # (W5) analytic Step 5 bounds
    bad5 = 0; m5r = math.inf; m5s = math.inf; m5u = math.inf
    s = AC.sH; s_std = lstd - 2*math.log(lam)
    while s < s_std:
        l = 2*math.log(lam) + s
        if AC.gamma(s)*lam > 4*l*l - math.log(4):
            gm = AC.gamma(s); U = logh(l, lam)/(3.01*gm*lam)
            r = 0.9*U*math.log(U)/(4.02*gm*lam)
            if r < 1 or U < 2*lam: bad5 += 1
            m5r = min(m5r, r); m5u = min(m5u, U/lam)
        s += 1e-4 if s < AC.sH + 2 else 1e-3*s
    l = lstd
    while l < 1e70:
        v = 120*l**4/(math.log(l)*(12*l*l + 9*l + 8))
        r = 0.9*v*math.log(v)/(16*l*l + 19*l + 7)
        u0 = 27*lam*l*l/(12*l*l + 9*l + 8)
        if r < 1.10 or u0 < 2*lam: bad5 += 1
        m5s = min(m5s, r); m5u = min(m5u, u0/lam)
        l *= 1.0005
    fails = bad + bad3 + bad4 + bad5 + (jump > 1e-9)
    tot_fail += fails
    print(f"Lam={lam:.0e}: (W1-2) {n} pts, fails {bad}, min (12.2) ratio {wr[0]:.4f} at l={wr[1]:.5g}, min u0/Lam {wu[0]:.4f} at l={wu[1]:.5g};"
          f" (W3) {n3} pts, fails {bad3}, min margin {m3[0]:.4g} at L={m3[1]:.3g}; (W4) fails {bad4}, max b {maxb:.4f}, rel. jump {jump:.1e};"
          f" (W5) fails {bad5}, min raised {m5r:.4f}, min std {m5s:.4f}, min u0/Lam {m5u:.4f}")

# (W6) scalar constants quoted in the text
sH = AC.sH; g0 = AC.gstar(sH)
c = []
c.append(("log 400 <= s_H + 0.017", math.log(400) <= sH + 0.017))
c.append(("gamma(s_H) + 7.17*0.017 <= 0.46", g0 + (7.5 - g0)*0.017 <= 0.46 and 7.5 - g0 <= 7.17))
c.append(("e^{s_H}/8 >= 49.1", math.exp(sH)/8 >= 49.1))
c.append(("49.1/(3.01*0.46) >= 35", 49.1/(3.01*0.46) >= 35))
c.append(("0.9*35*log(35e8) >= 689", 0.9*35*math.log(35e8) >= 689))
c.append(("50/22.575 >= 2.214", 50/22.575 >= 2.214))
c.append(("log(2.214e8) >= 19.21", math.log(2.214e8) >= 19.21))
c.append(("4.02*3.01/45 <= 0.2689 and 0.2689*56.25 <= 15.13", 4.02*3.01/45 <= 0.2689 and 0.2689*56.25 <= 15.13))
c.append(("19.21/15.13 >= 1.26", 19.21/15.13 >= 1.26))
lstd8 = math.sqrt((7.5*1e8 + math.log(4))/4)
c.append(("l_std(1e8) >= 1.36e4; 16 + 19/l + 7/l^2 <= 16.002", lstd8 >= 1.36e4 and 16 + 19/1.36e4 + 7/1.36e4**2 <= 16.002))
c.append(("27/(12 + 9/l + 8/l^2) >= 2.249 at l = 1.36e4", 27/(12 + 9/1.36e4 + 8/1.36e4**2) >= 2.249))
c.append(("q <= 1.0001 and log(10/q) >= 2.3024", 1 + 0.75/1.36e4 + 0.67/1.36e4**2 <= 1.0001 and math.log(10/1.0001) >= 2.3024))
gmax = max((math.log(x) - 2.3024)/(2*x) for x in [math.exp(i*1e-4) for i in range(1, 200000)])
c.append((f"max g = {gmax:.6f} <= 0.0184", gmax <= 0.0184))
c.append(("18*(1-0.0184)/1.0001 >= 17.66 >= 1.10*16.002", 18*(1 - 0.0184)/1.0001 >= 17.66 >= 1.10*16.002))
c.append(("ZA: 4/0.87 <= 4.6, 4.6e <= 12.6", 4/0.87 <= 4.6 and 4.6*math.e <= 12.6))
c.append(("latenoise: 3.01*(1/(0.99-1e-6) + 1e-6) <= 3.1; 6.2*1.0001*(1+1e-10) <= 6.21; 6.21e*2/0.198 <= 171",
          3.01*(1/(0.99 - 1e-6) + 1e-6) <= 3.1 and 6.2*1.0001*(1 + 1e-10) <= 6.21 and 6.21*math.e*2/0.198 <= 171))
c.append(("04k: 8 log(113 Lam+18)^2 <= Lam-1 and 0.06 sqrt(113 Lam+18)+1.4 <= Lam-1 (Lam=1e8)",
          8*math.log(113e8 + 18)**2 <= 1e8 - 1 and 0.06*math.sqrt(113e8 + 18) + 1.4 <= 1e8 - 1))
c.append(("04k: log 2.1 <= 0.75, 2 log 2 <= 1.4", math.log(2.1) <= 0.75 and 2*math.log(2) <= 1.4))
c.append(("T1: 2*392^-4 <= 1", 2*392.0**-4 <= 1))
c.append(("D_max std: 3 + 17 e^{2l-4l^2} + 5e^{-8l^2} <= 3.01 at l = 1.36e4", 3 + 17*math.exp(2*1.36e4 - 4*1.36e4**2) <= 3.01))
for name, ok in c:
    print(("OK   " if ok else "FAIL ") + name)
    tot_fail += (not ok)
print("TOTAL FAILURES:", tot_fail)
