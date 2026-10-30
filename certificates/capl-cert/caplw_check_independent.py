# Independent numeric checks of the capacity theorem (paper Thm 6.22) Steps 1-3,5 (Λ-uniform version). Log-domain floats.
import math, random, os
# theta_b: absorption-window exponent (worst case 1/20 by default; CAPL_THETA_B overrides).
THETA_B = float(os.environ.get('CAPL_THETA_B', 1/20))
print("theta_b =", THETA_B)
def A(Lam, s): l = 2*math.log(Lam) + s; return math.log(2) + 3*math.log(Lam) + 2*s - math.log(l)
def G(Lam, s): a = A(Lam, s); return 2*math.sqrt(a*(a+1))*math.exp(s/2)/math.sqrt(Lam - a - 1)
def gstar(s): return 1.3*G(max(1e8, math.exp(-s)), s)
# s_H
lo, hi = 0.0, 10.0
for _ in range(100):
    m = (lo+hi)/2
    if gstar(m) < 1/3 - 1e-5: lo = m
    else: hi = m
sH = lo; print("s_H =", sH)
def gamma(s): return gstar(s) if s <= sH else (gstar(sH) + (7.5-gstar(sH))*(s-sH) if s <= sH+1 else 7.5)
random.seed(1); bad1 = bad2 = bad3 = bad5 = badu = 0; minH = minD = min5 = minu = math.inf
for _ in range(200000):
    Lam = 10**random.uniform(8, 30); s = random.uniform(-math.log(Lam), 60)
    l = 2*math.log(Lam) + s; L = math.exp(l) if l < 700 else None
    # Step 1: G decreasing in Λ (finite difference)
    if G(Lam*1.001, s) > G(Lam, s) and Lam - A(Lam*1.001, s) - 1 > 0: bad1 += 1
    logc = max(4*l*l - math.log(4), gamma(s)*Lam)
    # exact-ish ingredients: r0, D, m, a, j
    logL = l
    if s <= sH + 1:
        # high-degree rows (Step 2) with exact D*, j (log-domain): m <= L^2/(l Λ)
        logm = 2*l - math.log(l) - math.log(Lam); a = math.log(2) + logm   # a <= log(r0(D+1)) <= log 2m
        j = math.floor((logc - 1)/(2*a) - 0.5)
        logQ = logc/2; Dstar = math.floor(logQ/(1 + math.log(2) + logm)); k = Dstar + 1
        gain = k*(Lam - 1 - (math.log(2) + logm)) - math.log(3)
        lhs = (1 + j)*gain
        rhs = math.exp(l) + 10*l + 10 if l < 700 else float('inf')
        if lhs < rhs: bad2 += 1
        else: minH = min(minH, lhs/rhs)
    elif l <= 0.3*Lam:
        # Dickman rows: g >= Λ - log(3π) + 0.9(D-1)log(D-1), D >= L/Λ ; π <= L^2 ; a <= log(r0(D+1)) with r0 <= L/(3l)+4
        logD = l - math.log(Lam)                    # lower bound for D
        # g/L ~ 0.9 (D-1) log(D-1)/L with D-1 >= e^{logD} - 1
        g_over_L = 0.9*(1 - math.exp(-logD))*(logD)/Lam    # (D-1)log(D-1)/L >= (1/Λ)(1-1/D) log(D-1); log(D-1)~logD
        a = math.log(1/(3*l) + 4*math.exp(-l)) + l + math.log(2*math.exp(l)/Lam + 1)  # log(r0(D+1)) upper, D<=2L/Λ
        onej = (logc - 1)/(2*a) - 0.5
        ratio = onej*g_over_L
        if ratio < 1 + 1e-3: bad3 += 1
        else: minD = min(minD, ratio)
    # Step 5 condition for s >= sH with log c = γΛ (raised): e^s log(θ_b Λ e^s/(3.01γ)) >= 13.45 γ^2/θ_b,
    # and hypothesis (*) of Lemma P(v): u0 >= θ_b Λ e^s/(3.01γ) >= 2Λ
    if s >= sH and gamma(s)*Lam > 4*l*l:
        gm = gamma(s); es = math.exp(min(s,700))
        lhs5 = es*math.log(THETA_B*Lam*es/(3.01*gm)); rhs5 = 13.45*gm*gm/THETA_B
        if lhs5 < rhs5: bad5 += 1
        min5 = min(min5, lhs5/rhs5)
        u0L = THETA_B*es/(3.01*gm)
        if u0L < 2: badu += 1
        minu = min(minu, u0L)
print("Step1 violations:", bad1, " Step2 violations:", bad2, "(min lhs/rhs %.4f)" % minH,
      " Dickman violations:", bad3, "(min ratio %.4f)" % minD, " Step5 violations:", bad5, "(min lhs/rhs %.4f)" % min5,
      " u0 >= 2Lam violations:", badu, "(min u0/Lam %.4f)" % minu)
