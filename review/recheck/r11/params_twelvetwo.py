"""Independent check of the absorption thresholds (05-queue §queue-conv, Thm caplw(b), Lemma P, Lemma ZA).
Everything in log space.  For each Lambda and each s = loglog z - 2 log Lambda on a fine grid:
  * s <= s_H : log y(z) < log X0^-  (no absorbed element at that scale);
  * s >  s_H : condition eq:twelvetwo of Lemma P at u = z, with y := max(y(scale z), y(scale 2z)) (the sup over [u,2u]),
               theta_b = 1/8 (worst case), C_d = M_1(u) L^6 / 2;
  * Lemma ZA: log 2y <= lambda(v) = max(22.6 Lambda, 12(log v)^2 + 9 log v + 8), v = log z, wherever s > s_H;
  * Lemma P (v): u_0 >= 2 Lambda and loglog 2y <= 1.79 u_0 wherever s > s_H.
Parameters as in eq:params and Thm caplw: gamma(s), log c = max(4 l^2 - log 4, gamma Lambda), Q = c^{1/2},
phi(u) = c + uQ + u(u+1)/2, r0 = ceil(L/(3l)) + 3, M1 = r0 + phi(r0) + 1, rbar0 = L/(3l) + 4, Mbar1 likewise,
H = max(exp(8 l^2), Mbar1^2), L0 = max(L^5, 48 M1 L^3 / 0.15^2), y = H L0 L^6."""
import math

def A_(Lam, s):
    return math.log(2 * Lam ** 3 * math.exp(2 * s) / (2 * math.log(Lam) + s))

def G_(Lam, s):
    A = A_(Lam, s)
    return 2 * math.sqrt(A * (A + 1)) * math.exp(s / 2) / math.sqrt(Lam - A - 1)

def gamma_star(s):
    Lam_s = max(1e8, math.exp(-s))
    return 1.3 * G_(Lam_s, s)

# s_H by bisection
lo, hi = 5.0, 7.0
for _ in range(200):
    mid = (lo + hi) / 2
    if gamma_star(mid) < 1 / 3 - 1e-5: lo = mid
    else: hi = mid
sH = lo

def gamma(s):
    if s <= sH: return gamma_star(s)
    if s <= sH + 1: return gamma_star(sH) + (7.5 - gamma_star(sH)) * (s - sH)
    return 7.5

def logaddexp(a, b):
    m = max(a, b); return m + math.log(math.exp(a - m) + math.exp(b - m))

def params(Lam, l, dl=0.0):
    """log-space parameters at the scale with loglog z = l (L = e^l), optionally L -> L + dl."""
    if dl:
        l = l + math.log1p(dl * math.exp(-l)) if l < 700 else l
    s = l - 2 * math.log(Lam)
    logc = max(4 * l * l - math.log(4), gamma(s) * Lam)
    def log_phi_plus(u):   # log(u + phi(u) + 1), phi = c + u c^{1/2} + u(u+1)/2
        t = logc
        t = logaddexp(t, math.log(u) + logc / 2)
        t = logaddexp(t, math.log(u * (u + 1) / 2 + u + 1))
        return t
    if l < 700:
        L = math.exp(l)
        r0 = math.ceil(L / (3 * l)) + 3
        rb = L / (3 * l) + 4
        logM1 = log_phi_plus(r0); logMb = log_phi_plus(rb)
    else:   # r0 ~ e^l/(3l): c = e^{logc} with logc >= 4 l^2 - log 4 dominates r0 c^{1/2} and r0^2
        lr0 = l - math.log(3 * l)
        logM1 = logaddexp(logaddexp(logc, lr0 + logc / 2), 2 * lr0)
        logMb = logM1
    logH = max(8 * l * l, 2 * logMb)
    logL0 = max(5 * l, math.log(48) + logM1 + 3 * l - 2 * math.log(0.15))
    logy = logH + logL0 + 6 * l
    return dict(l=l, s=s, logc=logc, logM1=logM1, logH=logH, logL0=logL0, logy=logy)

def main():
    print(f"s_H = {sH:.6f}  (paper: 5.9745...),  gamma_*(s_H) = {gamma_star(sH):.8f}")
    thb = 1 / 8
    for Lam in (1e8, 1e9, 1e10, 1e12, 1e16, 1e20):
        logX0m = Lam - 1e-300   # log X0^- = Lambda - O(e^{-0.98 Lambda})
        worst_empty = -1e300; worst_cond = 1e300; worst_cond_at = None; worst_lam = 1e300
        worst_u0 = 1e300; n = 0
        l_std = math.sqrt((7.5 * Lam + math.log(4)) / 4)
        # grid in s from -log Lambda (z = X0) to well past l_std, plus a few huge l
        s_vals = [-math.log(Lam) + 0.01 * i for i in range(int((math.log(Lam) + sH + 3) / 0.01))]
        s_vals += [sH - 1e-12, sH - 1e-9, sH - 1e-6, sH + 1e-9, sH + 1e-6, sH + 1e-3] + [sH + 0.001 * i for i in range(1, 2001)]
        s_vals += [l_std - 2 * math.log(Lam) + d for d in (-5, -1, -0.1, 0, 0.1, 1, 5)]
        s_vals += [math.log(x) - 2 * math.log(Lam) for x in (1e5, 1e6, 1e8, 1e12)]
        for s in s_vals:
            l = s + 2 * math.log(Lam)
            if l < math.log(Lam - 1): continue
            p = params(Lam, l)
            if s <= sH:
                worst_empty = max(worst_empty, p['logy'] - logX0m)
                continue
            # sup over [u, 2u]: scales L and L + log 2
            p2 = params(Lam, l, dl=math.log(2))
            logy = max(p['logy'], p2['logy'])
            log2y = logy + math.log(2)
            logu0 = math.log(thb) + l - math.log(log2y)
            rhs = log2y + (p['logM1'] + 6 * l - math.log(2)) + 4 * l
            log_lhs = math.log(0.9) + logu0 + math.log(logu0)
            n += 1
            ratio = math.exp(min(700, log_lhs - math.log(rhs)))
            u0 = math.exp(min(700, logu0))
            if ratio < worst_cond:
                worst_cond, worst_cond_at = ratio, s
            lam_v = max(22.6 * Lam, 12 * l * l + 9 * l + 8)
            worst_lam = min(worst_lam, lam_v - log2y)
            worst_u0 = min(worst_u0, math.exp(min(700, logu0 - math.log(2 * Lam))))
            assert logu0 >= math.log(100) and math.log(math.log(log2y)) <= math.log(1.79) + logu0
        print(f"Lambda={Lam:.0e}: [s<=s_H] max(log y - log X0^-) = {worst_empty:.1f} (<0 needed);  "
              f"[s>s_H] {n} pts: min LHS/RHS of twelvetwo = {worst_cond:.3f} at s-s_H={worst_cond_at - sH:.4f}; "
              f"min(lambda(v) - log 2y) = {worst_lam:.3e}; min u0/(2 Lambda) = {worst_u0:.2f}")
        # Lemma ZA constants
        u_star = Lam * math.exp(sH) / 22.6
        v0 = Lam ** 2 * math.exp(sH)
        lv0 = math.log(v0)
        print(f"   ZA: u_* = {u_star:.4e}, 0.45 u_* log u_* = {0.45 * u_star * math.log(u_star):.4e}, "
              f"22.6Lam - (12 log^2 v0+9log v0+8) = {22.6 * Lam - (12 * lv0 ** 2 + 9 * lv0 + 8):.3e}, "
              f"12.1 l_std^2 / (22.6 Lam) = {12.1 * l_std ** 2 / (22.6 * Lam):.5f}")

if __name__ == "__main__":
    main()
