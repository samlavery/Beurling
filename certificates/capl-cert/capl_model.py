# Model for Theorem caplw (Section 6 of the paper). All quantities in log space; l = log L, L = log z, Lam = log X0.
import math
LAM = 1e8; THETA_B = 1/8; SLACK = 1.0
def lse(a, b): m = max(a, b); return m + math.log(math.exp(a - m) + math.exp(b - m))
def base(l, lam=LAM):
    """log L, log D, log r0, log(pi) with pi = r0*D (worst-case labels)."""
    # degree cap D = log 2z / log X0^- (paper, Section 6.4/6.6); the e^{-0.98 Lam} difference between log X0^- and Lam
    # is below double precision, so D = (L + log 2)/Lam
    logD = (math.log(math.exp(l) + math.log(2)) if l < 700 else l) - math.log(lam)
    r0 = None
    logr0 = math.log(math.exp(l - math.log(3*l)) + 4) if l < 700 else l - math.log(3*l)   # r0 = ceil(L/(3l)) + 3 <= L/(3l) + 4
    return logD, logr0, logr0 + max(logD, 0.0)
def j_of(logc, l, lam=LAM):
    """largest j with log N(r0, D, j) < log c; N <= e (r0(D+1))^{2j+1}."""
    logD, logr0, _ = base(l, lam)
    a = logr0 + lse(logD, 0.0)
    j = math.floor(((logc - 1)/a - 1)/2)
    return max(j, -1)
def rhs_over_L(l):
    """(L + 10 log L + 10)/L"""
    return SLACK*(1 + (10*l + 10)*math.exp(-l) if l < 700 else 1.0)
def highdeg_ok(logc, l_hi, l_lo, lam=LAM):
    """High-degree-row criterion (Step 2 of the proof of Theorem caplw) on the cell [l_lo, l_hi] with capacity c fixed (worst corner l_hi; degree cap at l_lo)."""
    logD, logr0, logpi = base(l_hi, lam)
    j = j_of(logc, l_hi, lam)
    if j < 0: return False
    logQ = logc/2
    # D* = max{k : k log(e(m+k)/k) <= log Q}, m = pi; bisection in k (real), conservative upper bound for log binom
    m_log = logpi
    lo, hi = 0.0, 1e300
    def f(k): return k*(1 + lse(m_log, math.log(k)) - math.log(k)) if k > 0 else 0.0
    hi = max(1.0, logQ)  # f(k) >= k so k <= logQ
    if f(hi) <= logQ: kstar = hi
    else:
        for _ in range(200):
            mid = (lo + hi)/2
            if f(mid) <= logQ: lo = mid
            else: hi = mid
        kstar = lo
    Dstar = math.floor(kstar)
    logD_hi_cap = logD   # degree cap D = log 2z/log X0^- at the TOP of the cell (worst corner: upper end of the cell)
    if logD_hi_cap < 700 and Dstar >= math.exp(logD_hi_cap) - 1: return True   # every element has degree <= D*: Cap >= c impossible
    k = Dstar + 1
    row_gain = k*(lam - 1 - (lse(m_log, math.log(k)) - math.log(k))) - math.log(3)   # -log w_row, Lemma rowweights(b)
    gain_over_L = (1 + j)*row_gain*(math.exp(-l_hi) if l_hi < 700 else 0.0)
    return gain_over_L >= rhs_over_L(l_hi)
def rankin_rho(u):
    """log(1/rho)-type saving per row from Psi(Y,X0) <= Y exp(-0.9 u log u), valid for u >= 1e4 (Lemma rowweights(c))."""
    return 0.9*u*math.log(u) if u >= 1e4 else 0.0
def dickman_ok(logc, l_hi, l_lo, lam=LAM):
    """sec 16.16 rows (any degree; k = 1 dominates) on the cell; g lower bound uses D at l_lo for the Dickman part."""
    logD_hi, logr0, logpi = base(l_hi, lam)
    j = j_of(logc, l_hi, lam)
    if j < 0: return False
    logD_lo = l_lo - math.log(lam)
    if l_hi < 700:
        L = math.exp(l_hi)
        D_lo = math.exp(logD_lo)
        g = lam - math.log(3) - logpi + rankin_rho(D_lo - 1)
        return (1 + j)*g >= SLACK*(L + 10*l_hi + 10)
    else:  # g/L >= 0.9 (D_lo-1)log(D_lo-1)/L ~ 0.9 (logD - small)/lam * e^{l_lo - l_hi}
        g_over_L = 0.9*(logD_lo - 1.0)/lam*math.exp(l_lo - l_hi)
        return (1 + j)*g_over_L >= SLACK
def logy_of(logc, l):
    logM1 = logc + math.log(2)
    lH = max(8*l*l, 2*logM1)
    logL0 = max(5*l, math.log(48) - 2*math.log(0.15) + logM1 + 3*l)   # L0 = max(L^5, 48 M1 L^3 / c'^2), c' = 0.15
    return lH + logL0 + 6*l + math.log(2), logM1
def lemmaP_ok(logc, l_hi, l_lo, lam=LAM, theta_b=THETA_B):
    """A empty (y <= X0) at l_hi, or (12.2) at worst corners."""
    logy, logM1 = logy_of(logc, l_hi)
    if logy <= lam: return True
    logu0 = math.log(theta_b) + l_lo - math.log(logy)
    if logu0 < math.log(100): return False   # (12.2) requires u0 >= 100
    lhs = math.log(0.9) + logu0 + math.log(logu0)
    rhs = math.log(logy + (logM1 + 6*l_hi - math.log(2)) + 4*l_hi)
    return lhs >= rhs + math.log(SLACK)
