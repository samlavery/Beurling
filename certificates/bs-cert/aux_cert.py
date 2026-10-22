# Certified one-variable checks for Theorem bs (Appendix B) (outward-rounded intervals from bs_cert):
#  (1) positivity of c_0(u), u >= 27:  5 log(1+u)[3(1-1/r(u)) - (1+u)^3 log(2+u)/(u^3 log(1+u)) - 144(1+u)^2 log(2+u)/(u^3 r0^2 log(1+u))]
#                      - 2 r(u-1) - (u+1)/u^2  >=  log(1+u),   with r -> r_low, r0 -> r_low(u-1), r(u-1) -> r_up.
#  (2) Lemma V one-step, closed form, u in [1, L], L >= 100, worst case L = max(100, u) (L*Q_V increasing in L):
#      L(1-e^{-alpha}) * max(1/2, 1 - 1/r_low(u-1)) - 2 K_M r_up(u) - 15 e^{-0.4 L}  >  0   (last term: prime powers p^k > z),
#      alpha = 4K(log(u+1) + (u-1)/(u+1))/L.
import sys, math
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from bs_cert import I, ilog, iexp, iexpm1, r_low, r_up, lo_, hi_
def cA_cell(ua, ub):
    u = I(ua, ub)
    r = I(r_low(ua), r_up(ub)); r0l = r_low(ua - 1); r0u = r_up(ub - 1)
    L1, L2 = ilog(1 + u), ilog(2 + u)
    u3 = u * u * u
    jA = 3 * (1 - 1 / r) - (1 + u) * (1 + u) * (1 + u) * L2 / (u3 * L1) - 144 * (1 + u) * (1 + u) * L2 / (u3 * (r0l * r0l) * L1)
    val = 5 * L1 * jA - 2 * r0u - (u + 1) / (u * u) - L1
    return lo_(val)
K, KM = 3.2, 1.01
def lemV_cell(ua, ub):
    u = I(ua, ub)
    L = I(max(100.0, ua), max(100.0, ub))
    alpha = 4 * K * (ilog(u + 1) + (u - 1) / (u + 1)) / L
    E = max(0.5, 1 - 1 / r_low(ua - 1)) if ua >= 2 else 0.5
    ru = r_up(ub) if ub > 1 else 1.0
    val = L * (-iexpm1(-alpha)) * E - 2 * KM * ru - 15 * iexp(-0.4 * L)
    return lo_(val)
def cover(f, a, b, ratio, name):
    cells, x, worst, n, stack = [], a, math.inf, 0, []
    while x < b:
        y = min(x * ratio, b); stack.append((x, y, 0)); x = y
    fails = 0
    while stack:
        xa, xb, d = stack.pop(); v = f(xa, xb); n += 1
        if v > 0: worst = min(worst, v); continue
        if d > 30: fails += 1; continue
        m = 0.5 * (xa + xb); stack += [(xa, m, d + 1), (m, xb, d + 1)]
    print(f"{name}: [{a:g},{b:g}] cells={n} failed={fails} min certified margin={worst:.4g}")
cover(cA_cell, 27.0, 4e5, 1.001, "c_0 >= K'u^2 log(1+u)")
cover(lemV_cell, 1.0, 1e6, 1.001, "Lemma V one-step (L*Q_V, L = max(100,u))")
