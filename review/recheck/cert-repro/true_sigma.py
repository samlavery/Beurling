# Non-rigorous sanity check: evaluate Sigma(l, u; tau) of Theorem bs, Step 5 (with T from Step 6) numerically, using
# Dickman's rho from a fine-grid solution of v rho'(v) = -rho(v-1), and compare l*Sigma with the certified lower bounds
# (mine: z2_indep.lS; the script's: bs_cert_arb.S_cell) on small cells containing the point. Expect l*Sigma >= both.
import sys, math
sys.path.insert(0, '/tmp/rhscratch/cert-repro/mine'); sys.path.insert(0, '/tmp/rhscratch/cert-repro/src/certificates/bs-cert')
B, KP, KV = 11.0, 2.2, 3.2
M = 1000; H = 1.0 / M              # rho via v rho(v) = int_{v-1}^v rho (positive terms only: stable), per-unit rescaling
VMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 1100
LR = [0.0] * (VMAX + 2)            # log rho(k)
SIG = [[1.0] * (M + 1)]            # sigma_k(j) = rho(k + j/M)/rho(k); interval 0: rho = 1
for k in range(1, VMAX + 1):
    prev = SIG[k - 1]
    LR[k] = LR[k - 1] + math.log(prev[M])
    ratio = 1.0 / prev[M]          # rho(k-1)/rho(k)
    suf = [0.0] * (M + 1)          # suf[j] = int_{k-1+j/M}^{k} sigma_{k-1}, trapezoid
    for j in range(M - 1, -1, -1): suf[j] = suf[j + 1] + 0.5 * H * (prev[j] + prev[j + 1])
    cur = [1.0] * (M + 1); pre = 0.0
    for j in range(1, M + 1):
        v = k + j * H
        cur[j] = (ratio * suf[j] + pre + 0.5 * H * cur[j - 1]) / (v - 0.5 * H)
        pre += 0.5 * H * (cur[j - 1] + cur[j])
    SIG.append(cur)
def logrho(v):
    if v <= 1: return 0.0
    k = int(v); t = (v - k) * M; j = int(t); a = t - j
    if j >= M: j, a = M - 1, 1.0
    c = SIG[k]
    return LR[k] + math.log((1 - a) * c[j] + a * c[j + 1])
def r(v): return math.exp(logrho(v - 1) - logrho(v)) / v
print('check rho(3) = %.8f (0.04860838), rho(10) = %.6e (2.770172e-11)' % (math.exp(logrho(3)), math.exp(logrho(10))))

def sigma(l, u, tau):
    u0 = l ** 0.25; kap = 4 * tau + 1500
    def U(x): return x ** 0.25 * (1 + math.sqrt(2 * math.log(x / tau) + 4))
    def Q(x, w): return B * (1 + w) ** 3 * math.log(2 + w) / x + max(0.0, w - x ** 0.25) ** 2 / (2 * math.sqrt(x))
    Qlu = Q(l, u); lr = logrho(u - 1)
    def D(w):
        m = l * w / (1 + w); return Q(m, w) - Qlu - kap / (w * l)
    def eta(w):
        m = l * w / (1 + w); L = math.log(2 + w); yy = max(0.0, w - m ** 0.25)
        dmA = B * (1 + w) ** 3 * L / m ** 2
        dma = yy / (4 * m ** 1.25) + yy * yy / (4 * m ** 1.5)
        dwA = B * (3 * (1 + w) ** 2 * L + (1 + w) ** 3 / (2 + w)) / m
        dwa = yy / math.sqrt(m)
        return kap / m ** 2 + dmA + dma + (1 + w) ** 2 / l * (dwA + dwa)
    wlo = u - 1; top = min(U(l), u + 60.0)
    n = 40000; hw = (top - wlo) / n
    M1 = E2 = E3 = 0.0
    for i in range(n + 1):
        w = wlo + i * hw; wt = 1 if 0 < i < n else 0.5
        dens = math.exp(logrho(w - 1) - lr) / w
        m = l * w / (1 + w)
        ind = w <= U(m)
        d = D(w)
        M1 += wt * dens * (math.expm1(d) if ind else -1.0)
        if ind:
            g = dens * w * math.exp(d)
            E2 += wt * g * (1 + w) / w
            E3 += wt * g * eta(w) / w
    M1 *= hw; E2 *= hw * KP / l; E3 *= hw * 2 * KP
    E1 = 2 * KP * (1 + wlo) ** 2 * math.exp(logrho(wlo - 1) - lr + D(wlo)) / (wlo * l)
    us = U(l) + 0.5; aV = 4 * KV * us * us * math.log(us + 2) / l
    yv = math.log(l / tau)
    T = math.exp(kap / l + aV + yv - max(0.0, u - u0) ** 2 / (2 * math.sqrt(l)) - r(u - 1) * (U(l) - u + 1.5))
    return l * (-(M1 + E1 + E2 + E3 + T)), dict(lM1=l * M1, lE1=l * E1, lE2=l * E2, lE3=l * E3, lT=l * T)

import z2_indep as Z, dick
dick.build(300000)
from bs_cert_arb import S_cell
pts = [(1.2e10, 160.0), (3.05e9, 2.2), (3.05e9, 535.0), (3.05e9, 1005.0), (1e12, 1050.0), (8.5e10, 205.0), (1e12, 30.0)]
for l, u in pts:
    for tau in (1e8, l / 30):
        if l / tau < 30 - 1e-9: continue
        ts, parts = sigma(l, u, tau)
        la, lb = l * 0.999, l * 1.001; ua, ub = u - 0.01, u + 0.01
        mine = float(Z.lS(la, lb, ua, ub, False).lower())
        scr = S_cell(la, lb, ua, ub, False)[0] * la
        print('l=%.3g u=%g tau=%.3g: l*Sigma(num)=%.4g  mine=%.4g  script=%.4g  ok=%s' % (l, u, tau, ts, mine, scr, ts >= mine and ts >= scr),
              {k: '%.3g' % v for k, v in parts.items()})
