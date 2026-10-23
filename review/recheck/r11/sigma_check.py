"""#65 context: Rankin exponents actually used where the absorbed set is nonempty (s > s_H).
  Lemma P (v):   Y = 2yh,  u_* = log(2yh)/log(2y) = 1 + u0,  sigma_P = 1 - log(u_*)/log(2y)
  Lemma ZA:      Y = x (height of the counting function), log 2y <= lambda(v) majorant used:
                 sigma_ZA = 1 - log(v/lambda(v))/lambda(v)  (v = log x), and with the true y: 1 - log(L/log2y)/log2y
  Lemma rhoA(b): cofactor sum over 2y-smooth w >= Y/y(Y), u = L/log 2y, sigma = 1 - log u/log 2y.
Grid as in params_twelvetwo.py (theta_b in {1/8, theta_1/2})."""
import math, sys
sys.path.insert(0, '/tmp/rhscratch/r11/checks')
import params_twelvetwo as P

for Lam in (1e8, 1e9, 1e10, 1e12, 1e16, 1e20):
    l_std = math.sqrt((7.5 * Lam + math.log(4)) / 4)
    svals = [P.sH + 1e-9, P.sH + 1e-6] + [P.sH + 0.001 * i for i in range(1, 3001)]
    svals += [l_std - 2 * math.log(Lam) + d for d in (-5, -1, 0, 1, 5)]
    svals += [math.log(x) - 2 * math.log(Lam) for x in (1e5, 1e6, 1e8, 1e12, 1e15, 1e30, 1e100)]
    minP = minZA = minZAlam = minR = 9.0
    for s in svals:
        l = s + 2 * math.log(Lam)
        if s <= P.sH or l < math.log(Lam): continue
        p = P.params(Lam, l); p2 = P.params(Lam, l, dl=math.log(2))
        log2y = max(p['logy'], p2['logy']) + math.log(2)
        for thb in (1 / 8, (0.5 - 1e-4) / 2):
            logu0 = math.log(thb) + l - math.log(log2y)
            # u_* = 1 + u0 ; log u_* = log1p(u0) computed in log space
            logus = logu0 + math.log1p(math.exp(-logu0)) if logu0 < 700 else logu0
            minP = min(minP, 1 - logus / log2y)
        # ZA at Y = x (scale height): u = L/log 2y
        logu = l - math.log(log2y)
        minZA = min(minZA, 1 - logu / log2y)
        lam_v = max(22.6 * Lam, 12 * l * l + 9 * l + 8)
        minZAlam = min(minZAlam, 1 - (l - math.log(lam_v)) / lam_v)
        minR = min(minR, 1 - logu / log2y)
    print(f"Lambda={Lam:.0e}: min sigma  LemmaP(v)@Y=2yh: {minP:.6f}   ZA@Y=x (true y): {minZA:.6f}   "
          f"ZA (lambda majorant): {minZAlam:.6f}   rhoA(b): {minR:.6f}")
