# T5: the Lemma-M step |rho_edge - g|(x) <= sum_n |c_n(x)|/n * sup_n |D(x/n)| <= (log x + 1) sup_{u<=x}|D(u)|
import sys, math, random, bisect
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
import t3_realised as T3
for (X0, k, H, umax, variant, eps, seed) in [(100, 0.2, 2, 4e6, 'drift', 0.1, 7), (100, 0.2, 2, 4e6, 'add', 0.15, 7),
                                             (1000, 0.05, 4, 3e7, 'drift', 0.025, 3), (1000, 0.05, 4, 3e7, 'add', 0.15, 3)]:
    M = T3.Model(X0, k, H, umax, variant, eps, seed); toy = M.toy
    rnd = random.Random(21)
    u0 = 2 * X0 * toy.X0m / (1 + k)
    worst1 = worst2 = 0.0
    for _ in range(25):
        x = math.exp(rnd.uniform(math.log(u0), math.log(umax)))
        diff = M.resolvent_real(toy.mu_edge, x) - M.g(x)
        # collect |c_n|/n and D(x/n)
        terms = []
        nmax = x / toy.X0m
        for n in toy.smooth:
            if n > nmax: break
            if toy.mu[n] and toy.chi_rat(n, x): terms.append((1.0 / n, M.D(x / n)))
        for el in M.Er[:bisect.bisect_right(M.Erv, nmax)]:
            if M.real.c_lemmaM(el, x): terms.append((1.0 / el[0], M.D(x / el[0])))
        tri = sum(w * abs(d) for w, d in terms)
        supD = max(abs(d) for w, d in terms)
        lm = (math.log(x) + 1) * supD
        worst1 = max(worst1, (abs(diff) - 1e-15) / tri if tri > 1e-15 else 0)
        worst2 = max(worst2, tri / lm if lm else 0)
    print(f"X0={X0} k={k} {variant}: max |rho_edge-g|/triangle = {worst1:.3f}; max triangle/((log x+1) sup|D|) = {worst2:.3f}")
