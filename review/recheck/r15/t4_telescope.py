# Lemma margin(b) Step 3 and (d)(iii): symmetric mixed telescope, one-replacement Abel bounds, summation over the
# other variables, diagonal, decision-order mismatch, partial windows.  h in {f0*1, g}.
import sys, math, random, itertools
sys.argv = ['x', '100']
sys.path.insert(0, '/tmp/rhscratch/r15')
from toy_ops import *

which = os.environ.get('WHICH', 'f0') if False else None
import os
which = os.environ.get('WHICH', 'f0')

_gc = {}
def g(x):
    v = _gc.get(x)
    if v is None:
        v = resolventQ(x, mu_edge, cutoff=X0)
        _gc[x] = v
    return v

h = f0 if which == 'f0' else g
supp_lo = X0 if which == 'f0' else 2 * X0 / (1 + kappa)   # h vanishes below this

QL = [float(p) for p in PR if p >= X0]          # rational large primes
RL = sorted(JITV)                                  # realised large (jittered) primes
Dset = [d for d in range(1, MMAX + 1) if gpf[d] < X0]

def direct_val(u):
    """sum over realised w (value-order filter) minus sum over rational m (sharp filter)."""
    sR = 0.0
    for (w, tau, pval, idxs, sqf) in get_els():
        if w > u / X0m:
            break
        if w < 1.5:
            continue
        if pval < u / w and u / w >= X0m:
            sR += h(u / w) / w
    sQ = 0.0
    for m in range(2, int(u / X0) + 1):
        if gpf[m] < u / m:
            sQ += h(u / m) / m
    return sR - sQ

def direct_dec(u):
    return Kpt(u, h, order='dec') - Kpt(u, h, order='val')

def bnd_b(u, mj, Mp):
    filt = math.sqrt(u / mj) if Mp * Mp * mj <= u else u / (Mp * mj)
    return min(filt, u / (supp_lo * mj))

def one_repl(u, mj, Mp):
    """Return (delta, abel_exact, B1, B2, B3, TVg, suph, b) for the replacement of one variable."""
    b = bnd_b(u, mj, Mp)
    if b <= X0m:
        return None
    def G(t):
        return h(u / (mj * t)) / (mj * t)
    i1 = bisect.bisect_left(RL, b); i0 = bisect.bisect_left(RL, X0m)
    j1 = bisect.bisect_left(QL, b)
    sR = sum(G(p) for p in RL[i0:i1])
    sQ = sum(G(p) for p in QL[:j1])
    delta = sR - sQ
    # merged atoms, theta-difference
    atoms = sorted([(p, math.log(p)) for p in RL[i0:i1]] + [(p, -math.log(p)) for p in QL[:j1]])
    if not atoms:
        return (delta, 0.0, 0, 0, 0, 0, 0, b)
    E = 0.0
    Es = []
    for p, e in atoms:
        E += e
        Es.append(E)
    ts = [p for p, e in atoms]
    phi = [G(t) / math.log(t) for t in ts]
    a = [1.0 / (mj * t * math.log(t)) for t in ts]
    gt = [h(u / (mj * t)) for t in ts]
    k = len(ts)
    abel = phi[-1] * Es[-1] - sum(Es[i] * (phi[i + 1] - phi[i]) for i in range(k - 1))
    B1 = abs(phi[-1] * Es[-1])
    suph = max(abs(v) for v in gt)
    B2 = sum(abs(Es[i]) * abs(gt[i + 1]) * abs(a[i + 1] - a[i]) for i in range(k - 1))
    TVg = sum(abs(gt[i + 1] - gt[i]) for i in range(k - 1))
    B3 = sum(abs(Es[i] * a[i]) * abs(gt[i + 1] - gt[i]) for i in range(k - 1))
    return (delta, abel, B1, B2, B3, TVg, suph, b)

def K5_of(u):
    # sup over t in [X0m, u/X0] of |Delta_psi(t)|/(t log^2 t); also theta version
    xs = [t for t in EVP_x if t <= u / X0] + [u / X0]
    k5p = max(abs(Dpsi(t)) / (t * math.log(t) ** 2) for t in xs if t >= X0m)
    k5t = max(abs(Dth(t)) / (t * math.log(t) ** 2) for t in xs if t >= X0m)
    return k5p, k5t

def telescope(u):
    tot = 0.0; diag_tot = 0.0
    abel_err = 0.0; chain_viol = 0
    sumB = 0.0           # sum over one-replacements of (B1+B2+B3) / r!
    sum_paper = 0.0      # same with the paper's analytic chain using K5
    k5p, k5t = K5_of(u)
    K5 = k5t
    nrep = 0
    for d in Dset:
        if d * X0m > u / X0:
            break
        Pd = gpf[d] if d > 1 else 1
        # r = 1
        res = one_repl(u, d, Pd)
        if res:
            delta, abel, B1, B2, B3, TVg, suph, b = res
            tot += delta
            abel_err = max(abel_err, abs(abel - delta))
            if abs(delta) > B1 + B2 + B3 + 1e-14:
                chain_viol += 1
            sumB += B1 + B2 + B3
            nrep += 1
        # r = 2 : multisets {p1<=p2} realised minus rational
        lim = u / (X0 * d)        # d p1 p2 <= u/X0 roughly (support)
        if X0m * X0m > lim:
            continue
        def G2(p1, p2):
            w = d * p1 * p2
            if max(p1, p2, Pd) * w < u and u / w >= supp_lo:
                return h(u / w) / w
            return 0.0
        RLs = [p for p in RL if p * X0m <= lim]
        QLs = [p for p in QL if p * X0 <= lim]
        msR = sum(G2(RLs[i], RLs[j]) for i in range(len(RLs)) for j in range(i, len(RLs)))
        msQ = sum(G2(QLs[i], QLs[j]) for i in range(len(QLs)) for j in range(i, len(QLs)))
        ordR = sum(G2(p, q) for p in RLs for q in RLs)
        ordQ = sum(G2(p, q) for p in QLs for q in QLs)
        dR = sum(G2(p, p) for p in RLs) / 2
        dQ = sum(G2(p, p) for p in QLs) / 2
        assert abs(msR - (ordR / 2 + dR)) < 1e-12 and abs(msQ - (ordQ / 2 + dQ)) < 1e-12
        tot += msR - msQ
        diag_tot += abs(dR) + abs(dQ)
        # telescope: R x R - R x Q (replace 2nd, first realised fixed) + R x Q - Q x Q (replace 1st, 2nd rational fixed)
        tsum = 0.0
        for p1 in RLs:
            res = one_repl(u, d * p1, max(p1, Pd))
            if res:
                tsum += res[0]
                if abs(res[0]) > res[2] + res[3] + res[4] + 1e-14:
                    chain_viol += 1
                sumB += (res[2] + res[3] + res[4]) / 2
                nrep += 1
        for p2 in QLs:
            res = one_repl(u, d * p2, max(p2, Pd))
            if res:
                tsum += res[0]
                if abs(res[0]) > res[2] + res[3] + res[4] + 1e-14:
                    chain_viol += 1
                sumB += (res[2] + res[3] + res[4]) / 2
                nrep += 1
        assert abs(tsum - (ordR - ordQ)) < 1e-12, (tsum, ordR - ordQ)
    return tot, diag_tot, abel_err, chain_viol, sumB, K5, k5p, nrep

rng = random.Random(3)
us = [rng.uniform(2.0e5, 4.2e6) + 0.37 for _ in range(int(os.environ.get('NU', '12')))]
us += [1.0e6 + 0.37, 2.0e6 + 0.37, 4.1e6 + 0.37]
print("which =", which)
for u in sorted(us):
    dv = direct_val(u)
    tot, diag, abel_err, cv, sumB, K5, k5p, nrep = telescope(u)
    mism = direct_dec(u)
    L = math.log(u)
    sd = sum(1.0 / d for d in Dset)  # sum over all X0-smooth d <= MMAX
    ellu = sum(1.0 / p for p in RL if p <= u) 
    ellq = sum(1.0 / p for p in QL if p <= u)
    suph = 1.0 / math.log(X0) if which == 'f0' else max(abs(g(y)) for y in [2 * X0 / (1 + kappa) * (1 + i / 50.0) for i in range(1, 400)])
    cd = 1 + 2 / math.log(X0m)
    if which == 'f0':
        closed = K5 * (2 * L + 0.5 * cd * L * L) * suph * sd * (1 + max(ellu, ellq))
    else:
        # paper's (iii) form: boundary + differences of 1/(t log t) + variation of g, with TV(g on [a,b]) <= Cg (log(b/a)+1)
        closed = None
    print(f"u={u:11.2f} direct(val)={dv:+.3e} telescope={tot:+.3e} |diff|={abs(dv-tot):.1e} abel_err={abel_err:.1e} "
          f"chain_viol={cv} sumB={sumB:.3e} diag={diag:.2e} K5th={K5:.2e} K5psi={k5p:.2e} mismatch={mism:+.2e} "
          + (f"closed={closed:.3e}" if closed else "") + f" reps={nrep}")
