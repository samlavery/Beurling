import sys, math, pickle, random
sys.path.insert(0, "/tmp/rhscratch/r30/indep"); sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from multiprocessing import Pool
from flint import arb, ctx
import sigma_true as ST
from indep_S import S_point
def Ubar(l): return l ** 0.25 * (1 + math.sqrt(2 * math.log(l / 1e8) + 4))
def E1_check(l, u, tau, P):
    # D(u-1) <= betaI - alpha, in 200-bit arb, exact a(m,w), A(m,w), kappa = 4 tau + 1500
    ctx.prec = 200
    L, Uu, kap = arb(l), arb(u), 4 * arb(tau) + 1500
    def Q(x, w):
        X = w - x.root(4); X = X if X > 0 else arb(0)
        return 11 * (1 + w) ** 3 * (2 + w).log() / x + X * X / (2 * x.sqrt())
    w = Uu - 1; m = L * w / (1 + w)
    Dw = Q(m, w) - Q(L, Uu) - kap / (w * L)
    return (P['bI'] - P['alpha']) - Dw          # must be > 0
def check_point(args):
    tag, cell, l, u, taus = args
    out = []
    r, r0 = ST.R.r(u), (ST.R.r(u - 1) if u > 2 else 1.0)
    S, P = S_point(l, u, r, r0, r0, parts=True)
    Slo = float(S.lower())
    for tau in taus:
        if not (u <= ST.U(l, tau)) or l < 30 * tau: continue
        c = ST.components(l, u, tau)
        e1m = float(E1_check(l, u, tau, P).lower())
        out.append(dict(tag=tag, cell=cell, l=l, u=u, tau=tau, S=Slo, scell=cell[5], Sig=c['Sigma'], SigC0=c['SigmaC0'],
                        dM=float(P['Mm1'].mid()) - c['Mm1'], dE2=float(P['E2'].mid()) - c['E2'], dE3=float(P['E3'].mid()) - c['E3'],
                        dT=float(P['T'].mid()) - c['Tc0'], E1marg=e1m, Mref=abs(c['Mm1']) + 1e-300, E2ref=c['E2'], E3ref=c['E3'], Tref=c['Tc0']))
    return out
def init(): ST.load()
if __name__ == "__main__":
    res = pickle.load(open("/tmp/rhscratch/r30/indep/leaves.pkl", "rb"))
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    picks = []
    # boundary / seam cells: in every 10th band + first/last bands + worst band
    worst_band = min(range(len(res)), key=lambda i: min(c[5] * c[0] for c in res[i][2]))
    special = sorted(set(list(range(0, len(res), 10)) + [0, 1, len(res) - 2, len(res) - 1, worst_band]))
    for i in special:
        lv = res[i][2]
        uc = sorted([c for c in lv if not c[4]], key=lambda c: c[2]); vc = sorted([c for c in lv if c[4]], key=lambda c: c[2])
        for c, t in ((uc[0], "u-bottom"), (uc[-1], "u-seam"), (vc[0], "v-seam"), (vc[-1], "v-top"), (min(lv, key=lambda c: c[5] * c[0]), "band-worst")):
            picks.append((t, c))
    for _ in range(700):
        i = random.randrange(len(res)); c = random.choice(res[i][2]); picks.append(("random", c))
    tasks = []
    for t, c in picks:
        la, lb, xa, xb, vm = c[:5]
        pts = []
        for k in range(4):
            if k == 0: tl, tu = 0.0, 0.0
            elif k == 1: tl, tu = 1.0, 1.0
            else: tl, tu = random.random(), random.random()
            l = la * (lb / la) ** tl; l = min(max(l, la), lb)
            if vm:
                u = l ** 0.25 + (xa + tu * (xb - xa))
            else:
                u = xa + tu * (xb - xa)
            u = min(u, Ubar(l) * (1 - 1e-12))
            if u < 2: continue
            pts.append((l, u))
        for (l, u) in pts:
            taus = [1e8, 10 ** random.uniform(8, math.log10(l / 30)), l / 30 * (1 - 1e-9)]
            tasks.append((t, c[:6], l, u, taus))
    print("points", len(tasks), flush=True)
    with Pool(10, initializer=init) as pool: out = [x for o in pool.map(check_point, tasks, chunksize=4) for x in o]
    pickle.dump(out, open(f"/tmp/rhscratch/r30/indep/sample_out_{sys.argv[1] if len(sys.argv)>1 else 3}.pkl", "wb"))
    n = len(out)
    v_cell = [o for o in out if not (o['S'] >= o['scell'])]
    v_sig = [o for o in out if not (o['S'] <= o['SigC0'] + 1e-9 * abs(o['SigC0']))]
    v_pos = [o for o in out if not (o['SigC0'] > 0 and o['S'] > 0)]
    v_M = [o for o in out if o['dM'] < -1e-9 * o['Mref']]
    v_E2 = [o for o in out if o['dE2'] < -1e-9 * o['E2ref']]
    v_E3 = [o for o in out if o['dE3'] < -1e-9 * o['E3ref']]
    v_T = [o for o in out if o['dT'] < -1e-9 * o['Tref']]
    v_E1 = [o for o in out if not (o['E1marg'] > 0)]
    print(f"(l,u,tau) evaluations: {n}")
    print(f"  S_point >= certified cell lower bound s_cell : violations {len(v_cell)}")
    print(f"  S_point <= Sigma_true (C0 tail)            : violations {len(v_sig)}")
    print(f"  Sigma_true > 0 and S_point > 0              : violations {len(v_pos)}")
    print(f"  majorants: M-1 {len(v_M)}, E1 {len(v_E1)}, E2 {len(v_E2)}, E3 {len(v_E3)}, T {len(v_T)} violations")
    ratio = min(o['S'] / o['SigC0'] for o in out)
    print(f"  min S/Sigma_true = {ratio:.4f};  min l*S_point = {min(o['S'] * o['l'] for o in out):.4g};  min l*Sigma_true = {min(o['SigC0'] * o['l'] for o in out):.4g}")
    print(f"  min (S_point - s_cell)/|s_cell| = {min((o['S'] - o['scell']) / abs(o['scell']) for o in out):.3g}")
    for nm, key, ref in (("M-1", "dM", "Mref"), ("E2", "dE2", "E2ref"), ("E3", "dE3", "E3ref"), ("T", "dT", "Tref")):
        m = min(out, key=lambda o: o[key] / o[ref] if o[ref] > 0 else math.inf)
        print(f"  tightest {nm}: rel slack {m[key] / m[ref]:.3g} at l={m['l']:.4g} u={m['u']:.6g} tau={m['tau']:.3g}")
    m = min(out, key=lambda o: o['E1marg']); print(f"  tightest E1 exponent margin (betaI-alpha)-D(u-1) = {m['E1marg']:.3g} at l={m['l']:.4g} u={m['u']:.6g}")
    from collections import Counter
    print("  tags:", dict(Counter(o['tag'] for o in out)))
    for o in (v_cell + v_sig + v_pos + v_M + v_E1 + v_E2 + v_E3 + v_T)[:10]: print("VIOL", o)
