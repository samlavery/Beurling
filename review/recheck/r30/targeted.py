import sys, math, pickle, random, bisect
sys.path.insert(0, "/tmp/rhscratch/r30/indep"); sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from multiprocessing import Pool
from flint import arb
import sigma_true as ST
from indep_S import S_point
from sample_check import E1_check, Ubar
res = pickle.load(open("/tmp/rhscratch/r30/indep/leaves.pkl", "rb"))
bl = [r[0][0] for r in res]
def find_cell(l, u):
    i = max(0, bisect.bisect_right(bl, l) - 1)
    cands = []
    for j in (i - 1, i, i + 1):
        if 0 <= j < len(res):
            for c in res[j][2]:
                if not (c[0] <= l <= c[1]): continue
                if not c[4]:
                    if c[2] <= u <= c[3]: cands.append(c)
                else:
                    v = arb(u) - arb(l).root(4)
                    if arb(c[2]) <= v and v <= arb(c[3]): cands.append(c)
    return cands
def task(args):
    tag, l, u = args
    cs = find_cell(l, u)
    if not cs: return [dict(tag=tag, l=l, u=u, err="NO CELL")]
    r, r0 = ST.R.r(u), (ST.R.r(u - 1) if u > 2 else 1.0)
    S, P = S_point(l, u, r, r0, r0, parts=True); Slo = float(S.lower())
    out = []
    for tau in (1e8, math.sqrt(1e8 * l / 30), l / 30):
        if u > ST.U(l, tau): continue
        c = ST.components(l, u, tau)
        out.append(dict(tag=tag, l=l, u=u, tau=tau, S=Slo, scell=min(x[5] for x in cs), Sig=c['SigmaC0'],
                        okM=float(P['Mm1'].mid()) >= c['Mm1'] - 1e-9 * abs(c['Mm1']), okE2=float(P['E2'].mid()) >= c['E2'] * (1 - 1e-9),
                        okE3=float(P['E3'].mid()) >= c['E3'] * (1 - 1e-9), okT=float(P['T'].mid()) >= c['Tc0'] * (1 - 1e-9),
                        E1m=float(E1_check(l, u, tau, P).lower()), T=c['Tc0'], Tb=float(P['T'].mid())))
    return out
def init(): ST.load()
if __name__ == "__main__":
    random.seed(5); tasks = []
    Ls = [3e9, 3e9 * 1.05, 1e18, 1e18 / 1.0000001] + [10 ** random.uniform(math.log10(3e9), 18) for _ in range(60)] + [b[0][1] for b in res[::37]]
    for l in Ls:
        u0 = l ** 0.25; Ub = Ubar(l); U30 = u0 * (1 + math.sqrt(2 * math.log(30) + 4))
        pts = [("u=2", 2.0), ("u=2+", 2.0 + 1e-9), ("u=3", 3.0), ("u-1=2", 3.0 + 1e-12), ("u=40", 40.0), ("split", 0.5 * u0)]
        for eps in (-1e-6, 0.0, 1e-6):
            # v + c_u = 0  <=>  u = u0 - u0/(3u): solve u^2 - u0 u + u0/3 = 0, larger root
            ush = 0.5 * (u0 + math.sqrt(u0 * u0 - 4 * u0 / 3)); pts.append(("v=-c_u", ush + eps))
            # v - 1 + c_u = 0  <=>  u = u0 + 1 - u0/(3u)
            ua = ush + 1; ua = 0.5 * ((u0 + 1) + math.sqrt((u0 + 1) ** 2 - 4 * u0 / 3)); pts.append(("v=1-c_u", ua + eps))
            pts.append(("u=u0", u0 + eps)); pts.append(("u=U30", U30 + eps * u0))
        pts += [("top", Ub * (1 - 1e-12)), ("top-1", Ub - 1), ("top-0.5u0^0", Ub - 0.5), ("u0+60", u0 + 60), ("mid", 0.5 * (u0 + Ub))]
        for t, u in pts:
            if 2 <= u <= Ub * (1 - 1e-13): tasks.append((t, l, u))
    with Pool(10, initializer=init) as pool: out = [x for o in pool.map(task, tasks, chunksize=2) for x in o]
    nocell = [o for o in out if 'err' in o]
    out = [o for o in out if 'err' not in o]
    bad = [o for o in out if not (o['S'] >= o['scell'] and 0 < o['S'] <= o['Sig'] * (1 + 1e-9) and o['okM'] and o['okE2'] and o['okE3'] and o['okT'] and o['E1m'] > 0)]
    print("targeted points:", len(tasks), " evaluations:", len(out), " uncovered:", len(nocell), " violations:", len(bad))
    from collections import defaultdict
    agg = defaultdict(lambda: [math.inf, math.inf, 0])
    for o in out:
        a = agg[o['tag']]; a[0] = min(a[0], o['S'] * o['l']); a[1] = min(a[1], (o['S'] - o['scell']) / abs(o['scell'])); a[2] += 1
    for k, (a, b, n) in sorted(agg.items()): print(f"  {k:12s} n={n:4d}  min l*S_point={a:.4g}  min (S_point-s_cell)/|s_cell|={b:.3g}")
    tmax = max(out, key=lambda o: o['T'] * o['l']); print("  largest l*T_true:", tmax['T'] * tmax['l'], "bound l*T:", tmax['Tb'] * tmax['l'], "at", tmax['tag'], tmax['l'], tmax['u'], tmax['tau'])
    for o in (bad + nocell)[:10]: print("BAD", o)
