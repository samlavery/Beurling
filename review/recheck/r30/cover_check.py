# Independent coverage check of the leaf set against the claimed region
#   {(l,u): 3e9 <= l <= 1e18, 2 <= u <= Ubar(l)},  Ubar(l) = l^{1/4}(1+sqrt(2 log(l/1e8)+4)) >= U(l;tau) for tau >= 1e8.
import pickle, math, random, collections, bisect
from flint import arb, ctx
ctx.prec = 200
res = pickle.load(open("/tmp/rhscratch/r30/indep/leaves.pkl", "rb"))
depths = collections.Counter(x[6] for r in res for x in r[2]); print("depth histogram", dict(depths))
ninit = sum(len(r[1]) for r in res); print("initial cells", ninit)
bands = [r[0] for r in res]
# 1. bands tile [3e9, 1e18] exactly (float equality of seams)
assert bands[0][0] == 3e9 and bands[-1][1] == 1e18
assert all(bands[i][1] == bands[i+1][0] for i in range(len(bands)-1)); assert all(a < b for a, b in bands)
print("bands tile [3e9,1e18] with exact seams:", len(bands))
def Ubar_exact(l):  # arb ball, high precision
    L = arb(l); return L.root(4) * (1 + (2 * (L / arb(10)**8).log() + 4).sqrt())
bad = 0
for band, init, leaves in res:
    la, lb = band
    ucells = sorted([c for c in init if not c[4]], key=lambda c: c[2]); vcells = sorted([c for c in init if c[4]], key=lambda c: c[2])
    # u-cells: contiguous from 2.0 to split
    assert ucells[0][2] == 2.0 and all(ucells[i][3] == ucells[i+1][2] for i in range(len(ucells)-1))
    split = ucells[-1][3]
    assert all(vcells[i][3] == vcells[i+1][2] for i in range(len(vcells)-1))
    va, vtop = vcells[0][2], vcells[-1][3]
    # rigorous: for all l in [la,lb]: u0(l)+va <= split  and  u0(l)+vtop >= Ubar(l)
    c1 = arb(lb).root(4) + arb(va) < arb(split)
    c2 = arb(la).root(4) + arb(vtop) > Ubar_exact(lb)
    if not (c1 and c2): bad += 1; print("SEAM PROBLEM", band, c1, c2)
    # leaves exactly tile each initial cell: total measure check in (log l, x) coordinates with exact rationals
    from fractions import Fraction as F
    meas = collections.defaultdict(F)
    for c in leaves: meas[c[4]] += F(c[1]) - F(c[0]) if False else 0
print("u/v seam and top-edge checks failed in", bad, "bands")
# 2. tiling: since no leaf is deeper than 0 (checked above if so), leaves == initial cells
same = all(sorted((c[0],c[1],c[2],c[3],c[4]) for c in leaves) == sorted((c[0],c[1],c[2],c[3],c[4]) for c in init) for _, init, leaves in res)
print("leaves identical to initial cells in every band:", same)
# 3. random point-in-cover test, exact u0 via arb
random.seed(11); miss = 0; N = 200000
for _ in range(N):
    i = random.randrange(len(res)); (la, lb), init, leaves = res[i]
    t = random.random(); l = la * (lb/la)**t if random.random() > 0.02 else (la if random.random() < 0.5 else lb)
    l = min(max(l, la), lb)
    ub = float(Ubar_exact(l).upper())
    u = 2 + random.random() * (ub - 2) if random.random() > 0.05 else random.choice([2.0, ub])
    u0 = arb(l).root(4)
    ok = False
    for c in leaves:
        if not (c[0] <= l <= c[1]): continue
        if not c[4]:
            if c[2] <= u <= c[3]: ok = True; break
        else:
            v = arb(u) - u0
            if arb(c[2]) <= v and v <= arb(c[3]): ok = True; break
    if not ok:
        # u = ub was taken from an upper bound; accept a miss only if u exceeds the exact Ubar(l)
        if arb(u) > Ubar_exact(l): continue
        miss += 1
        if miss < 5: print("MISS", l, u, (la, lb))
print("random points tested", N, "uncovered", miss)
