# Toy B: X0 = 1000, kappa = 0.05, H = 4 (k = 2 cofactors only for u <= 3e7).
import sys, math, random
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
import t3_realised as T3
from t4_bounds import Bounds
for variant, eps in [('jitter', 0.0), ('add', 0.15), ('drift', 0.025)]:
    M, Dvals = T3.run(1000, 0.05, 4, 3.0e7, variant, eps, 3, 10, 30, f"toyB-{variant}")
    Bd = Bounds(M); toy = M.toy
    Ginf = toy.Me * (toy.k + (1 + toy.k) / 2)
    rnd = random.Random(4)
    u0 = 2 * toy.X0 * toy.X0m / (1 + toy.k)
    us = sorted(math.exp(rnd.uniform(math.log(u0), math.log(3.0e7))) for _ in range(25))
    wr = [0, 0, 0]
    for u in us:
        r = Bd.run_u(u, Ginf)
        Dv = M.D(u, value_order=True)
        assert abs(r['val2'] + r['val3'] + Dv) < 1e-12
        a, b, c, d = abs(Dv), r['abel2'] + r['abel3'], r['paper2'] + r['paper3'], r['closed']
        wr = [max(wr[0], a / b if b else 0), max(wr[1], b / c), max(wr[2], c / d)]
    print(f"   Step-3 chain on {len(us)} u: max |D_val|/Abel={wr[0]:.3f} Abel/paper-form={wr[1]:.3f} paper-form/closed={wr[2]:.4f}; "
          f"last u={u:.3g}: |D_val|={a:.2e} Abel={b:.2e} paper={c:.2e} closed={d:.2e} C_D={r['CD']:.2e}")
