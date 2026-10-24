import sys; sys.path.insert(0, "/tmp/rhscratch/r30/indep")
import sigma_true as ST, time
from indep_S import S_point
ST.load()
for (l, u) in [(3e9, 2.0), (3e9, 30.0), (8.5e10, 205.0), (1e12, 2.0), (1e15, 1000.0), (5e17, 2.0), (5e17, 30000.0)]:
    t = time.time(); c = ST.components(l, u, 1e8)
    r, r0 = ST.R.r(u), (ST.R.r(u - 1) if u > 2 else 1.0)
    S, P = S_point(l, u, r, r0, r0, parts=True)
    print(f"l={l:.3g} u={u:g}  l*Sigma_true={l*c['Sigma']:.6g}  l*S={float((S*l).mid()):.6g}  "
          f"[Mm1 {l*c['Mm1']:.4g}<= {float((P['Mm1']*l).mid()):.4g}; E1 {l*c['E1']:.4g}<={float((P['E1']*l).mid()):.4g}; "
          f"E2 {l*c['E2']:.4g}<={float((P['E2']*l).mid()):.4g}; E3 {l*c['E3']:.4g}<={float((P['E3']*l).mid()):.4g}; T {l*c['Tc0']:.3g}<={float((P['T']*l).mid()):.3g}]  {time.time()-t:.1f}s")
