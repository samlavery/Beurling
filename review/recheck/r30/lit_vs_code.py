import sys, pickle, math
sys.path.insert(0, "/tmp/rhscratch/r30/indep"); sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from indep_S import S_point
from dickman import Rho
from flint import arb
R = Rho.__new__(Rho); R.logrho, R.C = pickle.load(open("/tmp/rhscratch/r30/indep/rho270k.pkl","rb")); R.K = len(R.logrho)-1
for l in (3e9, 1e12, 1e15, 9.9e17):
    for u in (2.0, 5.0, 20.0, 40.0, 100.0):
        if u > 0.5 * l**0.25: continue
        r, r0 = R.r(u), R.r(u-1) if u > 2 else 1.0
        sc = S_point(l, u, r, r0, r0); sl_ = S_point(l, u, r, r0, r0, literal=True)
        print(f"l={l:.3g} u={u:6g}  l*S(code form)={float((sc*l).mid()):.4g}   l*S(paper literal)={float((sl_*l).mid()):.4g}")
