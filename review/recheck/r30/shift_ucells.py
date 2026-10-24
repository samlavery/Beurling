# Is the shift term set to 0 (hi(v + c_u) <= 0) on every u-cell of the cover?  Same quantities as bs_cert_arb.S_cell.
import sys, math
sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from flint import arb
from ivarb import I, hi_
import cert_run_arb as C
bands = []; l = C.LMIN
while l < C.LMAX: bands.append((l, min(l * 1.05, C.LMAX))); l *= 1.05
nu = nz = 0; worst = -math.inf
for b in bands:
    for (la, lb, ua, ub, vm, d) in C.band_cells(*b):
        if vm: continue
        u0 = I(arb(la).root(4), arb(lb).root(4)); u = I(ua, ub); dv = u - u0; cu = u0 / (3 * u)
        h = hi_(dv + cu); nu += 1; nz += (h <= 0); worst = max(worst, h)
print("u-cells", nu, "with shift = 0:", nz, " max over u-cells of hi(v + c_u) =", worst)
