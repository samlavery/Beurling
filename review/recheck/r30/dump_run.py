# Same cover as cert_run_arb_patched.py, recording every leaf (la, lb, xa, xb, vmode, s, depth) and the band list.
import sys, math, pickle
sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from multiprocessing import Pool
from bs_cert_arb import S_cell
import cert_run_arb as C
import cert_run_arb_patched as P
def run_cells_rec(cells):
    leaves = []; stack = list(cells)
    while stack:
        a, b, xa, xb, vm, d = stack.pop()
        s, info = S_cell(a, b, xa, xb, vm)
        if s > 0: leaves.append((a, b, xa, xb, vm, s, d, info if isinstance(info, dict) else None)); continue
        if d >= C.MAXD: leaves.append((a, b, xa, xb, vm, s, d, "FAIL")); continue
        if d % 2 == 0:
            m = 0.5 * (xa + xb); stack += [(a, b, xa, m, vm, d + 1), (a, b, m, xb, vm, d + 1)]
        else:
            lm = math.sqrt(a * b); stack += [(a, lm, xa, xb, vm, d + 1), (lm, b, xa, xb, vm, d + 1)]
    return leaves
def work(band):
    init = P.band_cells(*band)
    return band, init, run_cells_rec(init)
if __name__ == "__main__":
    bands = []; l = C.LMIN
    while l < C.LMAX: bands.append((l, min(l * 1.05, C.LMAX))); l *= 1.05
    with Pool(10) as pool: res = pool.map(work, bands, chunksize=1)
    nleaf = sum(len(r[2]) for r in res); nfail = sum(1 for r in res for x in r[2] if x[7] == "FAIL")
    print("bands", len(bands), "leaves", nleaf, "fails", nfail)
    with open("/tmp/rhscratch/r30/indep/leaves.pkl", "wb") as f: pickle.dump(res, f)
