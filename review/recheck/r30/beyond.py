# Cross-check only (not part of the paper's proof): the same closed-form bound S on l in [1e18, 1e24].
import sys, math
sys.path.insert(0, "/tmp/rhscratch/r30/cert")
from multiprocessing import Pool
import cert_run_arb as C
import cert_run_arb_patched as P
def work(band): return band, C.run_cells(P.band_cells(*band))
if __name__ == "__main__":
    bands = []; l = 1e18
    while l < 1e24: bands.append((l, min(l * 1.05, 1e24))); l *= 1.05
    with Pool(10) as pool: res = pool.map(work, bands, chunksize=1)
    print("bands", len(bands), "cells", sum(r[1][0] for r in res), "failed", sum(r[1][1] for r in res),
          "min l*S", min(r[1][2] for r in res))
    for b, r in res:
        if r[1]: print("FAIL", b, r[1], r[4][:2])
