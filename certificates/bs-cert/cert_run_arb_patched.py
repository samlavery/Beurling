# Alias of cert_run_arb.py: same cell code (imports run_cells/LMIN/LMAX/MAXD from it); kept for the documented command line. Not an independent check.
import sys, math, time
from multiprocessing import Pool
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from flint import arb
from bs_cert_arb import S_cell, Ubar, Ubar_up
from ivarb import _fdn, _fup
import cert_run_arb as C
def band_cells(la, lb):
    u0a, u0b = la ** 0.25, lb ** 0.25
    split = max(40.0, 0.5 * u0a)
    cells = []
    e = [2.0 + 0.5 * k for k in range(77)]; x = 40.0
    while x < split: x = min(x * 1.05, split); e.append(x)
    cells += [(la, lb, e[i], e[i + 1], False, 0) for i in range(len(e) - 1)]
    u0b_up = _fup(arb(lb).root(4).upper()); u0a_dn = _fdn(arb(la).root(4).lower())
    va = _fdn((arb(split) - arb(u0b_up)).lower())               # u0(l) + va <= split for every l <= lb
    vtop = _fup((arb(Ubar_up(lb)) - arb(u0a_dn)).upper())         # u0(l) + vtop >= Ubar(lb) >= U(l;tau) for l >= la
    n = max(8, int((vtop - va) / max(1.0, 0.01 * u0a)))
    edges = [va + k * (vtop - va) / n for k in range(n)] + [vtop]
    cells += [(la, lb, edges[k], edges[k + 1], True, 0) for k in range(n)]
    return cells
def work(band): return band, C.run_cells(band_cells(*band))
if __name__ == "__main__":
    q = float(sys.argv[1]); nproc = int(sys.argv[2])
    bands = []; l = C.LMIN
    while l < C.LMAX: bands.append((l, min(l * q, C.LMAX))); l *= q
    t0 = time.time()
    with Pool(nproc) as P: res = P.map(work, bands, chunksize=1)
    tot = sum(r[1][0] for r in res); fails = sum(r[1][1] for r in res)
    mn = min(res, key=lambda r: r[1][2])
    print(f"[patched seams] q={q} bands={len(bands)} cells={tot} failed={fails} min certified l*S={mn[1][2]:.4g} at {mn[1][3]} time={time.time()-t0:.0f}s", flush=True)
