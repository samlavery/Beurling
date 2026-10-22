# [arb backend] Certified cell cover for Lemma BS (H⁗): l in [3e9, 1e18], u in [2, Ubar(l)].
# u-mode cells on [2, u0(la)/2]; v-mode cells (v = u - u0(l)) covering u in [u0(la)/2, Ubar(l)].
# Adaptive bisection; a cell passes iff the outward-rounded interval lower bound of Sigma is > 0.
import sys, math, time
from multiprocessing import Pool
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from bs_cert_arb import S_cell, Ubar, Ubar_up
from ivarb import _fdn, _fup
from flint import arb
LMIN, LMAX, MAXD = 3e9, 1e18, 20
def run_cells(cells):
    ncell, nfail, minval, worst, fails = 0, 0, math.inf, None, []
    stack = list(cells)
    while stack:
        a, b, xa, xb, vm, d = stack.pop()
        s, _ = S_cell(a, b, xa, xb, vm)
        ncell += 1
        if s > 0:
            v = s * a
            if v < minval: minval, worst = v, (a, b, xa, xb, vm)
            continue
        if d >= MAXD:
            nfail += 1; fails.append((a, b, xa, xb, vm)); continue
        if d % 2 == 0:
            m = 0.5 * (xa + xb); stack += [(a, b, xa, m, vm, d + 1), (a, b, m, xb, vm, d + 1)]
        else:
            lm = math.sqrt(a * b); stack += [(a, lm, xa, xb, vm, d + 1), (lm, b, xa, xb, vm, d + 1)]
    return ncell, nfail, minval, worst, fails[:5]
def band_cells(la, lb):
    u0a, u0b = la ** 0.25, lb ** 0.25
    split = max(40.0, 0.5 * u0a)
    cells = []
    e = [2.0 + 0.5 * k for k in range(77)]; x = 40.0
    while x < split: x = min(x * 1.05, split); e.append(x)
    cells += [(la, lb, e[i], e[i + 1], False, 0) for i in range(len(e) - 1)]
    # v-mode, seam-safe (referee B §21): va = down(split - up(lb^{1/4})), top = up(Ubar_up(lb) - down(la^{1/4})),
    # last edge exactly top; so every u in [split, Ubar(l)] is covered for every l in [la, lb].
    u0b_up = _fup(arb(lb).root(4).upper()); u0a_dn = _fdn(arb(la).root(4).lower())
    va = _fdn((arb(split) - arb(u0b_up)).lower())
    vb = _fup((arb(Ubar_up(lb)) - arb(u0a_dn)).upper())
    n = max(8, int((vb - va) / max(1.0, 0.01 * u0a)))
    e = [va + k * (vb - va) / n for k in range(n)] + [vb]
    cells += [(la, lb, e[k], e[k + 1], True, 0) for k in range(n)]
    return cells
def work(band):
    return band, run_cells(band_cells(*band))
if __name__ == "__main__":
    q = float(sys.argv[1]); nproc = int(sys.argv[2])
    bands = []; l = LMIN
    while l < LMAX: bands.append((l, min(l * q, LMAX))); l *= q
    t0 = time.time()
    with Pool(nproc) as P: res = P.map(work, bands, chunksize=1)
    tot = sum(r[1][0] for r in res); fails = sum(r[1][1] for r in res)
    mn = min(res, key=lambda r: r[1][2])
    print(f"q={q} bands={len(bands)} cells={tot} failed={fails} min certified l*S={mn[1][2]:.4g} at {mn[1][3]} time={time.time()-t0:.0f}s", flush=True)
    for band, r in res:
        if r[1]: print("FAIL", band, r[1], r[4])
