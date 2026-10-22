import math, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from capl_model import *
def need(okfun, l, lam=LAM):
    lo, hi = 0.0, 60*lam
    if not okfun(hi, l, l, lam): return float('inf')
    for _ in range(100):
        mid = (lo + hi)/2
        if okfun(mid, l, l, lam): hi = mid
        else: lo = mid
    return hi
def ceiling(l, lam=LAM):
    lo, hi = 0.0, 60*lam
    if not lemmaP_ok(lo, l, l, lam): return -1
    if lemmaP_ok(hi, l, l, lam): return hi
    for _ in range(100):
        mid = (lo + hi)/2
        if lemmaP_ok(mid, l, l, lam): lo = mid
        else: hi = mid
    return lo
for l in (18.5, 20, 22.2, 25, 30, 31.4, 35, 38, 40, 41.95, 42.5, 43, 43.6, 44.2, 45, 50, 100, 1000, 5000, 10000, 11000):
    nH = need(routeH_ok, l); nD = need(dickman_ok, l); ce = ceiling(l)
    print(f"l={l:8}: routeH need {nH/LAM:9.4f}  dickman need {nD/LAM:9.4f}  P-ceiling {ce/LAM:9.4f}  std 4l^2-log4 = {(4*l*l-math.log(4))/LAM:9.4f}  (units of Lam)")
