# Toy model for the operator comparison of Section 6 (Lemma margin (b)-(d)).
# Rational system N and a synthetic realised system NN: rational primes < X0 (t(p)=p) plus jittered primes
# (value = slot + H(U-1/2), decision time t = slot >= X0).  All operators are implemented from the paper's definitions.
import math, random, bisect, sys
import flint

X0 = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 100
kappa = 0.15
H = 4.0
X0m = X0 - H / 2
Lam = math.log(X0)
UMAX = 4.3e6
SEED = 12345

# ---------------- rational primes, gpf, mobius ----------------
PMAX = int((1 + kappa) * UMAX) + 10
sieve = bytearray([1]) * (PMAX + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(PMAX ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(range(i * i, PMAX + 1, i)))
PR = [i for i in range(PMAX + 1) if sieve[i]]

MMAX = int((1 + kappa) * UMAX / (X0 / (1 + kappa))) + 10
gpf = [0] * (MMAX + 1)
mob = [1] * (MMAX + 1)
for p in PR:
    if p > MMAX:
        break
    for j in range(p, MMAX + 1, p):
        gpf[j] = p
        mob[j] = -mob[j]
    pp = p * p
    for j in range(pp, MMAX + 1, pp):
        mob[j] = 0
gpf[1] = 1


def nprimes(a, b):
    """# rational primes p with a <= p <= b (real a,b)."""
    if b < a:
        return 0
    return bisect.bisect_right(PR, b) - bisect.bisect_left(PR, a)


_li_cache = {}


def li(x):
    v = _li_cache.get(x)
    if v is None:
        v = float(flint.arb(x).li())
        _li_cache[x] = v
    return v


def Iint(a, b):
    """int_a^b dt/log t."""
    if b <= a:
        return 0.0
    return li(b) - li(a)


# ---------------- window densities ----------------
def MA_P_restr(q, a):
    """MA_{kq}[rational primes >= max(a, X0)](q)."""
    lo = max(q, a, X0)
    return nprimes(lo, (1 + kappa) * q) / (kappa * q)


def MA_nu0_restr(q, a):
    lo = max(q, a, X0)
    return Iint(lo, (1 + kappa) * q) / (kappa * q)


def MAP(q):
    return MA_P_restr(q, 0)


def f0(q):
    """f_0 1_{[X0,oo)}: only defined/nonzero for q >= X0 (the paper evaluates f0 only there)."""
    if q < X0:
        return 0.0
    return Iint(q, (1 + kappa) * q) / (kappa * q)


def f1(q):
    if q < X0:
        return 0.0
    return MAP(q) - f0(q)


# ---------------- rational-system operators ----------------
def KQwin(x, which, full=False):
    """Windowed K_Q acting on the measure nu: which in {'P','nu0','nu1'}.
    full=False: K_Q(h 1_{[X0,oo)}) (components q>=X0); full=True: all components."""
    s = 0.0
    mtop = int((1 + kappa) * x / X0) + 1
    for m in range(2, min(mtop, MMAX) + 1):
        q = x / m
        if (1 + kappa) * q < X0:
            break
        if not full and q < X0:
            break
        P = gpf[m]
        if which == 'P':
            v = MA_P_restr(q, P)
        elif which == 'nu0':
            v = MA_nu0_restr(q, P)
        else:
            v = MA_P_restr(q, P) - MA_nu0_restr(q, P)
        s += v / m
    return s


def KQsh(x, h, cutoff=None, strict=False):
    """Sharp rational operator: sum_{m>=2} 1/m 1[P+(m) <= x/m] 1[x/m >= cutoff] h(x/m)."""
    if cutoff is None:
        cutoff = X0
    s = 0.0
    for m in range(2, int(x / cutoff) + 1):
        q = x / m
        P = gpf[m]
        if (P < q) if strict else (P <= q):
            s += h(q) / m
    return s


def mu_edge(u):
    s = 0.0
    Nlo = int(u / X0) + 1
    Nhi = int((1 + kappa) * u / X0) + 1
    for N in range(max(2, Nlo - 1), Nhi + 1):
        q = u / N
        if X0 / (1 + kappa) < q < X0:
            s += MA_P_restr(q, gpf[N]) / N
    return s


def chiQ(n, y):
    """chi_y(n) for the rational system (t(p)=p): n squarefree, p * prod_{q|n,q>=p} q < y for all p|n."""
    if mob[n] == 0:
        return 0
    ps = []
    m = n
    while m > 1:
        p = gpf[m]
        ps.append(p)
        m //= p
    # ps descending
    prod = 1
    for p in ps:
        prod *= p
        if p * prod >= y:
            return 0
    return 1


def resolventQ(x, h, cutoff=None):
    """(1+K'_Q)^{-1} h (x) via Lemma M in the rational system, cutoff X0."""
    if cutoff is None:
        cutoff = X0
    s = 0.0
    for n in range(1, int(x / cutoff) + 1):
        c = mob[n]
        if c == 0:
            continue
        if n > 1 and not chiQ(n, x):
            continue
        s += c * h(x / n) / n
    return s


# ---------------- realised system ----------------
rng = random.Random(SEED)
WMAX = UMAX / X0m + 10
JIT = []  # (value, t)
# forced slots that land below X0
JIT.append((X0 - 1.1, X0 + 0.3))
JIT.append((X0 - 0.4, X0 + 1.2))
for n in range(X0, int(WMAX * 1.2) + int(H) + 2):
    if sieve[n]:
        keep = rng.random() < 0.9
    else:
        keep = rng.random() < 0.10 / math.log(n)
    if keep:
        t = n + rng.random() * 0.999 + 0.0005  # slot (decision time), non-integer
        v = t + H * (rng.random() - 0.5)
        if v < X0m:
            v = X0m + 1e-3
        JIT.append((v, t))
JIT.sort()
JITV = [v for v, t in JIT]
BASE = [p for p in PR if p < X0]
# realised primes: list of (value, t, is_jit)
RP = [(float(p), float(p), False) for p in BASE] + [(v, t, True) for v, t in JIT]
RP.sort()


def build_elements(WM):
    """All elements of NN with value <= WM. Each element: (value, tau, Pval, primes(tuple of idx), squarefree)."""
    els = []
    nP = len(RP)

    def rec(start, val, tau, pval, idxs, sqf):
        els.append((val, tau, pval, idxs, sqf))
        for i in range(start, nP):
            pv, pt, _ = RP[i]
            nv = val * pv
            if nv > WM:
                break
            # exponent >= 1 of prime i
            e_idxs = idxs + (i,)
            rec(i + 1, nv, max(tau, pt), max(pval, pv), e_idxs, sqf)
            nv2 = nv * pv
            ee = e_idxs
            while nv2 <= WM:
                ee = ee + (i,)
                rec(i + 1, nv2, max(tau, pt), max(pval, pv), ee, False)
                nv2 *= pv
    rec(0, 1.0, 0.0, 1.0, (), True)
    els.sort()
    return els


ELS = None


def get_els():
    global ELS
    if ELS is None:
        ELS = build_elements(WMAX)
    return ELS


def Kpt(y, h, order='dec', cutoff=None):
    """K_pt h(y) = sum_{w in NN, w>=2} 1/w 1[tau_w < y/w] 1[y/w >= cutoff] h(y/w); order='val' uses P+(w) by value."""
    if cutoff is None:
        cutoff = X0m
    els = get_els()
    s = 0.0
    wmax = y / cutoff
    for (w, tau, pval, idxs, sqf) in els:
        if w > wmax:
            break
        if w < 1.5:
            continue
        key = tau if order == 'dec' else pval
        if key < y / w:
            s += h(y / w) / w
    return s


def cn_real(el, y):
    """Lemma M coefficient c_n(y) for the realised system (decision order)."""
    (w, tau, pval, idxs, sqf) = el
    if y / w < X0m:
        return 0
    if not sqf:
        return 0
    if w < 1.5:
        return 1
    prs = sorted(((RP[i][1], RP[i][0]) for i in idxs), reverse=True)  # by t descending
    prod = 1.0
    for t, v in prs:
        prod *= v
        if t * prod >= y:
            return 0
    return (-1) ** len(idxs)


def resolvent_pt(x, h):
    els = get_els()
    s = 0.0
    for el in els:
        if el[0] > x / X0m:
            break
        c = cn_real(el, x)
        if c:
            s += c * h(x / el[0]) / el[0]
    return s


# Delta_psi = psi_NN - psi (all prime powers) and Delta_theta restricted to large primes
def psi_NN(t):
    s = 0.0
    for v, tt, isj in RP:
        if v > t:
            break
        pk = v
        while pk <= t:
            s += math.log(v)
            pk *= v
    return s


# ---------------- Delta_psi / Delta_theta for the large primes ----------------
_ev_psi = []
_ev_th = []
for v, tt, isj in RP:
    if isj:
        pk = v
        k = 1
        while pk <= 2 * WMAX:
            _ev_psi.append((pk, math.log(v)))
            if k == 1:
                _ev_th.append((pk, math.log(v)))
            pk *= v
            k += 1
for p in PR:
    if p < X0:
        continue
    if p > 2 * WMAX:
        break
    pk = p
    k = 1
    while pk <= 2 * WMAX:
        _ev_psi.append((float(pk), -math.log(p)))
        if k == 1:
            _ev_th.append((float(pk), -math.log(p)))
        pk *= p
        k += 1
_ev_psi.sort()
_ev_th.sort()
EVP_x = [a for a, b in _ev_psi]
EVT_x = [a for a, b in _ev_th]
EVP_c = []
EVT_c = []
_s = 0.0
for a, b in _ev_psi:
    _s += b
    EVP_c.append(_s)
_s = 0.0
for a, b in _ev_th:
    _s += b
    EVT_c.append(_s)


def Dpsi(t):
    i = bisect.bisect_right(EVP_x, t)
    return EVP_c[i - 1] if i else 0.0


def Dth(t):
    i = bisect.bisect_right(EVT_x, t)
    return EVT_c[i - 1] if i else 0.0
