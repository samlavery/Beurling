# Toy for Theorem lp, Steps 2-3: a synthetic Beurling system N tracking the A-free target T0 of eq:target
# (rigid X0-smooth integers + continuous density 1 - rho_det, no oscillation), built by a greedy rule;
# then P_y, Delta, Delta' computed exactly (double precision) and compared with the displayed Step-3 bounds.
import math, cmath, heapq, random, bisect, sys, json

X0, H, KAP, Y = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(float(sys.argv[4]))
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 1
rnd = random.Random(SEED)
X0m = X0 - H / 2
LIM = int((1 + KAP) * Y) + 10
spf = list(range(LIM + 1))
for i in range(2, int(LIM ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j:
                spf[j] = i
def Pplus(n):
    m = 1
    while n > 1:
        p = spf[n]; m = max(m, p)
        while n % p == 0: n //= p
    return m
rigid = [n for n in range(1, LIM + 1) if Pplus(n) < X0]          # X0-smooth integers
small = [p for p in range(2, X0) if spf[p] == p]

# ---- integral of rho_det: I(x) = int_{X0}^x rho_det, rho_det(u) = #rigid in [u,(1+k)u]/(k u) ----
ev = []
for d in rigid:
    a = d / (1 + KAP)
    if d < X0: continue
    ev.append((max(a, X0), +1)); ev.append((d, -1))
ev.sort(key=lambda e: (e[0], -e[1]))
def make_I():
    # returns arrays at integers n in [X0, Y]: I(n)
    I = {}
    cnt = 0; pos = X0; acc = 0.0; j = 0
    for n in range(X0, Y + 1):
        while j < len(ev) and ev[j][0] <= n:
            x, s = ev[j]
            acc += cnt * math.log(x / pos) / KAP; pos = x; cnt += s; j += 1
        I[n] = acc + cnt * math.log(n / pos) / KAP
    return I
Iint = make_I()
rig_le = lambda x: bisect.bisect_right(rigid, x)
def T0(n):  # at integer n
    if n < X0: return n
    return X0 + (rig_le(n) - rig_le(X0)) + (n - X0) - Iint[n]

# ---- greedy realised system: slots at integers n >= X0, add a prime at n + U(0,H) when T0(n) - N(n) >= 1/2 ----
primes = list(small)            # values
slots = list(small)
heap = [1.0]
elems = []
L_of = {}                        # element value -> largest prime index (for unique generation)
L_of[1.0] = -1
def create(e):
    elems.append(e)
    li = L_of[e]
    for idx in range(max(li, 0), len(primes)):
        v = e * primes[idx]
        if v > Y: break
        if v not in L_of:
            L_of[v] = idx; heapq.heappush(heap, v)
# primes sorted by value for the generation rule: small primes first (sorted), large appended in increasing value
maxdev = 0.0; maxrel = 0.0
for n in range(1, Y + 1):
    while heap and heap[0] <= n:
        e = heapq.heappop(heap); create(e)
    if n >= X0:
        Nn = len(elems)
        dfc = T0(n) - Nn
        if dfc >= 0.5:
            P = n + rnd.uniform(0, H)
            primes.append(P); slots.append(n)
            j = len(primes) - 1
            for e in elems:
                v = e * P
                if v > Y: break
                if v not in L_of:
                    L_of[v] = j; heapq.heappush(heap, v)
            # P itself (from e = 1) is pushed above; powers P^k come from e = P later via create()
        dev = abs(T0(n) - len(elems))
        maxdev = max(maxdev, dev); maxrel = max(maxrel, dev / n ** 0.5)
while heap and heap[0] <= Y:
    create(heapq.heappop(heap))
elems.sort()
# check: elems below X0m are exactly 1..X0-1
assert elems[:X0 - 1] == [float(i) for i in range(1, X0)], "N != floor below X0"
logy = math.log(Y)
print(f"toy: X0={X0} H={H} kappa={KAP} y={Y}: #elements={len(elems)} #large primes={len(primes)-len(small)}; "
      f"max_n |N-T0| = {maxdev:.2f}, max |N-T0|/n^0.5 = {maxrel:.3f}  (LP-a needs <= n^theta')")

# ---- prime measure Pi on [1,y]: primes and prime powers with weight 1/k ----
pk = []
for p in primes:
    q = p; k = 1
    while q <= Y:
        pk.append((q, k, p)); q *= p; k += 1
Py1 = math.exp(sum(1 / (k * q) for q, k, p in pk))
Sy = sum(math.log(p) / q for q, k, p in pk)
# int_[1,z] dPi/u - log log z, max over z >= e
pk.sort()
acc = 0.0; mx = 0.5
for q, k, p in pk:
    acc += 1 / (k * q)
    if q >= 3: mx = max(mx, acc - math.log(math.log(q)))
print(f"Step 2: P_y(1)={Py1:.3f} <= e^4.5 log y = {math.exp(4.5)*logy:.1f};  max_z(int dPi/u - loglog z) = {mx:.4f} <= 4.5;  "
      f"S(y)={Sy:.4f} <= log y + 0.43 = {logy+0.43:.4f}")

def Psum(s):  # sum over elements <= y of n^{-s}
    return sum(cmath.exp(-s * math.log(e)) for e in elems)
def Py(s):
    return cmath.exp(sum(cmath.exp(-s * math.log(q)) / k for q, k, p in pk))
def Pyd_over(s):  # P_y'/P_y = - sum log(q) q^{-s}/k
    return -sum(math.log(q) * cmath.exp(-s * math.log(q)) / k for q, k, p in pk)
rig_y = [d for d in rigid if d <= Y]
rig_1k = [d for d in rigid if d <= (1 + KAP) * Y]
def euler(s):
    r = 1
    for p in small: r /= (1 - cmath.exp(-s * math.log(p)))
    return r
def A(s):  # int_{(y,oo)} u^{-s} dT0, T0 = rigid jumps + (1 - rho_det) du
    E = euler(s)
    rig_tail = E - sum(cmath.exp(-s * math.log(d)) for d in rig_y)
    lin = cmath.exp((1 - s) * logy) / (s - 1)
    full_tail = E - sum(cmath.exp(-s * math.log(d)) for d in rig_1k)   # d > (1+k) y
    rho = ((1 + KAP) ** s - 1) / (s * KAP) * full_tail
    rho += sum(cmath.exp(-s * logy) - cmath.exp(-s * math.log(d)) for d in rig_1k if d > Y) / (s * KAP)
    return rig_tail + lin - rho
def Delta(s):
    return Psum(s) + A(s) - Py(s)

rows = []
worst = {}
for eta in [0.125, 0.06, 0.03, 0.015, 0.008]:
    sig = 1 + eta
    Pys = Py(sig).real
    yb = Y ** (-eta / 2)
    BP = 1 / eta + 6 + yb * Py1
    BD = 2 * Y ** (-eta) / eta + yb * Py1
    BD1 = 2 * Y ** (-eta) * (logy / eta + 1 / eta ** 2) + yb * Py1 * Sy
    # the two pieces of |Delta| at real sigma
    Ttail = A(sig).real
    Nytail = Pys - Psum(sig).real
    hstep = 1e-5
    Ttail_log = -(A(sig + hstep).real - A(sig - hstep).real) / (2 * hstep)
    Nytail_log = -(Py(sig + hstep).real - Py(sig - hstep).real) / (2 * hstep) - sum(math.log(e) * e ** (-sig) for e in elems)
    for t in [0.0, 1.0, 3.7, 14.13, 50.0, 211.0, rnd.uniform(0, 1000)]:
        s = complex(sig, t)
        d = Delta(s)
        d1 = (Delta(s + hstep) - Delta(s - hstep)) / (2 * hstep)
        py = Py(s)
        q = d / py
        dlog = (d1 / py - d * Pyd_over(s) / py) / (1 + q)
        rec = dict(eta=eta, t=t, P_sig=Pys, BP=BP, absD=abs(d), BD=BD, absD1=abs(d1), BD1=BD1,
                   absPy=abs(py), inv=1 / Pys, PydP=abs(Pyd_over(s)), Sy=Sy, q=abs(q), qb=abs(d) * Pys, dlog=abs(dlog),
                   Ttail=Ttail, Ttail_b=2 * Y ** (-eta) / eta, Nytail=Nytail, Nytail_b=yb * Py1, Nytail_b2=Y ** (-eta) * Py1,
                   Ttail_log=Ttail_log, Ttail_log_b=2 * Y ** (-eta) * (logy / eta + 1 / eta ** 2), Nytail_log=Nytail_log,
                   Nytail_log_b=yb * Py1 * Sy)
        rows.append(rec)
checks = [('P_y(sigma) <= 1/eta+6+y^-eta/2 P_y(1)', 'P_sig', 'BP'), ('|Delta| <= bound', 'absD', 'BD'),
          ('|Delta\'| <= bound', 'absD1', 'BD1'), ('1/P_y(sigma) <= |P_y(s)|', 'inv', 'absPy'), ('|P_y\'/P_y| <= S(y)', 'PydP', 'Sy'),
          ('T0 tail <= 2y^-eta/eta', 'Ttail', 'Ttail_b'), ('N_y tail <= y^-eta/2 P_y(1)', 'Nytail', 'Nytail_b'),
          ('N_y tail <= y^-eta P_y(1) (sharper)', 'Nytail', 'Nytail_b2'),
          ('log-weighted T0 tail <= 2y^-eta(log y/eta+1/eta^2)', 'Ttail_log', 'Ttail_log_b'),
          ('log-weighted N_y tail <= y^-eta/2 P_y(1) S(y)', 'Nytail_log', 'Nytail_log_b'),
          ('|Delta/P_y| <= |Delta| P_y(sigma)', 'q', 'qb')]
for name, a, b in checks:
    r = max(rw[a] / rw[b] for rw in rows)
    worst[name] = r
    print(f"  {name:55s}: max actual/bound = {r:.4f}  {'OK' if r <= 1 + 1e-9 else 'FAIL'}")
for eta in [0.125, 0.008]:
    rw = [r for r in rows if r['eta'] == eta]
    print(f"  eta={eta}: P_y(sigma)={rw[0]['P_sig']:.3f} (2/eta={2/eta:.1f}); T0 tail={rw[0]['Ttail']:.4f} vs y^-eta/eta={Y**(-eta)/eta:.4f}; "
          f"N_y tail={rw[0]['Nytail']:.4f}; max|Delta/P_y|={max(r['q'] for r in rw):.4f}; max|dlog(1+Delta/P_y)|={max(r['dlog'] for r in rw):.4f} "
          f"vs (eta log y)^-1={1/(eta*logy):.4f}")
json.dump(rows, open(f'/tmp/rhscratch/r10/out/toy_{X0}_{Y}_{SEED}.json', 'w'))
