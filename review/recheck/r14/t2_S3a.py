# Exact/rigorous pathwise check of Lemma fac (S3)(a) and (S3)(c).
# g_t represented as sum c[(a,b)] x^a (log x)^b with rational c; G_t(E) = A^{K_t} g_t(E/A).
import random, math
from flint import fmpq, arb, ctx
ctx.prec = 256

def prim(term):
    # antiderivative of x^a (log x)^b as dict
    (a, b) = term
    out = {}
    if a == -1:
        out[(0, b+1)] = fmpq(1, b+1)
        return out
    # int x^a L^b = x^{a+1} L^b/(a+1) - b/(a+1) int x^a L^{b-1}
    out[(a+1, b)] = fmpq(1, a+1)
    if b > 0:
        sub = prim((a, b-1))
        for k, v in sub.items():
            out[k] = out.get(k, fmpq(0)) - fmpq(b, a+1) * v
    return out

def integ_e_to_1(poly):
    # Q(e) = int_e^1 poly(x) dx
    P = {}
    for (a, b), c in poly.items():
        for k, v in prim((a, b)).items():
            P[k] = P.get(k, fmpq(0)) + c*v
    # value at 1: only b==0 terms
    P1 = sum((v for (a, b), v in P.items() if b == 0), fmpq(0))
    Q = {k: -v for k, v in P.items()}
    Q[(0, 0)] = Q.get((0, 0), fmpq(0)) + P1
    return {k: v for k, v in Q.items() if v != 0}

def mulx(poly, j):
    return {(a + j - 1, b): c for (a, b), c in poly.items()}

def g_seq(js):
    gs = [{(0, 0): fmpq(1)}]
    K = 0
    Ks = [0]
    for j in js:
        K += j
        Ks.append(K)
        gs.append({k: fmpq(K)*v for k, v in integ_e_to_1(mulx(gs[-1], j)).items()})
    return gs, Ks

def ev(poly, e):
    # e: arb in (0,1]
    L = e.log()
    s = arb(0)
    for (a, b), c in poly.items():
        s += arb(c) * e**a * L**b
    return s

def G(gs, Ks, t, E, A):
    if t == 0:
        return arb(1)
    if E >= A:
        return arb(0)
    return A**Ks[t] * ev(gs[t], E/A)

random.seed(12345)
worst = 0.0
ntest = 0
for trial in range(400):
    # random realised primes at slots 1..N (slot 0 = 'X0'); values arbitrary > 1
    N = random.randint(3, 14)
    present = [random.random() < 0.7 for _ in range(N)]
    mode = random.choice(["small", "large", "mixed"])
    vals = []
    for s in range(N):
        if mode == "small": v = fmpq(random.randint(2, 9)) + fmpq(random.randint(0, 9), 10)
        elif mode == "large": v = fmpq(random.randint(50, 400))
        else: v = fmpq(random.choice([2, 3, 5, 40, 200, 1000]))
        vals.append(v)
    Eu_rat = fmpq(random.randint(10, 30), 10)  # product over 'rational primes'
    Eu = [Eu_rat]  # Eu[s] = product over realised primes of slot < s
    for s in range(N):
        Eu.append(Eu[-1] / (1 - 1/vals[s]) if present[s] else Eu[-1])
    # composition with possible zero stages (Cover Bound) ; first j >= 1
    T = random.randint(1, 4)
    js = [random.randint(1, 3)] + [random.randint(0, 3) for _ in range(T-1)]
    gs, Ks = g_seq(js)
    t = random.randint(1, T)
    K = Ks[t]; j = js[t-1]; m = Ks[t-1]
    smax = random.randint(1, N)   # slots u must be <= smax
    a = random.randint(0, N-1)    # a = s_{t+1}
    # A_top: random, at least Eu_rat; good event G_{<u} := Eu[u'] <= A for all u' <= u
    A = arb(Eu[random.randint(0, N)]) * arb(fmpq(random.randint(100, 160), 100))
    if A < arb(Eu_rat): A = arb(Eu_rat)
    def chi(u):
        if u > smax: return 0
        return 1 if all(arb(Eu[w]) <= A for w in range(u+1)) else 0
    # LHS: sum over latest prime f at slot sigma in [a, N), with u = sigma+1
    lhs = arb(0)
    for sigma in range(a, N):
        if not present[sigma]: continue
        u = sigma + 1
        if not chi(u): continue
        f = vals[sigma]
        other = arb(Eu[sigma] / Eu[a]) ** K          # all subsets/exponents of primes in [a, sigma)
        top = arb(1/(1 - 1/f)) ** K - 1               # nonzero exponent vectors of f
        Phi_prev = G(gs, Ks, t-1, arb(Eu[u]), A) / arb(Eu[u]) ** m
        lhs += other * top * Phi_prev
    rhs = G(gs, Ks, t, arb(Eu[a]), A) / arb(Eu[a]) ** K
    ntest += 1
    if not (lhs <= rhs + arb(10)**-40):
        print("VIOLATION (S3)(a)", trial, js, t, float(lhs), float(rhs))
    if float(rhs) > 0:
        worst = max(worst, float(lhs)/float(rhs))
print("(S3)(a): %d random pathwise instances, no violation; max LHS/RHS = %.6f" % (ntest, worst))

# tightness: one large-prime block with K=j (first stage), many primes
for vbig in [10, 100, 1000, 10**5]:
    N = 40
    vals = [fmpq(vbig + 3*s) for s in range(N)]
    Eu_rat = fmpq(2)
    Eu = [Eu_rat]
    for s in range(N): Eu.append(Eu[-1]/(1-1/vals[s]))
    for js in ([2], [1, 2], [2, 0]):
        gs, Ks = g_seq(js); t = len(js); K = Ks[t]; m = Ks[t-1]
        A = arb(Eu[N]); a = 0
        lhs = arb(0)
        for sigma in range(a, N):
            u = sigma+1
            other = arb(Eu[sigma]/Eu[a])**K; top = arb(1/(1-1/vals[sigma]))**K - 1
            lhs += other*top*G(gs, Ks, t-1, arb(Eu[u]), A)/arb(Eu[u])**m
        rhs = G(gs, Ks, t, arb(Eu[a]), A)/arb(Eu[a])**K
        print("tightness v~%-6d js=%s: LHS/RHS = %.6f" % (vbig, js, float(lhs)/float(rhs)))
