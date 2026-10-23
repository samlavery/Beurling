# Exact checks of Lemma SC (1)-(3), the Schur-complement factorisation of Theorem svl(i),
# the late-free-column facts of svl(ii), and greedy-pivot facts, on random configurations.
import random
from fractions import Fraction as Fr

def rank(rows):
    M = [list(map(Fr, r)) for r in rows]
    if not M: return 0
    m, n = len(M), len(M[0]); r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f*b for a, b in zip(M[i], M[r])]
        r += 1
        if r == m: break
    return r

def det(M):
    M = [list(map(Fr, r)) for r in M]; n = len(M); d = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for i in range(c+1, n):
            f = M[i][c] / M[c][c]
            M[i] = [a - f*b for a, b in zip(M[i], M[c])]
    return d

def inv(M):
    n = len(M); A = [list(map(Fr, r)) + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]; A[c] = [a / pv for a in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f*b for a, b in zip(A[i], A[c])]
    return [r[n:] for r in A]

def matmul(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]

def sub(A, rows, cols): return [[A[i][j] for j in cols] for i in rows]

random.seed(2026)
stats = dict(configs=0, covers=0, sc_fail=0, schur_fail=0, latefree_fail=0, rfirst_fail3=0, colmass_fail=0)
for trial in range(3000):
    k = random.randint(2, 7)
    ncols = random.randint(k, k+6)
    dens = random.choice([0.25, 0.4, 0.6])
    E = [[(random.randint(1, 3) if random.random() < dens else 0) for _ in range(ncols)] for _ in range(k)]
    # every column nonzero
    for j in range(ncols):
        if all(E[i][j] == 0 for i in range(k)): E[random.randrange(k)][j] = 1
    if rank(E) < k: continue
    # columns in decision order 0..ncols-1 (0 earliest); greedy pivots latest first
    piv = []
    for j in reversed(range(ncols)):
        cols = [[E[i][p] for p in piv] for i in range(k)]
        if rank([r + [E[i][j]] for i, r in enumerate(cols)]) > rank(cols) if piv else True:
            piv.append(j)
    assert len(piv) == k
    pivset = set(piv)
    # runs: maximal runs of consecutive pivot columns, latest first
    runs = []; j = ncols - 1
    while j >= 0:
        if j in pivset:
            run = []
            while j >= 0 and j in pivset: run.append(j); j -= 1
            runs.append(run)
        else: j -= 1
    T = len(runs)
    # blocks: F_t = free columns between run t and run t+1 ; early block F_T
    blocks = []
    for t in range(T):
        lo = runs[t+1][0] if t+1 < T else -1
        blocks.append([c for c in range(lo+1, runs[t][-1]) if c not in pivset])
    Pst = lambda t: [p for r in runs[:t] for p in r]
    Fst = lambda t: [f for b in blocks[:t] for f in b]
    # (A-span): every f in F_{<=t} lies in span of P_{<=t} columns
    for t in range(1, T+1):
        PP = Pst(t)
        for f in Fst(t):
            A = [[E[i][p] for p in PP] for i in range(k)]
            assert rank([A[i] + [E[i][f]] for i in range(k)]) == rank(A)
    stats['configs'] += 1
    # random covers C (subsets of rows covering all columns)
    for _ in range(4):
        C = sorted(random.sample(range(k), random.randint(1, k)))
        if any(all(E[i][j] == 0 for i in C) for j in range(ncols)): continue
        stats['covers'] += 1
        for order_name, order in (("Cfirst", C + [i for i in range(k) if i not in C]),
                                  ("Rfirst", [i for i in range(k) if i not in C] + C)):
            Rs = []
            for t in range(1, T+1):
                PP = Pst(t); basis = []
                for y in order:
                    rows = [[E[w][p] for p in PP] for w in basis + [y]]
                    if rank(rows) > len(basis): basis.append(y)
                Rs.append(basis)
            ok3 = all(any(E[y][j] != 0 for y in Rs[t-1] if y in C) for t in range(1, T+1) for j in Pst(t) + Fst(t))
            if order_name == "Rfirst":
                if not ok3: stats['rfirst_fail3'] += 1
                continue
            ok1 = all(set(Rs[t]) <= set(Rs[t+1]) for t in range(T-1)) and set(Rs[-1]) == set(range(k))
            ok2 = all(len(Rs[t-1]) == len(Pst(t)) and det(sub(E, Rs[t-1], Pst(t))) != 0 for t in range(1, T+1))
            if not (ok1 and ok2 and ok3): stats['sc_fail'] += 1; print("SC FAIL", E, C, runs, Rs)
            # column masses over cover rows of R_{<=t} >= 1 for pivots of P_{<=t}
            for t in range(1, T+1):
                for j in Pst(t):
                    if sum(E[y][j] for y in Rs[t-1] if y in C) < 1: stats['colmass_fail'] += 1
            # Schur factorisation: det E_{R<=t,P<=t} = prod_s det S_s, staged
            for t in range(1, T+1):
                prod = Fr(1)
                for s in range(1, t+1):
                    Rprev = Rs[s-2] if s >= 2 else []; Cs = [y for y in Rs[s-1] if y not in Rprev]
                    Pprev = Pst(s-1); Ps = runs[s-1]
                    S = sub(E, Cs, Ps)
                    if Rprev:
                        corr = matmul(matmul(sub(E, Cs, Pprev), inv(sub(E, Rprev, Pprev))), sub(E, Rprev, Ps))
                        S = [[S[i][j] - corr[i][j] for j in range(len(Ps))] for i in range(len(Cs))]
                    prod *= det(S)
                # ordering of rows/cols: compare absolute values (row/col permutation changes sign only)
                d = det(sub(E, Rs[t-1], Pst(t)))
                if abs(d) != abs(prod) or d == 0 or d.denominator != 1: stats['schur_fail'] += 1
            # svl(ii): for f in F_t, coefficient in rows outside R_{<=t} vanishes; covered by C cap R_{<=t}
            for t in range(1, T+1):
                PP = Pst(t); R = Rs[t-1]; Minv = inv(sub(E, R, PP))
                for f in Fst(t):
                    v = matmul(Minv, [[E[y][f]] for y in R])
                    for y in range(k):
                        val = sum(Fr(E[y][p])*v[i][0] for i, p in enumerate(PP))
                        if val != E[y][f]: stats['latefree_fail'] += 1
print(stats)
