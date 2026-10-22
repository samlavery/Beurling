# Brute-force test of gap-G3 §16.22' condition (SC) / verify-CL §R.12'' nested cover.
# Rows = basis B' (r rows, rank r). Columns = primes, index 0 = latest decided.
# Greedy pivots latest-first; stages = maximal pivot runs; F_t = free cols between run t and run t+1.
# C = a minimum cover of row supports. (SC): exists nested R_1 ⊂ R_2 ⊂ ... with |R_<=t| = |P_<=t|,
# E[R_<=t, P_<=t] invertible, and every pivot of P_<=t and every f in F_t has a nonzero entry in a C-row of R_<=t.
import itertools, random, sys
from fractions import Fraction

def rank(M):
    if not M or not M[0]: return 0
    A = [[Fraction(x) for x in row] for row in M]
    rk, ncol = 0, len(A[0])
    for c in range(ncol):
        p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                f = A[i][c] / A[rk][c]
                A[i] = [a - f*b for a, b in zip(A[i], A[rk])]
        rk += 1
    return rk

def analyse(E):
    r, m = len(E), len(E[0])
    cols = [[E[i][j] for i in range(r)] for j in range(m)]
    piv, cur = [], []
    for j in range(m):
        if rank([[cols[p][i] for p in cur + [j]] for i in range(r)]) > len(cur):
            cur.append(j); piv.append(j)
    if len(piv) != r: return None
    # stages: runs of consecutive pivots in column order (ignoring nothing)
    stages, frees, run, fr = [], [], [], []
    for j in range(m):
        if j in piv:
            if fr and run:  # free block between runs closes run
                stages.append(run); frees.append(fr); run, fr = [], []
            elif fr and not run:  # free before first pivot: not late (no later pivot) -> ignore (never happens: col 0 nonzero)
                fr = []
            run.append(j)
        else:
            fr.append(j)
    stages.append(run); frees.append([])  # trailing frees are the early block (no SUP-SUM constraint)
    return piv, stages, frees

def min_covers(E):
    r, m = len(E), len(E[0])
    supp = [frozenset(j for j in range(m) if E[i][j]) for i in range(r)]
    allp = frozenset().union(*supp)
    for k in range(1, r + 1):
        cs = [c for c in itertools.combinations(range(r), k) if frozenset().union(*(supp[i] for i in c)) == allp]
        if cs: return cs
    return []

def sc_holds(E, stages, frees, C):
    r = len(E)
    C = set(C)
    def ok_cover(Rs, t):
        need = set(j for s in stages[:t+1] for j in s) | set(frees[t])
        return all(any(E[i][j] for i in Rs if i in C) for j in need)
    def rec(t, R):
        if t == len(stages): return True
        Pt = [j for s in stages[:t+1] for j in s]
        k = len(Pt) - len(R)
        rest = [i for i in range(r) if i not in R]
        for add in itertools.combinations(rest, k):
            Rs = R + list(add)
            if rank([[E[i][j] for j in Pt] for i in Rs]) == len(Pt) and ok_cover(Rs, t):
                if rec(t + 1, Rs): return True
        return False
    return rec(0, [])

def trial(r, m, maxe, dens, rng):
    E = [[(rng.randint(1, maxe) if rng.random() < dens else 0) for _ in range(m)] for _ in range(r)]
    if rank(E) < r: return None
    E = [list(row) for row in zip(*[c for c in zip(*E) if any(c)])]  # drop primes absent from every row
    if not E or len(E[0]) < r: return None
    a = analyse(E)
    if a is None: return None
    piv, stages, frees = a
    if len(stages) < 2: return 'single'
    covs = min_covers(E)
    res = [sc_holds(E, stages, frees, C) for C in covs]
    return (E, stages, frees, covs, res)

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    stats = dict(tested=0, single=0, all_ok=0, some_fail=0, all_fail=0)
    examples = []
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 40000
    rmax = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    for _ in range(N):
        r = rng.randint(2, rmax); m = rng.randint(r + 1, r + 6)
        out = trial(r, m, rng.choice([1, 2, 3]), rng.choice([0.25, 0.35, 0.5, 0.65]), rng)
        if out is None: continue
        if out == 'single': stats['single'] += 1; continue
        stats['tested'] += 1
        E, stages, frees, covs, res = out
        if all(res): stats['all_ok'] += 1
        elif any(res): stats['some_fail'] += 1
        else:
            stats['all_fail'] += 1
            if len(examples) < 3: examples.append((E, stages, frees, covs))
    print(stats)
    for E, st, fr, cv in examples:
        print('E=', E); print(' stages', st, 'late frees', fr, 'min covers', cv)
