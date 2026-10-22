# Check the explicit construction: R_<=t := lex-first basis of M_t (rows restricted to P_<=t), C rows ordered first.
# Claims: (1) nested; (2) |R_<=t| = |P_<=t| and E[R_<=t, P_<=t] invertible; (3) C ∩ R_<=t covers P_<=t ∪ F_<=t.
import sys, random
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from sc_check import rank, analyse, min_covers
def greedy_basis(E, cols, order):
    B = []
    for i in order:
        if rank([[E[k][j] for j in cols] for k in B + [i]]) > len(B): B.append(i)
    return B
def check(E, stages, frees, C):
    r = len(E); order = [i for i in range(r) if i in C] + [i for i in range(r) if i not in C]
    prev = set(); Pt = []; Ft = []
    for t in range(len(stages)):
        Pt += stages[t]; Ft += frees[t]
        B = greedy_basis(E, Pt, order)
        if len(B) != len(Pt) or not prev <= set(B): return 'nest/size'
        if not all(any(E[i][j] for i in B if i in C) for j in Pt + Ft): return 'cover'
        prev = set(B)
    return 'ok'
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); rmax = int(sys.argv[3])
    from collections import Counter; cnt = Counter()
    for _ in range(N):
        r = rng.randint(2, rmax); m = rng.randint(r + 1, r + 6)
        E = [[(rng.randint(1, rng.choice([1,2,3])) if rng.random() < rng.choice([.25,.35,.5,.65]) else 0) for _ in range(m)] for _ in range(r)]
        if rank(E) < r: continue
        E = [list(row) for row in zip(*[c for c in zip(*E) if any(c)])]
        if not E or len(E[0]) < r: continue
        a = analyse(E)
        if a is None: continue
        piv, stages, frees = a
        if len(stages) < 2: continue
        for C in min_covers(E): cnt[check(E, stages, frees, set(C))] += 1
    print(dict(cnt))
