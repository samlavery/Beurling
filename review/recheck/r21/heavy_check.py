"""Check the #85 counterexample to Lemma heavy (ii) in its v3 form (>= Q+r+1).

S in Z^3: (i,0,0) for i=1..111, (i,1,0) for 13 values of i, (i,0,1) for 31 values of i; c = 100.2, r_0 = 4.
phi(u) = c + u*Q + u(u+1)/2 with Q = sqrt(c).  Enumerate every subspace spanned by elements of S, find the heavy
ones and the least heavy dimension, and test (ii) old (>= Q+r+1) and new (> Q+r) for every least heavy V and every
proper element-spanned W' of V (including W' = {0}).
"""
import itertools
import math
from fractions import Fraction


def rank(vs):
    rows = [[Fraction(x) for x in v] for v in vs]
    r = 0
    ncol = 3
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def in_span(v, basis):
    return rank(basis + [v]) == rank(basis)


def run(offset2, offset3):
    S = [(i, 0, 0) for i in range(1, 112)]
    S += [(i, 1, 0) for i in range(offset2, offset2 + 13)]
    S += [(i, 0, 1) for i in range(offset3, offset3 + 31)]
    assert len(S) == 155 and len(set(S)) == 155 and all(v != (0, 0, 0) for v in S)
    c = 100.2
    Q = math.sqrt(c)
    phi = lambda u: c + u * Q + u * (u + 1) / 2
    r0 = 4
    assert rank(S) < r0 and len(S) >= r0 + phi(r0), (rank(S), len(S), r0 + phi(r0))

    # element-spanned subspaces, represented by their sets of members of S
    subspaces = {}
    subspaces[frozenset()] = 0  # {0}
    for v in S:
        members = frozenset(w for w in S if in_span(w, [v]))
        subspaces[members] = 1
    seen_planes = set()
    for a, b in itertools.combinations(range(len(S)), 2):
        if rank([S[a], S[b]]) < 2:
            continue
        key = None
        members = frozenset(w for w in S if in_span(w, [S[a], S[b]]))
        if members in seen_planes:
            continue
        seen_planes.add(members)
        subspaces[members] = 2
    subspaces[frozenset(S)] = rank(S)

    heavy = {m: d for m, d in subspaces.items() if len(m) >= phi(d)}
    rmin = min(heavy.values())
    print(f"offsets ({offset2},{offset3}): Q={Q:.5f}, phi(1..4)={[round(phi(u), 3) for u in range(1, 5)]}")
    print(f"  #lines={sum(1 for d in subspaces.values() if d == 1)}, #planes={len(seen_planes)}, heavy dims={sorted(set(heavy.values()))}, least r={rmin}")
    print(f"  max #(S cap line) = {max(len(m) for m, d in subspaces.items() if d == 1)} vs phi(1) = {phi(1):.3f}")
    old_fail = new_fail = 0
    worst = None
    for V, r in heavy.items():
        if r != rmin:
            continue
        for W, d in subspaces.items():
            if d < r and W <= V:
                cnt = len(V - W)
                if cnt < Q + r + 1:
                    old_fail += 1
                    worst = (len(V), len(W), cnt, Q + r + 1)
                if not cnt > Q + r:
                    new_fail += 1
    print(f"  least-dimension heavy V: {sum(1 for d in heavy.values() if d == rmin)} (sizes {sorted(len(V) for V, d in heavy.items() if d == rmin)})")
    print(f"  (ii) old >= Q+r+1 failures: {old_fail} (example |S cap V|, |S cap W'|, count, Q+r+1 = {worst})")
    print(f"  (ii) new  > Q+r   failures: {new_fail}")


if __name__ == "__main__":
    run(1, 1)
    run(0, 0)
