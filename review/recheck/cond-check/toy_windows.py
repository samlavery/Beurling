"""Pick per-row windows for toy_exact.py's types that maximise E[X] under always-decide (J-halves averaged)."""
import sys
sys.path.insert(0, '/tmp/rhscratch/cond-check/scripts')
from fractions import Fraction as Fr
import toy_exact as T

slots = T.make_slots(3, ['R', 'J'] * 7)
types = {
 'k2a': ([('P', 0), ('F', {0: 1}), ('P', 1), ('F', {0: 1, 1: 1})], 2),
 'k2b': ([('P', 0), ('F', {0: 1}), ('P', 1), ('F', {0: 1}), ('F', {1: 1})], 2),
 'k2c': ([('P', 0), ('P', 1), ('F', {0: 1}), ('F', {1: 1})], 2),
 'k2d': ([('P', 0), ('F', {0: 1}), ('F', {0: 1}), ('P', 1), ('F', {0: 1, 1: 1})], 2),
}
# always decide, average over halves = full-window average: build a single history with half=None handled
def full_sum(cols, k, Jw):
    hist = [(i, kind, 1, 0) for i, (s, kind) in enumerate(slots)]
    h2 = [(i, kind, 1, 1) for i, (s, kind) in enumerate(slots)]
    # average of lower and upper half results per pivot = full window; approximate by averaging the two extremes
    return (T.config_sum(slots, hist, Jw, cols, k) + T.config_sum(slots, h2, Jw, cols, k)) / 2
for name, (cols, k) in types.items():
    best = (0, None)
    for z1 in range(10, 1200, 7):
        for z2 in range(6, 120, 3):
            Jw = [(Fr(z1), Fr(z1 + 1)), (Fr(z2), Fr(z2 + 1))]
            v = full_sum(cols, k, Jw)
            if v > best[0]:
                best = (v, (z1, z2))
    print(name, float(best[0]), best[1])
