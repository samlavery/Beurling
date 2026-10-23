import sys
from fractions import Fraction as F
sys.path.insert(0, sys.argv[1])
from toy import build_random
fails = {}; cnt_ok = 0; empty_jump = 0
for seed in range(10):
    for theta in (F(1, 2), F(1, 3)):
        P = build_random(seed, theta=theta, p_double=0.3)
        X0 = P.X0; jmax = int(P.T) - 3
        s = {j: P.hit(j + theta) for j in range(X0, jmax + 2)}
        kind = {j: ('jump' if P.Tval(s[j], left=True) < j + theta else 'cont') for j in range(X0, jmax + 1)}
        empty_jump += sum(1 for j in kind if kind[j] == 'jump' and s[j] == s[j + 1])
        conts = [j for j in kind if kind[j] == 'cont']
        for a, b in zip(conts, conts[1:]):
            m = P.cmass(s[b]) - P.cmass(s[a])
            if m == 1: cnt_ok += 1
            else: fails[(seed, a, b)] = m
print("on N_0: counting-fact holds in", cnt_ok, "gaps, fails in", len(fails), "; empty 'jump slots' (A_j = 0):", empty_jump)
