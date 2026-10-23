"""(1) exact identity sum_comp Final(rho=0) = k^k/k!; (2) sup over rho in [0,1] attained at rho=0 (grid);
(3) discrete recursion <= continuous model on random prime sets; (4) cor:R-Ecl margin with an extra
factor k^k/k! <= e^k per pattern."""
import sys, math, random
sys.path.insert(0, '/tmp/rhscratch/cond-check/scripts')
from fractions import Fraction as Fr
import pattern_sum as P

for k in range(1, 13):
    s = sum(P.final_cont(c, Fr(0)) for c in P.compositions(k))
    assert s == Fr(k ** k, math.factorial(k)), (k, s)
print("identity sum_comp Final(0) = k^k/k! holds exactly for k = 1..12")

worst = 0
for k in range(2, 9):
    comps = list(P.compositions(k))
    v0 = sum(P.final_cont(c, Fr(0)) for c in comps)
    for i in range(1, 101):
        r = Fr(i, 100)
        v = sum(P.final_cont(c, r) for c in comps)
        worst = max(worst, float(v / v0))
print(f"max over rho in (0,1] of sum_comp Final(rho) / sum_comp Final(0), k=2..8: {worst:.6f}")

random.seed(1)
viol = 0; n = 0; maxr = 0
for trial in range(300):
    m = random.randint(5, 400)
    vals = sorted(random.sample(range(3, 5000), m))
    Erat = random.choice([1.0, 2.0, 5.0])
    for k in (2, 3, 4):
        for c in P.compositions(k):
            fd, Atop = P.final_disc(c, [float(v) for v in vals], Erat)
            rho = Fr(Erat / Atop).limit_denominator(10 ** 12)
            fc = float(P.final_cont(c, rho)) * Atop ** k
            n += 1
            maxr = max(maxr, fd / fc)
            if fd > fc * (1 + 1e-12):
                viol += 1
print(f"discrete <= continuous: {n} (prime set, k, structure) cases, {viol} violations, max ratio {maxr:.6f}")

# cor:R-Ecl with extra factor per element: original 15 L^{-3.98}; with e: 15e L^{-3.98}
def margin(L, c):
    l = math.log(L)
    r0 = math.ceil(L / (3 * l)) + 3
    lhs = L + 6 * l + r0 * (math.log(c) - 3.98 * l)   # log(2z/delta * RHS) bound, exact r0
    return lhs, -4 * l
for c in (15, 15 * math.e):
    bad = [L for L in [465, 500, 600, 800, 1000, 1e4, 1e6, 1e8, 1e12] if margin(L, c)[0] > margin(L, c)[1]]
    print(f"cor:R-Ecl per-element constant {c:.2f}: failures at L in {bad}  "
          f"(L=465: {margin(465, c)[0]:.1f} vs {margin(465, c)[1]:.1f})")
