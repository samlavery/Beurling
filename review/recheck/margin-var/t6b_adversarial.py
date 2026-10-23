# T6b: an admissible-looking pair of prime systems with equal l_A = l_B where the mixed ordered hybrid sum exceeds the
# single-system multiset bound (l + (r+s) b)^{r+s}/(r+s)!  -- the Step-3 justification does not cover hybrids as written.
# A: rational primes >= X0 thinned (keep prob 1-delta) below the log-log midpoint, thickened (+delta') above, so l_A = l_B.
import sys, math, random
sys.path.insert(0, '/tmp/rhscratch/margin-var-check/scripts')
from t6_mixed import mixed
from toy_common import sieve_spf
X0, U = 1000, 10**7
spf = sieve_spf(U)
B = [float(p) for p in range(X0, U + 1) if spf[p] == p]
mid = math.exp(math.sqrt(math.log(X0) * math.log(U)))
rnd = random.Random(1)
for delta in (0.05, 0.1, 0.2):
    lo = [p for p in B if p < mid]; hi = [p for p in B if p >= mid]
    A = [p + rnd.uniform(-0.5, 0.5) for p in lo if rnd.random() > delta]
    need = sum(1 / p for p in B) - sum(1 / p for p in A)
    A += [p + rnd.uniform(-0.5, 0.5) for p in hi]
    have = sum(1 / p for p in hi)
    extra = need - have
    # add extra primes in the upper range at random points until l_A = l_B
    while extra > 0:
        t = math.exp(rnd.uniform(math.log(mid), math.log(U)))
        A.append(t); extra -= 1 / t
    A.sort()
    S, lA, lB = mixed(A, B, U, 4)
    l = max(lA, lB); b = 1 / (X0 - 1)
    # Mertens-type discrepancy actually used: sup_t |L_A(t) - L_B(t)|
    pts = sorted([(p, 1) for p in A] + [(p, -1) for p in B]); acc = 0; mx = 0
    for p, s in pts:
        acc += s / p; mx = max(mx, abs(acc))
    for (r, s) in [(1, 1), (2, 1), (1, 2), (2, 2)]:
        bnd = (l + (r + s) * b) ** (r + s) / math.factorial(r + s)
        print(f"delta={delta}: l_A={lA:.5f} l_B={lB:.5f} sup|L_A-L_B|={mx:.4f}  (r,s)=({r},{s}) "
              f"S_mixed={S[r][s]:.5f} single-system bound={bnd:.5f} ratio={S[r][s]/bnd:.4f}")
