"""R3 toy: exact E[X_s] per Cover-Bound skeleton against (theta*delta)^r * Sigma-bar_s of eq:coverbound (#55).
Configuration: r = 2 rows, C = {C-row}, R = {R-row}, kappa = 1.
  pivots q_a (later) and q_b (earlier) on jittered J-slots (H = 2, positions 4,6,..);
  C-row  n_C = q_a * q_b * (free primes, any exponents >= 1) * d_C,     d_C summed (rational primes {2});
  R-row  n_R = q_b^2 * (some early free primes of the C-row, by label, exponents >= 1) * d_R,   d_R fixed by (s4).
Free primes are rigid R-slot primes (odd positions 3,5,..). Free primes decided between q_b and q_a can only lie in the
C-row (span); early ones (before q_b) may also lie in the R-row. Both rows in one window J = [z, z+1).
Skeleton (s1)-(s4): C-row index (fixed here), labels of q_b and q_a = numbers e0 (early) and e1 (between) of free primes,
pivot exponents in C (1,1: no excess), R-row monomial in labels (which early labels, exponents) and d_R.
Bound: (theta delta)^2 * (1+lam)^{s_R} * A_top * z^{-1},  s_R = 1 iff e1 >= 1 (two runs; R-row joins alone).
Every slot decided, G = 1 (maximises E[X;Good])."""
import math, itertools, sys
sys.path.insert(0, '/tmp/rhscratch/cond-check/scripts')
from toy_family import inner_integral

H = 2.0
Jpos = [float(p) for p in range(4, 25, 2)]
Rval = [float(v) for v in range(3, 26, 2)]
RAT = [2.0]
theta = 0.5

def smooth_upto(cap):           # tails: products of rational primes {2}
    out = []; d = 1.0
    while d <= cap: out.append(d); d *= 2
    return out

def run(z):
    J = (z, z + 1.0)
    Erat = 1.0
    for p in RAT: Erat /= (1 - 1 / p)
    Atop = Erat
    for v in Rval: Atop /= (1 - 1 / v)
    lam = math.log(Atop / Erat)
    per = {}     # skeleton -> true E
    for ia, sa in enumerate(Jpos):
        for sb in Jpos[:ia]:
            G1 = [v for v in Rval if sb < v < sa]      # between: C-row only
            G0 = [v for v in Rval if v < sb]           # early
            qa_min, qb_min = sa - H / 2, sb - H / 2
            # enumerate subsets with exponents: C-row free part
            def choices(vals, cap):
                res = [((), 1.0)]
                for v in vals:
                    new = []
                    for (t, p) in res:
                        new.append((t, p)); e = 1; pp = p * v
                        while pp <= cap:
                            new.append((t + ((v, e),), pp)); e += 1; pp *= v
                    res = new
                return res
            capC = J[1] / (qa_min * qb_min)
            for c1, P1 in choices(G1, capC):
                for c0, P0 in choices(G0, capC / P1):
                    # R-row: subset of early free primes of the C-row (those in c0), exponents >= 1
                    early = [v for (v, e) in c0]
                    capR = J[1] / (qb_min ** 2)
                    for rs, PR in choices(early, capR):
                        for dR in smooth_upto(capR / PR):
                            for dC in smooth_upto(capC / (P1 * P0)):
                                FC = P1 * P0 * dC
                                MR = PR * dR
                                # q_b in W_b with q_b^2 * MR in J ; q_a in W_a with q_a*q_b*FC in J
                                lo_b = max(sb - H / 2, math.sqrt(J[0] / MR)); hi_b = min(sb + H / 2, math.sqrt(J[1] / MR))
                                if hi_b <= lo_b: continue
                                I = inner_integral(lo_b, hi_b, sa - H / 2, sa + H / 2, J[0] / FC, J[1] / FC) / H ** 2
                                if I <= 0: continue
                                e0 = len(c0); e1 = len(c1)
                                labels = {v: k + 1 for k, v in enumerate(sorted([v for v, _ in c0]))}
                                Rmono = tuple(sorted((labels[v], e) for v, e in rs))
                                key = (e0, e1, Rmono, dR)
                                per[key] = per.get(key, 0.0) + I
    viol = 0; worst = 0.0
    bsum = 0.0
    for (e0, e1, Rm, dR), E in per.items():
        sR = 1 if e1 >= 1 else 0
        bound = (theta * 1.0) ** 2 * (1 + lam) ** sR * Atop / z
        worst = max(worst, E / bound); viol += E > bound
        bsum += bound
    return len(per), viol, worst, sum(per.values()), bsum, Atop, lam

for z in (60.0, 120.0, 200.0, 330.0, 500.0, 800.0):
    n, viol, worst, Etot, bsum, Atop, lam = run(z)
    print(f"z={z:6.0f}: {n:4d} skeletons with E>0, {viol} violations, max E/bound = {worst:.4f}; "
          f"sum E = {Etot:.4e}, sum of per-skeleton bounds = {bsum:.3f} (A_top={Atop:.3f}, lam={lam:.3f})")
