"""The family  n1 = p1*g*c*d1,  n2 = p1*p2*g*d2,  n3 = p3*d3  (decision order p1 > g > p2 > c > p3),
tested in the toy world of toy_exact.py / toy_pattern.py:
  J-slots (jittered pivots, H = 2) at even positions 4..2M, R-slots (free primes, rigid values) at odd
  positions 3..2M+1, every slot decided and G = 1 (this maximises E[X; Good] over all adaptive decision rules
  and good events, since X is monotone in the decided set and the U_j are i.i.d.).  Tails d_i = 1.
Pivot pattern E_P (rows x pivots p1,p2,p3) = [[1,0,0],[1,1,0],[0,0,1]], |det| = 1, column sums (2,1,1).

Computed:
 (T)  the true E over the union of ALL free structures with this pivot pattern and pivot order (gap (p2,p1): primes
      with exponent vector e(1,1,0); gap (p3,p2): any (a,b,0); below p3: any (a,b,c)); exact up to float logs;
 (Tf) the true E restricted to the family's shape (one g in gap 1 shared by rows 1,2; row-1-only primes c in gap 2,
      any number r >= 1; nothing else);
 (B)  Thm R's per-pattern bound, as the paper sums it (patterns only, no type count):
      theta^3 * delta^3 * A_top^3 * tau_{p1}^{-1} / |det E_P|;
 (S)  the per-type PIL envelope (same number per type) times the number of feasible full types;
 (48) the sharpest per-pattern value of the #48 scheme: theta^3 delta^3 tau^{-1} * sum over run structures of Final;
 (Rf) for the family's block F_2 alone (passing owner = row 1, r varying): sum_r of the exact-count terms,
      i.e. sum over nonempty sets S of prod 1/g * Eu(a)/Eu(u(max S)), against the per-type value <= 1 and E|R|.
"""
import math
import sys
sys.path.insert(0, '/tmp/rhscratch/cond-check/scripts')
import pattern_sum as PS

H = 2.0
M = 12
Jpos = [float(p) for p in range(4, 2 * M + 1, 2)]
Rval = [float(v) for v in range(3, 2 * M + 2, 2)]
theta = 0.5


def ov(a, b, c, d):
    lo, hi = max(a, c), min(b, d)
    return hi - lo if hi > lo else 0.0


def inner_integral(w1lo, w1hi, w2lo, w2hi, A, B):
    """int_{w1lo}^{w1hi} |[w2lo,w2hi) cap [A/q, B/q)| dq, exactly (piecewise, with logs)."""
    if w1hi <= w1lo:
        return 0.0
    pts = sorted(set([w1lo, w1hi] + [x for x in (A / w2lo, A / w2hi, B / w2lo, B / w2hi) if w1lo < x < w1hi]))
    tot = 0.0
    for a, b in zip(pts, pts[1:]):
        m = 0.5 * (a + b)
        lo_is_A = A / m > w2lo
        hi_is_B = B / m < w2hi
        lo_val = A / m if lo_is_A else w2lo
        hi_val = B / m if hi_is_B else w2hi
        if hi_val <= lo_val:
            continue
        L = math.log(b / a)
        hi_int = B * L if hi_is_B else w2hi * (b - a)
        lo_int = A * L if lo_is_A else w2lo * (b - a)
        tot += hi_int - lo_int
    return tot


def multisets(vals, cap):
    out = [((), 1.0)]
    def rec(start, cur, prod):
        for i in range(start, len(vals)):
            p = prod * vals[i]
            if p > cap * (1 + 1e-12):
                break
            t = cur + (vals[i],)
            out.append((t, p))
            rec(i, t, p)
    rec(0, (), 1.0)
    return out


def true_E(J1, J2, J3, family_only=False):
    E = 0.0
    types = set()
    for i1, s1 in enumerate(Jpos):
        for i2 in range(i1):
            s2 = Jpos[i2]
            for i3 in range(i2):
                s3 = Jpos[i3]
                G1 = [v for v in Rval if s2 < v < s1]
                G2 = [v for v in Rval if s3 < v < s2]
                G0 = [v for v in Rval if v < s3]
                q1min, q2min, q3min = s1 - H / 2, s2 - H / 2, s3 - H / 2
                cap1 = J1[1] / q1min
                cap2 = J2[1] / (q1min * q2min)
                cap3 = J3[1] / q3min
                for m1, P1 in multisets(G1, min(cap1, cap2)):
                    if family_only and len(m1) != 1:
                        continue
                    for m1b, P1b in multisets(G2 + G0, cap1 / P1):
                        if family_only and (len(m1b) == 0 or any(v not in G2 for v in m1b)
                                            or len(set(m1b)) != len(m1b)):
                            continue
                        C1 = P1 * P1b
                        for m2b, P2b in multisets(G2 + G0, cap2 / P1):
                            if family_only and len(m2b) != 0:
                                continue
                            C2 = P1 * P2b
                            I12 = inner_integral(max(s1 - H / 2, J1[0] / C1), min(s1 + H / 2, J1[1] / C1),
                                                 s2 - H / 2, s2 + H / 2, J2[0] / C2, J2[1] / C2) / H ** 2
                            if I12 == 0:
                                continue
                            for m3, C3 in multisets(G0, cap3):
                                if family_only and len(m3) != 0:
                                    continue
                                I3 = ov(s3 - H / 2, s3 + H / 2, J3[0] / C3, J3[1] / C3) / H
                                if I3 == 0:
                                    continue
                                E += I12 * I3
                                cols = {}
                                for v in m1:
                                    cols.setdefault(v, [0, 0, 0]); cols[v][0] += 1; cols[v][1] += 1
                                for v in m1b:
                                    cols.setdefault(v, [0, 0, 0]); cols[v][0] += 1
                                for v in m2b:
                                    cols.setdefault(v, [0, 0, 0]); cols[v][1] += 1
                                for v in m3:
                                    cols.setdefault(v, [0, 0, 0]); cols[v][2] += 1
                                seq = sorted([(s1, 'p1'), (s2, 'p2'), (s3, 'p3')] +
                                             [(v, tuple(e)) for v, e in cols.items()], reverse=True)
                                types.add(tuple(x[1] for x in seq))
    return E, types


def main():
    Atop = 1.0
    for v in Rval:
        Atop /= (1 - 1 / v)
    tau_p1 = Jpos[2] - H / 2        # p1 is the 3rd earliest pivot
    B = theta ** 3 * Atop ** 3 / tau_p1
    S48 = sum(PS.final_disc(c, Rval, 1.0)[0] for c in PS.compositions(3)) * theta ** 3 / tau_p1
    print(f"toy: J-slots {Jpos[0]:.0f}..{Jpos[-1]:.0f}, R-values {Rval[0]:.0f}..{Rval[-1]:.0f}, theta={theta}, "
          f"A_top={Atop:.4f}, tau_p1={tau_p1}")
    print(f"(B)  Thm R per-pattern bound theta^3 delta^3 A^3/tau = {B:.4f}")
    print(f"(48) sharpest #48 per-pattern value                  = {S48:.4f}   ratio to (B) {S48 / B:.3f}")
    print(f"\n{'J1':>12} {'J2':>12} {'J3':>10} {'(T) all':>10} {'(Tf) family':>12} {'#types':>7} {'(S)=#types*B':>13}")
    best = []
    for z1 in range(100, 4000, 61):
        for z2 in range(100, 6000, 89):
            J1, J2, J3 = (z1, z1 + 1.0), (z2, z2 + 1.0), (4.0, 5.0)
            E, ty = true_E(J1, J2, J3, family_only=True)
            if E > 0:
                best.append((E, z1, z2))
    best.sort(reverse=True)
    for E, z1, z2 in best[:6]:
        J1, J2, J3 = (z1, z1 + 1.0), (z2, z2 + 1.0), (4.0, 5.0)
        Eall, tall = true_E(J1, J2, J3)
        print(f"{str(J1):>12} {str(J2):>12} {str(J3):>10} {Eall:10.5f} {E:12.5f} {len(tall):7d} {len(tall) * B:13.3f}")

    # (Rf): passing owner in block F_2, r varying; a = slot just above p3, primes = R-values above it
    print("\n(Rf) block F_2 of the family: passing owner (row 1), union over r of the exact-count terms")
    for a_idx in range(0, 4):
        primes = Rval[a_idx:]
        Eu = 1.0
        sig, u = [], []
        for g in primes:
            sig.append(Eu); Eu /= (1 - 1 / g); u.append(Eu)
        Eu_a = 1.0
        # sum over nonempty S with max element primes[i]: prod_{S} 1/g * Eu_a / Eu(u_i)
        #   = (1/g_i) * prod_{l<i} (1 + 1/g_l) * Eu_a / u_i
        tot, Pp = 0.0, 1.0
        for i, g in enumerate(primes):
            tot += Pp / g * Eu_a / u[i]
            Pp *= (1 + 1 / g)
        ER = sum(1 / g for g in primes)
        print(f"  primes from {primes[0]:.0f}: union sum = {tot:.4f} (per type <= 1),  E|R| = sum 1/g = {ER:.4f},  "
              f"Eu ratio = {u[-1]:.3f}")


if __name__ == "__main__":
    main()
