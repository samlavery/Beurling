"""Cover Bound, eq:coverbound's chain factor: for every C/R sequence (row kind of each pivot, latest first, first = C)
and every run structure, the EXACT discrete content sums of the #48/#55 scheme (all contents, carried function exact)
against the paper's bound (1 + kappa*lam)^{s_R} * kappa^kappa/kappa! * A^kappa, lam = log(A/Eu_rat).
Realised primes: random sets including tiny values; A = Eu after all primes (sharpest A_top)."""
import itertools, math, random

def compositions(k):
    if k == 0:
        yield (); return
    for f in range(1, k + 1):
        for r in compositions(k - f):
            yield (f,) + r

def fin_disc(js, primes, Erat):
    n = len(primes)
    sig = []
    E = Erat
    for g in primes:
        sig.append(E); E = E / (1 - 1 / g)
    A = E
    G = [1.0] * (n + 1)
    K = 0
    for jt in js[:-1]:
        Kp = K; K += jt
        new = [0.0] * (n + 1); acc = 0.0
        for i in range(n - 1, -1, -1):
            x = 1 - 1 / primes[i]
            acc += (x ** (-K) - 1) * x ** Kp * sig[i] ** jt * G[i + 1]
            new[i] = acc
        G = new
    jT = js[-1]; Kp = K; K += jT
    tot = Erat ** jT * G[0]
    for i in range(n):
        x = 1 - 1 / primes[i]
        tot += (x ** (-K) - 1) * x ** Kp * sig[i] ** jT * G[i + 1]
    return tot, A

rnd = random.Random(7)
worst = 0; viol = 0; cases = 0
for trial in range(60):
    pool = list(range(2, 3000))
    m = rnd.randint(3, 250)
    primes = sorted(rnd.sample(pool, m))
    Erat = rnd.choice([1.0, 2.0, 3.0])
    for r in range(1, 7):
        for seq in itertools.product('CR', repeat=r):
            if seq[0] != 'C': continue
            kappa = seq.count('C')
            for comp in compositions(r):
                pos = 0; js = []
                for size in comp:
                    js.append(sum(1 for c in seq[pos:pos + size] if c == 'C')); pos += size
                sR = sum(1 for j in js if j == 0)
                f, A = fin_disc(js, primes, Erat)
                lam = math.log(A / Erat)
                bound = (1 + kappa * lam) ** sR * kappa ** kappa / math.factorial(kappa) * A ** kappa
                cases += 1
                worst = max(worst, f / bound)
                if f > bound * (1 + 1e-12): viol += 1
print(f"Cover Bound chain factor: {cases} (prime set, C/R sequence, run structure) cases, {viol} violations, "
      f"max Fin/bound = {worst:.4f}")
