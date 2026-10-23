"""Toy 2: Lemma T1's absorbed part (#34) and the w_a bounds (#33), exact/closed form.
(a) For random point sets Abs in [X, Xmax] and h(u) = u^b: exact identity
      #Abs(<=x) - int_X^x rho = sum_{a<=x}(1-M_a) - sum_{u_a<x<a} int_{u_a}^x du/h,
    and the two bounds used:  0 <= 1-M_a <= 1.01 b a^{b-1};  sum_{a<=x} a^{b-1} <= 1.001 int u^{b-1} rho(u) du.
(b) w_a(s) = a^s int_{u_a}^a u^{-s} u^{-b} du in closed form; check (ii) |w_a| <= 1 + 1.02 sigma eps,
    (iii) |w_a| <= 2.01 a^{1-b}/|t|, (iv) |1-w_a| <= 1.01(|s|+b) eps, eps = a^{b-1}, over a grid of a, s."""
import math, random, cmath

def ua_of(a, b):
    u = a - a ** b
    for _ in range(60):                       # solve u + u^b = a
        u = a - u ** b
    return u

def partA():
    rnd = random.Random(3)
    worst = 0.0; viol = 0; n = 0
    for trial in range(300):
        b = rnd.choice([0.125, 0.2, 0.2499])
        X, Xmax = 1e6, 1e6 * rnd.choice([3, 10, 100])
        m = rnd.randint(5, 400)
        A = sorted(rnd.uniform(X * 1.01, Xmax) for _ in range(m))
        for x in [X * 1.02 + (Xmax - X) * k / 7 for k in range(1, 8)]:
            def H_(u): return u ** (1 - b) / (1 - b)       # antiderivative of 1/h
            lhs = sum(1 for a in A if a <= x)
            integ = 0.0; s1 = 0.0; s2 = 0.0; s3 = 0.0; s4 = 0.0
            for a in A:
                ua = ua_of(a, b)
                Ma = H_(a) - H_(ua)
                if a <= x:
                    integ += Ma; s1 += 1 - Ma
                    if not (-1e-12 <= 1 - Ma <= 1.01 * b * a ** (b - 1)): viol += 1
                    s3 += a ** (b - 1)
                    # 1.001 * int_{ua}^{a} u^{b-1}/h du = 1.001 * int u^{-1} du = 1.001 log(a/ua)
                    s4 += 1.001 * math.log(a / ua)
                elif ua < x:
                    part = H_(x) - H_(ua)
                    integ += part; s2 += part
                n += 1
            if abs((lhs - integ) - (s1 - s2)) > 1e-6: viol += 1
            if s3 > s4 * (1 + 1e-12): viol += 1
            worst = max(worst, s3 / s4 if s4 else 0)
    print(f"Toy 2a (T1 absorbed part): {n} (set, x, a) evaluations, {viol} violations; "
          f"max sum a^(b-1) / (1.001 int u^(b-1) rho) = {worst:.6f}")

def partB():
    viol = 0; n = 0
    worst = [0, 0, 0]
    for b in (0.125, 0.2, 0.2499):
        for a in [10 ** e for e in (6, 7, 8, 9, 10, 12)]:
            ua = ua_of(a, b); eps = a ** (b - 1)
            for sig in [0.0, 0.25, 0.5, 0.9, 1.0, 1.1, 1.5, 2.0]:
                for t in [0.0, 0.5, 1.0, 2.0, 10.0, 1e3, 1e5, 1e7]:
                    s = complex(sig, t)
                    if abs(1 - s - b) < 1e-12: continue
                    w = a ** s * (a ** (1 - s - b) - ua ** (1 - s - b)) / (1 - s - b)
                    n += 1
                    r2 = abs(w) / (1 + 1.02 * sig * eps)
                    r4 = abs(1 - w) / (1.01 * (abs(s) + b) * eps)
                    worst[0] = max(worst[0], r2); worst[2] = max(worst[2], r4)
                    if r2 > 1 + 1e-9 or r4 > 1 + 1e-9: viol += 1
                    if t != 0:
                        r3 = abs(w) / (2.01 * a ** (1 - b) / abs(t))
                        worst[1] = max(worst[1], r3)
                        if r3 > 1 + 1e-9: viol += 1
    print(f"Toy 2b (w_a bounds (ii)-(iv)): {n} (b,a,s) points, {viol} violations; max ratios "
          f"(ii) {worst[0]:.6f}, (iii) {worst[1]:.6f}, (iv) {worst[2]:.6f}")

partA(); partB()
