"""(#33) w_a bounds (ii)-(iv) of 03-zeros in ball arithmetic (python-flint), avoiding cancellation."""
from flint import arb, acb, ctx
ctx.prec = 400
def ua_of(a, b):
    u = a - a ** b
    for _ in range(200):
        u = a - u ** b
    return u
viol = 0; n = 0; worst = [arb(0), arb(0), arb(0)]
for b in (arb(1)/8, arb("0.2"), arb("0.2499")):
    for e in (5, 6, 8, 10, 12, 20):
        a = arb(10) ** e
        ua = ua_of(a, b); eps = a ** (b - 1)
        for sig in ("0", "0.25", "0.5", "0.9", "1", "1.1", "1.5", "2"):
            for t in ("0", "0.5", "1", "2", "10", "1e3", "1e5", "1e7", "1e12"):
                s = acb(arb(sig), arb(t))
                den = 1 - s - b
                w = acb(a) ** s * (acb(a) ** (1 - s - b) - acb(ua) ** (1 - s - b)) / den
                n += 1
                r2 = abs(w) / (1 + arb("1.02") * arb(sig) * eps)
                r4 = abs(1 - w) / (arb("1.01") * (abs(s) + b) * eps)
                ok = (r2 <= 1) and (r4 <= 1)
                if arb(t) > 0:
                    r3 = abs(w) / (arb("2.01") * a ** (1 - b) / arb(t))
                    ok = ok and (r3 <= 1)
                    worst[1] = max(worst[1], r3.upper()) if hasattr(r3, 'upper') else worst[1]
                if not ok:
                    viol += 1
                    print("VIOL", b, e, sig, t, r2, r4)
print(f"w_a (ii)-(iv) in arb: {n} points, {viol} violations")
