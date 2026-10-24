# The cutoff phi of eq:Rk (Section sec:target): phi(t) = psi(t)/(psi(t) + psi(1-t)), with psi(t) = exp(-1/t) for t > 0 and
# psi(t) = 0 for t <= 0. Certifies sup|phi''| <= 10 (the value is 9.841..., near t = 0.7817), and cross-checks the analytic
# bound sup|phi'| <= 2 of the text (equality at t = 1/2). Needs python-flint 0.9.0 (Arb ball arithmetic).
# Run:  python3 -I -B certificates/constants/phi_bounds.py
#
# Method.
# * On (0,1), phi = 1/(1 + e^g) with g(t) = 1/t - 1/(1-t). On [0.02, 0.98], phi' and phi'' are enclosed by Taylor arithmetic
#   (arb_series of length 3) at a ball covering a whole cell, so each enclosure holds for every t in the cell. A cell whose
#   enclosure does not decide the bound is bisected. No derivative formula is typed in by hand.
# * On (0, 0.02]: g > 0, so phi(1-phi) <= phi <= e^{-g}; with q := -g' = 1/t^2 + 1/(1-t)^2 and q' = -2/t^3 + 2/(1-t)^3,
#   phi' = phi(1-phi) q and phi'' = phi(1-phi)((1-2phi) q^2 + q'), so phi' <= e^{-g} q and |phi''| <= e^{-g}(q^2 + |q'|).
#   There e^{-g} <= e^{1/0.98} e^{-1/t}, q <= 1/t^2 + 1/0.98^2 and |q'| <= 2/t^3 + 2/0.98^3; every term e^{-1/t} t^{-k}
#   (k <= 6) increases on (0, 1/6], so the bounds at t = 0.02 hold on all of (0, 0.02].
# * On [0.98, 1): phi(1-t) = 1 - phi(t), so phi'(1-t) = phi'(t) and phi''(1-t) = -phi''(t).
# * Outside (0,1), phi is constant; at 0 and 1 every derivative of phi vanishes (psi is flat at 0).
from flint import arb, arb_series, ctx

ctx.prec = 80


def derivs(t):
    """Enclosures of (phi(t), phi'(t), phi''(t)) for every t in the ball t (0 < t < 1)."""
    x = arb_series([t, 1], prec=3)
    g = x.inv() - (1 - x).inv()
    phi = (1 + g.exp()).inv()
    c = phi.coeffs() + [arb(0)] * 3              # coeffs() drops trailing exact zeros
    return c[0], c[1], 2 * c[2]


B1, B2 = arb(2) + arb("1e-3"), arb(10)          # phi' is checked against 2.001 here (the text proves <= 2 analytically)
cells = [(arb(i) / 1000, arb(i + 1) / 1000) for i in range(20, 980)]
n_eval, n_split, sup1, sup2 = 0, 0, arb(0), arb(0)
while cells:
    a, b = cells.pop()
    t = (a + b) / 2 + arb(0, ((b - a) / 2).upper())
    _, d1, d2 = derivs(t)
    n_eval += 1
    u1, u2 = abs(d1).upper(), abs(d2).upper()
    if (arb(u1) <= B1 and arb(u2) <= B2) or n_split > 10 ** 6:
        sup1, sup2 = max(sup1, arb(u1)), max(sup2, arb(u2))
        continue
    m = (a + b) / 2
    cells += [(a, m), (m, b)]
    n_split += 1
ok_mid = sup1 <= B1 and sup2 <= B2
print("c1  [0.02,0.98]: %d cells evaluated, %d bisections" % (n_eval, n_split))
print("c2  [0.02,0.98]: largest cell bound for |phi'| = %s (<= 2.001: %s), for |phi''| = %s (<= 10: %s)"
      % (sup1.str(6), sup1 <= B1, sup2.str(6), sup2 <= B2))
t0 = arb("0.02")
eg = (1 / arb("0.98")).exp() * (-1 / t0).exp()
q = 1 / t0 ** 2 + 1 / arb("0.98") ** 2
dq = 2 / t0 ** 3 + 2 / arb("0.98") ** 3
e1, e2 = eg * q, eg * (q * q + dq)
print("c3  (0,0.02], analytic: phi' <= %s, |phi''| <= %s: %s" % (e1.str(4), e2.str(4), e1 < 1 and e2 < 1))
_, h1, _ = derivs(arb("0.5"))
_, _, p2 = derivs(arb("0.7817"))
print("c4  values: phi'(1/2) = %s; phi''(0.7817) = %s" % (h1.str(10), p2.str(8)))
print("c5  sup|phi'| <= 2 (analytic, cross-checked to 2.001) and sup|phi''| <= 10 on R: %s" % (ok_mid and e1 < 1 and e2 < 1))
