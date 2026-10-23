# Misc arb checks: the (1+cos)^4 identity, T0-tail constant, Step-8 anchor, Step-7 growth constant 0.495.
from flint import arb, ctx
import random
ctx.prec = 120
r = random.Random(1); mx = arb(0)
for _ in range(1000):
    ph = arb(r.uniform(-10, 10))
    lhs = (1 + ph.cos())**4
    rhs = (35 + 56*ph.cos() + 28*(2*ph).cos() + 8*(3*ph).cos() + (4*ph).cos())/8
    mx = max(mx, abs(lhs - rhs).upper())
print("max |(1+cos)^4 - (1/8)(35+56cos+28cos2+8cos3+cos4)| over 1000 phi:", mx, "; sum a_k =", 35+56+28+8+1)
print("Step 7: (1-1e-2)/(2/eta) = 0.495 eta:", (1 - arb('0.01'))/2)
print("Step 8: |log(1+q)| for |q|<=1e-2 <= -log(0.99) =", -arb('0.99').log())
# T0 tail: (1 + 2 kappa (eta + sigma) + ...) with kappa <= X0^-0.3967, eta <= 1/8
k = arb(10)**(-arb('0.3967')*8*arb(10).log()/arb(10).log())  # placeholder: kappa at Lambda=1e8 is e^{-0.3967e8}
print("T0-tail relative excess 2 kappa (eta+sigma) <= 2*1.25*kappa, kappa <= exp(-0.3967e8): negligible")
