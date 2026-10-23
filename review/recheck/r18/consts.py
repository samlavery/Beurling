from fractions import Fraction as F
import math
print("C73-3 1/sqrt(0.99) =", 1/math.sqrt(0.99), "<= 1.006:", 1/math.sqrt(0.99) <= 1.006)
c = 2/0.49
print("C76-3 per-term 2/0.49 =", c, "; x1.0001 =", c*1.0001, "<= 4.2:", c*1.0001 <= 4.2)
# Work in logs with X0^2 = e^{2e8}: log(tail) = log 4.2 + X0^2 - 0.24 e^{X0^2} << -0.49 X0^2 + log 0.47.
# It suffices that 0.24 e^{w} >= 1.49 w + 3 for w = X0^2 >= 10: e^w grows faster.
w = 10.0
print("C76-3 sufficient condition at w=10:", 0.24*math.exp(w) >= 1.49*w + 3)
print("C76-3 0.51+2.02+0.47 =", 0.51+2.02+0.47)
print("C73-4 theta_b/100 <= 1/400:", F(1,4)/100 == F(1,400))
