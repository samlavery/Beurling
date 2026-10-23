# Arithmetic of Lemma margin (b) Step 3 and (d)(iii), in ball arithmetic.
from flint import arb
eg = arb(0.5772156649015329).exp()
L = arb(10)**8                      # Lambda >= 1e8 (worst case for the 1/Lambda terms)
# (b): per replacement 10 k f0 log b/m + 2.75 k f0 log^2 b/m, f0 <= 1/Lambda
print("f0 per-replacement coeff of k log^2 u/(m Lam):", 2.75 + 10/L, "(paper: <= 4)")
tot_b = 4*arb(1.01)*eg               # times (1+l)e^l log^2 u kappa
print("4*1.01*e^gamma =", tot_b, "(paper 4.1 e^gamma; then 7.4)")
print("(b) final at loglog u = Lam/8: 7.4(1+Lam/8)/Lam =", 7.4*(1+L/8)/L, "(<= 1)")
# (d)(iii): per replacement: boundary 2*5*0.51 log b, smooth 5.5*0.51/2 log^2 b (+ log b), variation 5*3.1 log b (log(b/a)+1) <= 15.5 log^2 b
bd, sm, var = 2*5*arb(0.51), 5.5*arb(0.51)/2, 5*arb(3.1)
print("g per-replacement: log^2 coeff", sm + var, "+ log coeff", bd + 5*arb(0.51), "/log u -> total <=", sm + var + (bd+5*arb(0.51))/L, "(paper 17)")
c17 = 17*arb(1.01)*eg
print("17*1.01*e^gamma*(1/Lam + 1/8) =", c17*(1/L + arb(1)/8), "(paper: <= 4)")
# with the hybrid correction factor (1 + 10/Lambda)
print("  with (1+10/Lam):", c17*(1/L + arb(1)/8)*(1+10/L))
# final chain
X0log = L  # log X0 = Lambda
kap_exp = arb(-0.3967)
print("4.1 kappa (log x)^5 at log x = X0^(1/100): exponent of X0:", kap_exp + 5*arb(0.01), "; 4.1 X0^(-0.3467) <= X0^(-0.34) iff log 4.1 <= 0.0067 Lam:", arb(4.1).log() <= arb(0.0067)*L)
print("|g| log x at x = X0^1.01/2: 1.0001*(1.01 - log2/Lam)*2 =", arb(1.0001)*(arb(1.01) - arb(2).log()/L)*2, "* X0^-0.01 (paper 3)")
print("range (A) top: 0.99 - 6e-4 - 0.167 =", arb(0.99) - arb(6e-4) - arb(0.167), "(>= 0.822 after X0^-0.34, e^-80)")
print("pointwise (b): 0.822 - 0.4209 - 1e-12 =", arb(0.822) - arb(0.4209) - arb(10)**-12)
print("Cor r1: 1.01 c' =", 1.01*arb(0.15))
