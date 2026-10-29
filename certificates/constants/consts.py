# Numerical constants quoted in the text (Sections 5.5, 5.6 and 7) that no other certificate computes.
# Needs python-flint 0.9.0 (Arb ball arithmetic). Run:  python3 -I -B certificates/constants/consts.py
#
# Every quantity is an Arb ball that contains the true value; every comparison with the bound used in the paper is
# decided on the ball (True means the whole ball satisfies it). The integrals I_2 and I_3 are rigorous: I_2 by Arb's
# certified integration (acb.integral) on a finite range plus an explicit tail bound, I_3 in closed form.
from flint import arb, acb, arb_series, ctx

ctx.prec = 128


def zeta(s):
    return arb(s).zeta()


def dzeta(s):
    """zeta'(s), from the Taylor series of zeta at s."""
    return arb_series([arb(s), 1]).zeta()[1]


def A(s):
    """A(s) := 1/(2 - zeta(s)) - 1 = sum_{m>=2} H_ord(m) m^{-s} for N = the integers (s > rho_0)."""
    return 1 / (2 - zeta(s)) - 1


def line(tag, text, value, ok):
    print("%-3s %s = %s: %s" % (tag, text, value, "True" if ok else "False"))


# ---- Ordered factorisations: the abscissa rho_0 and A_0, A_1 (Section 5.6, "Ordered factorisations") ----
# zeta is decreasing on (1, oo), so zeta(a) > 2 > zeta(b) puts the root rho_0 of zeta = 2 in (a, b).
a, b = arb("1.7286"), arb("1.7287")
line("k1", "rho_0 (root of zeta(s) = 2): zeta(1.7286) - 2, zeta(1.7287) - 2",
     "%s, %s" % ((zeta(a) - 2).str(5), (zeta(b) - 2).str(5)), zeta(a) > 2 and zeta(b) < 2)
s = 2 - arb("0.03")
A0 = A(s)
A1 = -dzeta(s) / (2 - zeta(s)) ** 2          # sum H_ord(m) m^{-s} log m = -(d/ds) 1/(2 - zeta(s))
line("k2", "A_0(0.03) = A(1.97) (paper: 2.0673, used <= 2.07 and, in Cor. kr-weights, <= 2.06734)", A0.str(8),
     A0 <= arb("2.06734"))
line("k3", "A_1(0.03) = -zeta'(1.97)/(2-zeta(1.97))^2 (paper: 9.409, used <= 9.42 and, in Cor. kr-weights, <= 9.409)",
     A1.str(8), A1 <= arb("9.409"))
z18 = zeta(arb("1.8"))                       # X_0^{-0.7} <= e^{-7*10^7} < 10^{-30}
line("k4", "zeta(1.8) (paper: zeta(1.8) + X_0^-0.7 <= 1.883)", z18.str(8), z18 + arb("1e-30") <= arb("1.883"))
line("k5", "1/(2 - 1.883) (paper: sum H_ord(m) m^-1.8 <= 8.6)", (1 / (2 - arb("1.883"))).str(8),
     1 / (2 - arb("1.883")) <= arb("8.6"))

# ---- The X_0 band, Proposition xb-ranges (Section 5.5) ----
As = A(arb("1.8") - arb("3e-6"))
line("x1", "A(1.8 - 3e-6) (paper: <= 7.4915)", As.str(9), As <= arb("7.4915"))
c = arb("7.4915") * arb(2) ** arb("0.2") / 4
line("x2", "(1/4) 7.4915 2^0.2 (paper: <= 2.152)", c.str(8), c <= arb("2.152"))
w6 = 4 / arb(6).sqrt()                       # max over n of prod_{p | n} 2 p^{-1/2}, attained at n = 6
line("x3", "2^omega(n)/sqrt(n) <= prod_{p|n} 2p^-1/2 <= 4/sqrt(6) (paper: 1.64)", w6.str(8), w6 <= arb("1.64"))
n = arb(10) ** 6                             # both terms decrease in n, so n = 10^6 is the worst case
tb = (arb("0.5") + arb("1.64") * n.sqrt()) / n + arb("2.152") * n ** arb("-0.2")
line("x4", "(1/2 + 1.64 sqrt n)/n + 2.152 n^-0.2 at n = 1e6 (paper: <= 0.14 for n > 1e6)", tb.str(8), tb <= arb("0.14"))
A177 = A(arb("1.77"))
line("x5", "A(1.77) (paper: 13.08, used <= 13.1; abscissa 1.7286 < 1.77)", A177.str(8), A177 <= arb("13.1"))
z197 = zeta(arb("1.97")) - 1
line("x6", "sum_{w>=2} w^-1.97 = zeta(1.97) - 1 (paper: 0.674)", z197.str(8), z197 <= arb("0.674"))
dz = -dzeta(arb("1.97"))
line("x7", "sum_{w>=2} w^-1.97 log w = -zeta'(1.97) (paper: <= 1.0001)", dz.str(8), dz <= arb("1.0001"))

# ---- Lemma margin (c), the constant of eq:mu1sum (Section 7) ----
# Ein(2) := int_0^2 (e^w - 1)/w dw = sum_k 2^k/(k k!) = Ei(2) - gamma - log 2.
gamma = arb.const_euler()
Ein2 = arb(2).ei() - gamma - arb(2).log()
line("m1", "Ein(2) = int_0^2 (e^w-1)/w dw = Ei(2) - gamma - log 2 (paper: < 3.69)", Ein2.str(9), Ein2 < arb("3.69"))
# I_1 = int_1^4 v(log v + 1.01) dv, from the antiderivative v^2 log v/2 - v^2/4 + 1.01 v^2/2.
F = lambda v: v * v * v.log() / 2 - v * v / 4 + arb("1.01") * v * v / 2
I1 = F(arb(4)) - F(arb(1))
line("m2", "I_1 = int_1^4 v(log v + 1.01) dv (paper: 14.92)", I1.str(8), I1 <= arb("14.92"))
# I_2 = int_4^oo U^3 (log U + 1.01) v^-2 dv, U = 1 + 2 log v. With v = e^t:
#   I_2 = int_{log 4}^oo h(t) dt,  h(t) = (1+2t)^3 (log(1+2t) + 1.01) e^{-t}.
# On [log 4, T] Arb's acb.integral gives a certified enclosure (log(1+2t) is analytic near the path; the flag is
# forwarded). For t >= T >= 1, (log y + 1.01)/y is decreasing in y = 1+2t >= 1, so h(t) <= c_T (1+2t)^4 e^{-t} with
# c_T = (log(1+2T) + 1.01)/(1+2T), and int_T^oo p(t) e^{-t} dt = e^{-T} (p + p' + p'' + p''' + p'''')(T) for p = (1+2t)^4.
T = 60


def h(t, analytic):
    y = 1 + 2 * t
    return y ** 3 * (y.log(analytic=analytic) + acb("1.01")) * (-t).exp()


main = acb.integral(h, arb(4).log(), T).real
yT = arb(1 + 2 * T)
tail2 = (-arb(T)).exp() * (yT ** 4 + 8 * yT ** 3 + 48 * yT ** 2 + 192 * yT + 384) * (yT.log() + arb("1.01")) / yT
I2 = main + arb(0).union(tail2)
line("m3", "I_2 = int_4^oo U^3 (log U + 1.01) v^-2 dv, U = 1 + 2 log v (paper: 214.8)", I2.str(9), I2 <= arb("214.8"))
# I_3 = c_3 int_4^oo dv/(U v^2), c_3 = 2 e^gamma e^{Ein(2)}. With v = e^t and w = t + 1/2:
#   int_{log 4}^oo e^{-t}/(1+2t) dt = (e^{1/2}/2) E_1(log 4 + 1/2),  E_1(x) = -Ei(-x).
c3 = 2 * gamma.exp() * Ein2.exp()
J3 = arb("0.5").exp() / 2 * (-(-(arb(4).log() + arb("0.5"))).ei())
I3 = c3 * J3
line("m4", "I_3 = 2 e^gamma e^Ein(2) int_4^oo dv/(U v^2) (paper: 6.7)", I3.str(8), I3 <= arb("6.7"))
tot = arb("2.02") / arb(2).log() * (I1 + I2 + I3)
line("m5", "(2.02/log 2)(I_1 + I_2 + I_3) (paper: <= 690)", tot.str(8), tot <= 690)
line("m6", "690/Lambda at Lambda = 1e8 (paper eq:mu1sum: <= 7e-6)", (arb(690) / arb(10) ** 8).str(4),
     arb(690) / arb(10) ** 8 <= arb("7e-6"))
