from flint import arb, arb_series, ctx
ctx.prec = 80
x = arb_series([arb("0.3"), 1], prec=3)
print(type(x), x.prec if hasattr(x,'prec') else None, len(x.coeffs()))
y = (1 + (x.inv() - (1-x).inv()).exp()).inv()
print(len(y.coeffs()), y.coeffs())
d = arb("0.5") + arb(0, "1e-3")
u = abs(d).upper()
print(type(u), u, arb(u) <= arb(1))
# check that a series at a wide ball encloses pointwise derivatives
import random
t = arb("0.25") + arb(0, "0.01")
xs = arb_series([t, 1], prec=3)
ys = (1 + (xs.inv() - (1-xs).inv()).exp()).inv()
c = ys.coeffs()
print("ball enclosure:", c[1], 2*c[2])
for tt in ["0.24", "0.245", "0.25", "0.255", "0.26"]:
    xp = arb_series([arb(tt), 1], prec=3)
    yp = (1 + (xp.inv() - (1-xp).inv()).exp()).inv()
    cp = yp.coeffs()
    print(tt, cp[1].str(8), (2*cp[2]).str(8), c[1].contains(cp[1]), (2*c[2]).contains(2*cp[2]))
# max semantics
print(max(arb(0), arb(3)), max(arb(3), arb(2)))
