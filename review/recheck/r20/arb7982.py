from flint import arb, ctx
ctx.prec=200
r = arb(4)**arb("4e-6"); print("4^(4e-6) =", r.str(12), "<=1.000006?", r.upper()<=arb("1.000006"))
print("log4/1e8 =", (arb(4).log()/arb("1e8")).str(6))
f = arb(2)*arb("1.000006")*(1-arb("1.4e-8"))**(-11); print("cofactor factor =", f.str(12), "<=2.00002?", f.upper()<=arb("2.00002"))
# queue: |I|<=H(x), and queue L up to log x + 0.7: extra (1+0.7e-8)^11
g = arb("1.000006")*(1-arb("1.4e-8"))**(-11)*(1+arb("0.7e-8"))**11; print("queue factor =", g.str(12), "<=1.00001?", g.upper()<=arb("1.00001"))
# 12L(L0+1)+2 with L0=48 M1 L^3/c'^2
print("12*48/0.15^2 =", (arb(12)*48/arb("0.15")**2).str(10))
# #82: 2e^15 L^2 (L+1) e^-L at L=100
L=arb(100); v = 2*arb(15).exp()*L**2*(L+1)*(-L).exp(); print("#82 at L=100:", v.str(6))
# Step 6 (04c): (2+s)^2 <= 4 log(l/tau)+16 ; l^{1/2} >= 4 log l + 16 at l=3e9
l=arb("3e9"); print("sqrt(3e9)=", l.sqrt().str(6), " 4log l+16=", (4*l.log()+16).str(6))
# old clause counterexample: tau=1e8, l=1e4*tau
tau=arb("1e8"); l=arb("1e12"); U=l**arb("0.25")*(1+(2*(l/tau).log()+4).sqrt()); us=U+arb("0.5")
print("U=",U.str(8)," 4.3 l^1/4=",(arb("4.3")*l**arb("0.25")).str(8)," u*^2=",(us**2).str(8)," 19 l^1/2=",(19*l.sqrt()).str(8), " l/u*=",(l/us).str(8)," l^3/4/4.4=",(l**arb("0.75")/arb("4.4")).str(8))
print("U<=4.3 l^1/4 iff l/tau <=", ((arb("3.3")**2-4)/2).exp().str(8))
