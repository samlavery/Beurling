from flint import arb, ctx
ctx.prec = 200
ln = lambda z: arb(z).log()
# (1) endpoint value of g(ell)=11(1+U)^3 log(2+U)/ell, U = ell^{1/4}(1+sqrt(2 log ell+4)), ell=1e34
ell = arb(10)**34
x = ln(ell)
s = (2*x+4).sqrt()
U = ell**(arb(1)/4)*(1+s)
g = 11*(1+U)**3*ln(2+U)/ell
print('g(1e34) =', g, ' <=1.98e-3:', g < arb('1.98e-3'))
# (2) derivative bound d log g / d log ell <= 3(1/4+1/(s(1+s))) + (1/4+1/(s(1+s)))*4/x - 1 at x0 (terms decrease in x)
d = 3*(arb(1)/4+1/(s*(1+s))) + (arb(1)/4+1/(s*(1+s)))*4/x - 1
print('dlog g/dlog ell bound at 1e34:', d, ' <= -0.21:', d < arb('-0.21'))
# sanity: actual g at a grid of larger ell, decreasing
prev = g
ok = True
for e in range(35, 400):
    el = arb(10)**e; xx = ln(el); ss=(2*xx+4).sqrt(); UU = el**(arb(1)/4)*(1+ss)
    gg = 11*(1+UU)**3*ln(2+UU)/el
    ok = ok and (gg < prev); prev = gg
print('grid decreasing 1e34..1e399:', ok)
# (3) e^{A} e^{a} : A<=2e-3, so e^{Q} <= e^{2.002} ell/tau
print('2+2e-3 = 2.002 exact')
# (4) tail: (J/log2+1)*38.3*e^{2.002}/Gamma((0.449J)^{1/4}) < 1e-6 tau / J, tau>=1e8, J>=3e34
def tail_ok(J):
    J = arb(J)
    lhs = ln(J/ln(2)+1) + ln(arb('38.3')) + arb('2.002') - ((arb('0.449')*J)**(arb(1)/4)).lgamma()
    rhs = ln(arb('1e-6')*arb('1e8')/J)
    return lhs, rhs, lhs < rhs
for J in ['3e34','1e35','1e40','1e100']:
    print('J=',J, tail_ok(J))
# monotonicity of LHS*J/RHS-ratio: log(J/log2+1)+log J - lgamma((0.449J)^{1/4}) decreasing for J>=3e34 (lgamma grows like J^{1/4} log J)
# (5) Region 1 coefficient
c = arb('1.1001')*arb('38.3')/ln(2)
print('1.1001*38.3/log2 =', c)
print('  *(1+3e-6) =', c*(1+arb('3e-6')), ' <= 60.81:', c*(1+arb('3e-6')) < arb('60.81'))
# aggregate factor: (e^{6.88e-7})(1+1e-6)(1+1e-6 log2 + sigma-shift) + tail relative
A1 = 11*arb('1.01')*ell**(arb(-1)/4)*(x/4+arb('0.01'))
print('u<=ell^1/4 A bound at 1e34:', A1, ' <=7e-7:', A1 < arb('7e-7'))
p = A1.exp()*(1+arb('1e-6'))*(1+arb('1e-6')*ln(2)+arb('1e-8'))
tailrel = arb('1e-6')/(arb('38.3')/ln(2))
print('aggregate factor incl. tail relative:', p+tailrel, ' <= 1+3e-6:', p+tailrel < 1+arb('3e-6'))
print('60.81+2e-6<=61.1:', arb('60.81')+arb('2e-6') < arb('61.1'))
# with e^A dropped vs kept in tail: sanity e^{2.002}/e^2
print('e^0.002 =', arb('0.002').exp())
# (6) e^A at the reader's point
for l in ['4.49e36','1e37']:
    el = arb(l); UU = el**(arb(1)/4)*(1+(2*ln(el/arb('1e8'))+4).sqrt())
    AA = 11*(1+UU)**3*ln(2+UU)/el
    print('ell=',l,'A(U)=',AA,'e^A=',AA.exp())
