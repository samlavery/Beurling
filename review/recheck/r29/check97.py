from flint import arb, ctx
ctx.prec = 120
ln = lambda z: arb(z).log()
print('4*1.33+6.0001+2.0001 =', 4*arb('1.33')+arb('6.0001')+arb('2.0001'))
print('2.0001+11.4 =', arb('2.0001')+arb('11.4'), '<=13.41')
print('2.0001+1.01 =', arb('2.0001')+arb('1.01'))
print('H(4P)/H(P) <= 4^{4e-6} =', arb(4)**arb('4e-6'))
# eps in T'_cont: kappa_+/log u + 1/(kappa u) <= 0.81/log u <= 0.81e-8
print("T'_cont excess <= ", arb('0.81')/arb('1e8'))
# threshold where (2+eps)|J|+1 exceeds 2|J|+2
print('crude bound gives 2|J|+2 only for |J| <=', 1/(arb('0.81')/arb('1e8')))
# v3 absorption: (h-1)(Kloc(P)+Kloc(2P)+2) <= (|I|/6H)(H/100*(1+4^{4e-6}... ) + 2)
print('v3 extra copies per |I| <=', (arb(1)/6)*(arb('0.01')*(1+arb(2)**arb('4e-6'))) + arb(2)/(6*arb(10)**1000))
# Remark longwindows deleted sentence: (|J|/H)(H/100+2)
print('deleted-sentence extra per |J| <=', arb('0.01') + 2/arb(10)**1000)
# case 2 tail: M^{1/8}+(2M)^{1/4} <= 2 M^{1/4}, log M >= 1e8
lM = arb('1e8')
print('M^{-1/8}+2^{1/4} =', (-lM/8).exp()+arb(2)**arb('0.25'), '<= 2')
# K_loc sum: log(4(4M)^{0.01}+19 log M+47) vs log M / 8
lhs = (4*((ln(4)+lM)*arb('0.01')).exp() + 19*lM + 47).log()
print('log(4H(4M)+19logM+47) <=', lhs, ' vs (logM)/8 =', lM/8)
# case 3: K*/M <= 4*4^{1/4} M^{-3/4}
print('4*4^{1/4} =', 4*arb(4)**arb('0.25'), '<= 6')
print('04k: 2.0001*2.1 =', arb('2.0001')*arb('2.1'))
print('04f: 2.0001*2 + 2.01*1e-32 =', arb('2.0001')*2 + arb('2.01')*arb('1e-32'), '<= 4.01')
