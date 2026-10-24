from flint import arb, ctx
ctx.prec = 120
# 1-sqrt(1-e) <= e/2+e^2/2 on [0,1/2]  <=>  (1+e)(1+sqrt(1-e)) >= 2; check on a fine grid of intervals (monotone f)
ok = True
N = 20000
for i in range(N):
    lo = arb(i)/(2*N); hi = arb(i+1)/(2*N)
    # f increasing? lower bound of f on [lo,hi] by (1+lo)(1+sqrt(1-hi))
    if not ((1+lo)*(1+(1-hi).sqrt()) >= 2 - arb('1e-30')*0 or i == 0):
        ok = False; print('fail at', i); break
print('ineq on (0,1/2] grid:', ok)
e = arb('0.5'); print('max ratio (1-sqrt(1-e)-e/2)/e^2 at 1/2:', (1-(1-e).sqrt()-e/2)/e**2)
# exact worst case of |P - sqrt(Pq)| for P-q = H/2: (H/2)/(1+sqrt(1-H/(2P))) vs H/4 + H^2/(32P)
print('1.0001*1.5003 =', arb('1.0001')*arb('1.5003'))
print('0.5002 + 1 + 1e-6 =', arb('0.5002')+1+arb('1e-6'))
# v3: length H/2 interval -> slot window 1.5H(1+1e-8)+... ; 1.5H+2 fails once 1.5H*0.81e-8 > 1
print('v3 1.5H+2 fails (true T_cont excess) once H >', 1/(arb('1.5')*arb('0.81e-8')))
