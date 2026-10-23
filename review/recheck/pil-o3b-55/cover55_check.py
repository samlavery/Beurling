# Check of the Cover-Bound pull-out (#55): for compositions with zero parts (j_t=0 stages, K_t>=1),
# Fin = g_T(rho)+rho^{j_T} g_{T-1}(rho) (A=1) vs (1+kappa*lam)^{s_R} * F_kappa(rho), lam=log(1/rho),
# where F_kappa is the exact Thm R run-structure sum. g computed by quadrature on a fine log grid (upper Riemann sums
# not needed: we report the ratio; grid refinement shows stability).
import math, random, sys
from fractions import Fraction as Fr
exec(open('genfun55.py').read().split('ok=True')[0])   # H polynomials, ev
def Fk(k,r): return float(ev(H[k],Fr(r))+sum(Fr(r)**j*ev(H[k-j],Fr(r)) for j in range(1,k+1))) if isinstance(r,Fr) else None
def run(seed,M=4000):
    rnd=random.Random(seed)
    kappa=rnd.randint(1,5)
    parts=[]; r=kappa
    first=rnd.randint(1,r); parts.append(first); r-=first   # K_1>=1
    while r>0 or (rnd.random()<0.3 and len(parts)<8):
        if r>0 and rnd.random()<0.6: c=rnd.randint(1,r); parts.append(c); r-=c
        else: parts.append(0)
    rho=Fr(rnd.randint(1,99),100); lam=math.log(1/float(rho))
    # grid on [rho,1] in log scale
    xs=[float(rho)*(1/float(rho))**(i/M) for i in range(M+1)]
    g=[1.0]*(M+1); K=0; gs=[g]
    for j in parts:
        K+=j; new=[0.0]*(M+1); acc=0.0
        for i in range(M-1,-1,-1):
            a,b=xs[i],xs[i+1]
            # int_a^b K x^{j-1} g(x) dx, trapezoid
            fa=K*a**(j-1)*g[i]; fb=K*b**(j-1)*g[i+1]
            acc+=0.5*(fa+fb)*(b-a); new[i]=acc
        g=new; gs.append(g)
    jT=parts[-1]
    fin=gs[-1][0]+float(rho)**jT*gs[-2][0]
    sR=sum(1 for j in parts if j==0)
    bound=(1+kappa*lam)**sR*Fk(kappa,rho)
    return fin/bound, parts, float(rho)
worst=0
for s in range(int(sys.argv[1]) if len(sys.argv)>1 else 300):
    r,p,rho=run(s); 
    if r>worst: worst=r; wp=(p,rho)
print(f"max Fin/[(1+kappa lam)^sR F_kappa(rho)] = {worst:.6f} at parts={wp[0]} rho={wp[1]}")
