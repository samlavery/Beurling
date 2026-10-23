# Toy check of the sharp-reference formula rho_sh(y) = sum_n mu(n) 1[y/n >= X0] T'(y/n)/n,
# T'(v) = 1 - rho_det(v), rho_det(v) = #(X0-smooth in [v,(1+k)v])/(k v), versus F(y) = #(primes >= X0 in [y,(1+k)y])/(k y).
import math
X0=2000; k=0.05; N=40000
spf=list(range(N+1))
for i in range(2,int(N**.5)+1):
    if spf[i]==i:
        for j in range(i*i,N+1,i):
            if spf[j]==j: spf[j]=i
def P(n):
    m=1
    while n>1:
        p=spf[n]; m=max(m,p)
        while n%p==0: n//=p
    return m
smooth=[0]*(N+1); prime_ge=[0]*(N+1)
for n in range(1,N+1):
    smooth[n]=1 if P(n)<X0 else 0
    prime_ge[n]=1 if (n>=X0 and spf[n]==n) else 0
import itertools
cs=list(itertools.accumulate(smooth)); cp=list(itertools.accumulate(prime_ge))
def cnt(c,a,b):  # integers in [a,b]
    a=math.ceil(a); b=math.floor(b)
    if b<a: return 0
    return c[b]-(c[a-1] if a>=1 else 0)
def Tp(v): return 0.0 if v<X0 else 1-cnt(cs,v,(1+k)*v)/(k*v)
def F(q): return cnt(cp,q,(1+k)*q)/(k*q)
def mu(n):
    r=1
    while n>1:
        p=spf[n]; n//=p
        if n%p==0: return 0
        r=-r
    return r
def rsh(y): return sum(mu(n)*Tp(y/n)/n for n in range(1,int(y/X0)+1))
for y in (5000.0, 5600.0, 6*0.99*X0, 6*0.999*X0, 6*X0*1.001, 4*0.999*X0, 2*0.999*X0, 10*0.999*X0):
    print(f"y={y:9.1f}  rho_sh*log y={rsh(y)*math.log(y):.4f}  F*log y={F(y)*math.log(y):.4f}  pred dip -mu(N)F(y/N)/N terms: ",
          [ (Nn, round(-mu(Nn)*F(y/Nn)/Nn*math.log(y),4)) for Nn in range(2,13) if X0/(1+k)<y/Nn<X0 ])
