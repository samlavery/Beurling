# Exact small-N X0-band bound [P-CA]. For n <= N:
#   B(n) = (1/n)[ 1/2 mu^2(n) + 1/2 sum_{d|n,1<d<n} TVD(d) ],
#   TVD(d) = 2 mu^2(d) + 1/2*lam*X(d)/d,   X(d) = sum_{e|d,1<e<d} mu^2(e) * e * H(d/e),
#   H = ordered factorisations, lam = 1.0001 (covers H_e/H_d <= (d/e)^{3e-6}).
# H, X exact Python ints (stored in int64 arrays; overflow asserted). TVD, S, B: floats, sums of <= tau(n)
# nonnegative terms; relative rounding error < 1e-12, covered by the final factor (1+1e-9).
import sys
from array import array
N=int(sys.argv[1]) if len(sys.argv)>1 else 10**6
lam=1.0001
sqf=bytearray([1])*(N+1); sqf[0]=0
p=2
while p*p<=N:
    for m in range(p*p,N+1,p*p): sqf[m]=0
    p+=1
H=array('q',[0])*(N+1); H[1]=1
for d in range(1,N//2+1):
    hd=H[d]
    for m in range(2*d,N+1,d): H[m]+=hd
X=array('q',[0])*(N+1)
for e in range(2,N//2+1):
    if sqf[e]:
        k=2
        for m in range(2*e,N+1,e):
            X[m]+=e*H[k]; k+=1
S=array('d',[0.0])*(N+1)
for k in range(2,N//2+1):
    t=2.0*sqf[k]+0.5*lam*X[k]/k
    for m in range(2*k,N+1,k): S[m]+=t
best=[];sup={10:0,100:0,1000:0,10**4:0,10**5:0}
for n in range(2,N+1):
    b=(0.5*sqf[n]+0.5*S[n])/n*(1+1e-9)
    best.append((b,n)) if b>0.05 else None
    for lo in sup:
        if n>=lo and b>sup[lo]: sup[lo]=b
best.sort(reverse=True)
print("N=",N," Hmax=",max(H)," Xmax=",max(X)," (int64 ok:",max(X)<2**62,")")
print("top:",[(n,round(b,5)) for b,n in best[:10]])
for lo in sorted(sup): print("sup B(n), %d<=n<=N: %.6f"%(lo,sup[lo]))
tail=lambda n: (0.5+1.64*n**0.5)/n+0.25*lam*7.49109924*2**0.2*n**-0.2
print("analytic tail bound for n>=N:",tail(N))
