# Small-N X0-band jump term: B(n0) = (1/n0)[1/2|c_n0| + sum_{d|n0,1<d<n0} 1/2 TV(D_d)],
# TV(D_d) <= |c_d| + TVnom(C_d), TVnom(C_d) <= |c_d| + 1/2 sum_{e|d,1<e<d}|c_e| Hord(d/e)(e/d)^{0.97}; |c_e| <= mu^2(e)
import math
NMAX=20000
sqf=[1]*(NMAX+1)
for p in range(2,int(NMAX**0.5)+1):
    for k in range(p*p,NMAX+1,p*p): sqf[k]=0
divs=[[] for _ in range(NMAX+1)]
for d in range(1,NMAX+1):
    for k in range(d,NMAX+1,d): divs[k].append(d)
H=[0]*(NMAX+1); H[1]=1
for m in range(2,NMAX+1): H[m]=sum(H[d] for d in divs[m] if d<m)
tv=[0.0]*(NMAX+1); tv[1]=1.0
for d in range(2,NMAX+1):
    tv[d]=sqf[d]+0.5*sum(sqf[e]*H[d//e]*(e/d)**0.97 for e in divs[d] if 1<e<d)
best=[]
for n0 in range(2,NMAX+1):
    s=0.5*sqf[n0]+sum(0.5*(sqf[d]+tv[d]) for d in divs[n0] if 1<d<n0)
    best.append((s/n0,n0))
best.sort(reverse=True)
print("top B(n0):",[(round(b,4),n) for b,n in best[:8]])
print("max over n0>=100:",max(b for b,n in best if n>=100),"n0>=1000:",max(b for b,n in best if n>=1000))
