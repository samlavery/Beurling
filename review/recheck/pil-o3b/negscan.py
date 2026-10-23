# Scan: for random pivot patterns E_P (k x k, nonneg integer, invertible), singleton runs, lex-first stage bases,
# count boundaries t whose prefix-inverse row p_t has a negative entry (m-_t>0), total m-, vs total excess M.
import random, sys
from fractions import Fraction as Fr
def inv(A):
    n=len(A); M=[[Fr(x) for x in r]+[Fr(int(i==j)) for j in range(n)] for i,r in enumerate(A)]
    for c in range(n):
        p=next((r for r in range(c,n) if M[r][c]!=0),None)
        if p is None: return None
        M[c],M[p]=M[p],M[c]; pv=M[c][c]; M[c]=[x/pv for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[a-f*b for a,b in zip(M[r],M[c])]
    return [r[n:] for r in M]
def rank(rows):
    M=[[Fr(x) for x in r] for r in rows]; rk=0; n=len(M[0]) if M else 0
    for c in range(n):
        p=next((r for r in range(rk,len(M)) if M[r][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for r in range(len(M)):
            if r!=rk and M[r][c]!=0:
                f=M[r][c]/M[rk][c]; M[r]=[a-f*b for a,b in zip(M[r],M[rk])]
        rk+=1
    return rk
def scan(seed,k,dens):
    rnd=random.Random(seed)
    while True:
        E=[[ (rnd.choice([1,1,2]) if rnd.random()<dens else 0) for _ in range(k)] for _ in range(k)]
        for i in range(k):
            if rnd.random()<0.7: E[i][i]=max(E[i][i],1)
        if inv(E) is not None: break
    M=sum(sum(E[i][j] for i in range(k))-1 for j in range(k))
    nb=0; mtot=0
    for t in range(1,k+1):
        R=[]
        for y in range(k):
            if rank([E[r][:t] for r in R+[y]])==len(R)+1: R.append(y)
            if len(R)==t: break
        A=[[E[y][j] for j in range(t)] for y in R]; Ai=inv(A)
        row=Ai[t-1]                       # pivot p_t = column t-1 (latest first = column 0)
        m=sum(1 for v in row if v<0); mtot+=m; nb+= (m>0)
    return M,nb,mtot
worst=0
for k in (3,5,8):
  for dens in (0.15,0.3,0.5):
    rs=[scan(s*31+k,k,dens) for s in range(300)]
    ratio=max(nb/max(M,1) for M,nb,mt in rs); ratio2=max(mt/max(M,1) for M,nb,mt in rs)
    zeroM_neg=sum(1 for M,nb,mt in rs if M==0 and nb>0)
    print(f"k={k} dens={dens}: max #negbdry/M={ratio:.2f}  max m-tot/M={ratio2:.2f}  M=0 with neg: {zeroM_neg}")
