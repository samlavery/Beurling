# Independent check of Lemma SC (lead-notes L1). Exact rational rank.
import random, itertools
from fractions import Fraction

def rank(rows):
    M=[[Fraction(x) for x in r] for r in rows]
    if not M: return 0
    rk=0; ncol=len(M[0])
    for c in range(ncol):
        piv=None
        for i in range(rk,len(M)):
            if M[i][c]!=0: piv=i;break
        if piv is None: continue
        M[rk],M[piv]=M[piv],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]
                M[i]=[a-f*b for a,b in zip(M[i],M[rk])]
        rk+=1
    return rk

def lexfirst(order, E, cols):
    B=[]
    for y in order:
        if rank([[E[w][c] for c in cols] for w in B+[y]])==len(B)+1: B.append(y)
    return set(B)

def trial(rng, r, m, dens, maxe):
    E=[[ (rng.randint(1,maxe) if rng.random()<dens else 0) for _ in range(m)] for _ in range(r)]
    if any(all(E[y][j]==0 for y in range(r)) for j in range(m)): return None
    if rank(E)<r: return None
    # greedy latest-first pivots (column 0 = latest)
    piv=[]; 
    for j in range(m):
        if rank([[E[y][c] for y in range(r)] for c in piv+[j]])==len(piv)+1: piv.append(j)
    if len(piv)!=r: return None
    # runs and free blocks
    stage_of={}; t=0; prev_piv=False; blocks=[]
    for j in range(m):
        isp = j in piv
        if isp and not prev_piv: t+=1
        stage_of[j]=t; prev_piv=isp
    T=t
    if T<2: return None
    Pt=lambda s:[j for j in piv if stage_of[j]<=s]
    Ft=lambda s:[j for j in range(m) if j not in piv and stage_of[j]==s]
    # all covers that are minimal
    covers=[]
    for k in range(1,r+1):
        for C in itertools.combinations(range(r),k):
            if all(any(E[y][j] for y in C) for j in range(m)):
                if not any(set(c)<=set(C) for c in covers): covers.append(C)
    res={'ok':0,'fail':0,'advfail':0,'nest':0}
    for C in covers:
        C=set(C); R=[y for y in range(r) if y not in C]
        for orderC,key in ((sorted(C)+R,'ok'),(R+sorted(C),'adv')):
            prevB=set(); good=True
            for s in range(1,T+1):
                cols=Pt(s)
                B=lexfirst(orderC,E,cols)
                assert len(B)==len(cols)
                if not prevB<=B: res['nest']+=1
                prevB=B
                need=cols+Ft(s)
                if not all(any(E[y][j] for y in B&C) for j in need): good=False
            if key=='ok': res['ok' if good else 'fail']+=1
            elif not good: res['advfail']+=1
    return res

rng=random.Random(20261021)
tot={'ok':0,'fail':0,'advfail':0,'nest':0}; n=0
for it in range(6000):
    r=rng.randint(3,7); m=r+rng.randint(1,5)
    out=trial(rng,r,m,rng.choice([0.25,0.35,0.5]),rng.choice([1,2,3]))
    if out is None: continue
    n+=1
    for k in tot: tot[k]+=out[k]
print("configs",n,tot)
