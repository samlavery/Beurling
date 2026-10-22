#!/usr/bin/env python3
"""Numerical corroboration of some structural facts used in the proof of the Staged Volume Lemma (paper, Appendix A, Theorem thm:svl).
NOT part of any proof. Exact rational arithmetic (fractions.Fraction); no external dependencies.

Usage:  python3 -I svl_stress.py [seed=1] [configs_per_mode=60]
For each random configuration (k = 8..12 rows, exponents 0..D, D in {4,5,6}) it computes the greedy pivots
(latest-first), the maximal pivot runs (stages), and row stages C_t with E_{C<=t,P<=t} invertible, and checks:
  C1  stage rows exist;   C2  every pivot column has mass >= 1 in the rows of its stage prefix;
  C3  every late free column is nonzero on C_<=t (here C = all stage rows, i.e. the case C = B');
  C4/C5  every late free column equals E_{.,P<=t} E_{C<=t,P<=t}^{-1} e_{f,C<=t} on ALL rows
         (so it is determined by its C_<=t entries, and its coefficient in the remaining rows vanishes);
  C6  the cumulative determinant det E_{C<=t,P<=t} is a nonzero integer.
Modes: rand (dense), late (free columns = nonneg sums of later pivots, interleaved), shared (n_i = A f q_i d_i),
nest (nested groups with cycle cores). Expected output: "violations 0" for every mode.
"""
# Columns = primes in decision order (index 0 = latest). Checks per config:
# C1 greedy runs & C_t exist; C2 s_j^{(t_j)}>=1; C3 late f nonzero in C<=t; C4 e_f determined by C<=t entries;
# C5 remaining rows' coeff on f vanish after eliminating P<=t; C6 cumulative det integer, |det|>=1.
import random, sys
from fractions import Fraction as F
def rref_rank(M):
    M=[[F(x) for x in r] for r in M]; rk=0
    if not M or not M[0]: return 0
    for c in range(len(M[0])):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]; M[i]=[a-f*b for a,b in zip(M[i],M[rk])]
        rk+=1
    return rk
def det(M):
    n=len(M); A=[[F(x) for x in r] for r in M]; d=F(1)
    for c in range(n):
        p=next((i for i in range(c,n) if A[i][c]!=0),None)
        if p is None: return F(0)
        if p!=c: A[c],A[p]=A[p],A[c]; d=-d
        d*=A[c][c]
        for i in range(c+1,n):
            f=A[i][c]/A[c][c]; A[i]=[a-f*b for a,b in zip(A[i],A[c])]
    return d
def solve(A,b):  # square
    n=len(A); M=[[F(x) for x in r]+[F(bb)] for r,bb in zip(A,b)]
    for c in range(n):
        p=next(i for i in range(c,n) if M[i][c]!=0); M[c],M[p]=M[p],M[c]
        M[c]=[x/M[c][c] for x in M[c]]
        for i in range(n):
            if i!=c and M[i][c]!=0: f=M[i][c]; M[i]=[a-f*bb for a,bb in zip(M[i],M[c])]
    return [M[i][n] for i in range(n)]
def check(E):
    k=len(E); m=len(E[0]); col=lambda c:[E[i][c] for i in range(k)]
    piv=[]; kind=[]
    for c in range(m):
        if rref_rank([[E[i][q] for q in piv+[c]] for i in range(k)])>len(piv): piv.append(c); kind.append('P')
        else: kind.append('F')
    if len(piv)<k: return None
    stages=[]; cur=[]
    for c in range(m):
        if kind[c]=='P': cur.append(c)
        elif cur: stages.append(cur); cur=[]
    if cur: stages.append(cur)
    C=[]; Cst=[]; Pcum=[]; bad=[]
    for st in stages:
        Pcum=Pcum+st; ch=[]
        for i in range(k):
            if i in C or i in ch: continue
            if rref_rank([[E[r][c] for c in Pcum] for r in C+ch+[i]])==len(C)+len(ch)+1: ch.append(i)
            if len(ch)==len(st): break
        if len(ch)<len(st): return ('C1',)
        C=C+ch; Cst.append(list(C))
    joined={}
    for t,Cl in enumerate(Cst):
        for y in Cl: joined.setdefault(y,t)
        Pl=[c for s in stages[:t+1] for c in s]
        for j in Pl:
            if sum(E[r][j] for r in Cl)<1: bad.append('C2')
        D=det([[E[r][c] for c in Pl] for r in Cl])
        if D==0 or D.denominator!=1: bad.append('C6')
    for c in range(m):
        if kind[c]!='F': continue
        t=max(ti for ti,st in enumerate(stages) if st[0]<c); Cl=Cst[t]; Pl=[q for s in stages[:t+1] for q in s]
        if all(E[r][c]==0 for r in Cl): bad.append('C3')
        v=solve([[E[r][q] for q in Pl] for r in Cl],[E[r][c] for r in Cl])
        rec=[sum(E[i][q]*vv for q,vv in zip(Pl,v)) for i in range(k)]
        if rec!=[F(x) for x in col(c)]: bad.append('C4/C5')   # determined + remaining-row coeffs vanish
    return (len(stages),bad)
def gen(mode,k,D):
    if mode=='rand':
        m=random.randint(k,2*k)
        return [[random.choice([0]*3+list(range(1,D+1))) for _ in range(m)] for _ in range(k)]
    if mode=='late':   # pivots interleaved with free columns = nonneg combos of EARLIER-listed (later-decided) pivots
        cols=[]; pcols=[]
        while len(pcols)<k:
            if pcols and random.random()<0.55:
                S=random.sample(pcols,random.randint(1,min(3,len(pcols))))
                cols.append([min(D,sum(p[i] for p in S)) for i in range(k)])
            else:
                c=[random.choice([0,0,1,1,2][:D+2]) for _ in range(k)]
                if any(c): cols.append(c); pcols.append(c)
        cols+= [[random.choice([0,1]) for _ in range(k)] for _ in range(random.randint(0,3))]
        return [[cols[c][i] for c in range(len(cols))] for i in range(k)]
    if mode=='shared':   # n_i = A f q_i d_i, nested: A f B g q_i for half
        m=2+k; E=[[1,1]+[1 if j==i else 0 for j in range(k)] for i in range(k)]
        return E
    if mode=='nest':   # A f (B g q_i | q_i) nested groups + triangle cores
        cols=[[1]*k,[1]*k]; h=k//2
        cols.append([1 if i<h else 0 for i in range(k)]); cols.append([1 if i<h else 0 for i in range(k)])
        for i in range(k): cols.append([1 if j==i or j==(i+1)%k else 0 for j in range(k)])
        return [[cols[c][i] for c in range(len(cols))] for i in range(k)]
seed=int(sys.argv[1]) if len(sys.argv)>1 else 1
N=int(sys.argv[2]) if len(sys.argv)>2 else 60
random.seed(seed); stats={}; total_bad=0
for mode in ('rand','late','shared','nest'):
    n=0; maxT=0; nb=0
    for t in range(N):
        k=random.randint(8,12); D=random.choice([4,5,6])
        E=gen(mode,k,D)
        if any(all(E[i][c]==0 for i in range(len(E))) for c in range(len(E[0]))):
            E=[[x for c,x in enumerate(r) if any(E[i][c] for i in range(len(E)))] for r in E]
        res=check(E)
        if res is None: continue
        if res[0]=='C1': nb+=1; print('C1 fail',mode); continue
        n+=1; maxT=max(maxT,res[0]); nb+=len(res[1])
        if res[1]: print(mode,'violations',set(res[1]))
    print(mode,'configs',n,'max stages T',maxT,'violations',nb); total_bad+=nb

sys.exit(1 if total_bad else 0)
