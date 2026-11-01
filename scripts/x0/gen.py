import math, sys
from fractions import Fraction as F
P=[2,3,5,7,11,13,17]
def subs(v):
    if not v: return [[]]
    return [[j]+w for j in range(v[0]+1) for w in subs(v[1:])]
def nOf(w): return math.prod(p**a for p,a in zip(P,w))
reps=[]
def go(i,m,v):
    if i>0: reps.append(v+[0]*(7-len(v)))
    if i==7: return
    a=1
    while m*P[i]**a<=10**6:
        go(i+1,m*P[i]**a,v+[a]); a+=1
go(0,1,[])
H={}
def hord(n):
    if n<=1: return n
    if n in H: return H[n]
    r=sum(hord(d) for d in range(1,n) if n%d==0) if n<5000 else None
    H[n]=r; return r
def hordv(v):
    # from divisor lattice
    L=[nOf(w) for w in subs(v)]
    L.sort(); h={}
    for d in L:
        h[d]= d if d<=1 else sum(h[e] for e in L if e<d and d%e==0)
    return h
def sqV(w): return 1 if all(a<=1 for a in w) else 0
if __name__=='__main__':
    worst=F(0); cnt=0
    for v in reps:
        m=nOf(v); S=subs(v); h=hordv(v)
        T=[(nOf(w),sqV(w),h[nOf(w)]) for w in S]
        A=sum(s for d,s,_ in T if 1<d<m)
        Q=sum(se*hf*(m//f) for e,se,_ in T if e>1 for f,_,hf in T if f>1 and m%(e*f)==0 and e*f<m)
        lhs=3*(20000*m*sqV(v)+40000*m*A+10001*Q); rhs=50000*m*m
        B=F(2*m*sqV(v)*10000+4*m*A*10000+10001*Q,40000*m*m)
        assert (lhs<rhs) or m==6, (m,B)
        if m!=6: worst=max(worst,B)
        if m==6: assert lhs==rhs
    print(len(reps), float(worst))
