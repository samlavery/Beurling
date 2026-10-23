# Exact check of eq:A-HK and the run-structure sum in Thm R (#55).
# g-recursion with A=1: g_0=1, g_t(E)=int_E^1 K_t x^{j_t-1} g_{t-1}(x) dx (all j_t>=1). Polynomials over Q.
# Checks: (1) sum over compositions of K of g_T == H_K (eq:A-HK);  (2) H_k(0) == k^k/k!;
# (3) F_k(rho)=H_k(rho)+sum_j rho^j H_{k-j}(rho) is <= H_k(0) and non-increasing on a grid; F_k(1)=1;
# (4) Fin per composition = g_T(rho)+rho^{j_T} g_{T-1}(rho) summed over compositions == F_k(rho).
from fractions import Fraction as Fr
from math import factorial
from itertools import product
def integ_from(P, j, K):   # E -> int_E^1 K x^{j-1} P(x) dx ; P dict deg->coef
    out={}
    for d,c in P.items():
        e=j+d  # antiderivative degree
        out[0]=out.get(0,Fr(0))+K*c/e
        out[e]=out.get(e,Fr(0))-K*c/e
    return out
def ev(P,x): return sum(c*x**d for d,c in P.items())
def add(P,Q,s=1):
    R=dict(P)
    for d,c in Q.items(): R[d]=R.get(d,Fr(0))+s*c
    return R
def mulx(P,j): return {d+j:c for d,c in P.items()}
def compositions(n):
    if n==0: yield (); return
    for first in range(1,n+1):
        for rest in compositions(n-first): yield (first,)+rest
H={0:{0:Fr(1)}}
for K in range(1,11):
    acc={}
    for j in range(1,K+1): acc=add(acc,integ_from(H[K-j],j,K))
    H[K]=acc
ok=True
for k in range(1,11):
    # (1)
    tot={}; fin_tot_at={}
    rhos=[Fr(i,10) for i in range(11)]
    fin_sum={r:Fr(0) for r in rhos}
    for comp in compositions(k):
        g={0:Fr(1)}; K=0; gs=[g]
        for j in comp:
            K+=j; g=integ_from(g,j,K); gs.append(g)
        tot=add(tot,g)
        for r in rhos: fin_sum[r]+=ev(gs[-1],r)+r**comp[-1]*ev(gs[-2],r)
    c1=all(v==0 for v in add(tot,H[k],-1).values())
    c2=(ev(H[k],0)==Fr(k**k,factorial(k)))
    F=lambda r: ev(H[k],r)+sum(r**j*ev(H[k-j],r) for j in range(1,k+1))
    vals=[F(r) for r in rhos]
    c3=all(v<=vals[0] for v in vals) and all(vals[i+1]<=vals[i] for i in range(10)) and vals[-1]==1
    c4=all(fin_sum[r]==F(r) for r in rhos)
    ok&=c1 and c2 and c3 and c4
    print(f"k={k}: sum_comp g_T==H_k {c1}; H_k(0)=k^k/k! {c2} ({float(ev(H[k],0)):.4f}); F_k monotone,<=H_k(0),F(1)=1 {c3}; sum Fin==F_k {c4}; #comps={2**(k-1)}")
print("ALL OK" if ok else "FAIL")
# (5) closed forms at rational E: [z^K] (1-Ez)/(1-T(z e^{-Ez})) == H_K(E), and [z^k] 1/(1-T(z e^{-rho z})) == F_k(rho)
N=11
def ser_mul(a,b): return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(N)]
def ser_exp_lin(c):   # e^{c z}
    return [Fr(c)**n/factorial(n) for n in range(N)]
def ser_compose_T(wz):  # T(w(z)) with w(0)=0
    out=[Fr(0)]*N; pw=[Fr(1)]+[Fr(0)]*(N-1)
    for n in range(1,N):
        pw=ser_mul(pw,wz); c=Fr(n**(n-1),factorial(n))
        out=[o+c*x for o,x in zip(out,pw)]
    return out
def ser_inv(a):  # 1/a, a[0]!=0
    b=[Fr(0)]*N; b[0]=1/a[0]
    for n in range(1,N): b[n]=-sum(a[i]*b[n-i] for i in range(1,n+1))/a[0]
    return b
ok5=True
for E in (Fr(0),Fr(1,3),Fr(1,2),Fr(9,10)):
    wz=[Fr(0)]+ser_exp_lin(-E)[:N-1]
    T=ser_compose_T(wz); oneminusT=[1-T[0]]+[-x for x in T[1:]]
    inv=ser_inv(oneminusT)
    P=ser_mul([1,-E]+[Fr(0)]*(N-2),inv)
    for K in range(1,N):
        ok5&=(P[K]==ev(H[K],E))
        F=ev(H[K],E)+sum(E**j*ev(H[K-j],E) for j in range(1,K+1))
        ok5&=(inv[K]==F)
print("closed forms P=(1-Ez)/(1-T(ze^{-Ez})) and F_k=[z^k]1/(1-T(ze^{-rho z})) match for K<=10 at E in {0,1/3,1/2,9/10}:",ok5)
