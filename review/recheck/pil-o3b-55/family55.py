# Family boundary (pil-o3b family, boundary of p_2): one passing row (q* increasing in its piece) + one joining row,
# union over all contents. Carried factor of the passing row as in v3: A/Eu(s) (top A paid at its join) => G==A.
# Compare the true toy label sum with (i) the v3 per-row target A^2/E0^2 and (ii) the #55 bound Phi_t(a)=2A(A-E0)/E0^2.
import random, itertools, sys
from fractions import Fraction as Fr
def run(seed):
    rnd=random.Random(seed); n=rnd.randint(2,6)
    p=sorted(rnd.sample(range(2,30),n)); w=[Fr(1,x) for x in p]
    sl=[]; s=0
    for _ in range(n): s+=rnd.randint(1,2); sl.append(s)
    E0=Fr(1)
    def Eu(u):
        v=E0
        for i in range(n):
            if sl[i]<u: v/=(1-w[i])
        return v
    gthr=sl[-1]+rnd.randint(1,3); A=Eu(gthr); h=rnd.randint(0,2); Q=rnd.randint(-2,sl[-1]+2)
    dP=[rnd.randint(1,5) for _ in range(n)]; dJ=[-rnd.randint(0,3) for _ in range(n)]
    sup=[(0,),(1,),(0,1)]
    lhs=Fr(0)
    for r in range(1,n+1):
        for S in itertools.combinations(range(n),r):
            top=max(S)
            for sp in itertools.product(sup,repeat=r):
                wt=Fr(1); q=Q
                for g,sg in zip(S,sp):
                    wt*=(w[g]/(1-w[g]))**len(sg)
                    q+=(dP[g] if 0 in sg else 0)+(dJ[g] if 1 in sg else 0)
                for s_ in range(sl[top]+1,gthr+1):
                    if abs(q-s_)<=h: lhs+=wt*Fr(1,2*h+1)*A/Eu(s_)
    v3=A*A/E0**2; new=2*A*(A-E0)/E0**2
    return float(lhs/v3), float(lhs/new)
mv3=0; mnew=0
for s in range(int(sys.argv[1]) if len(sys.argv)>1 else 400):
    a,b=run(s); mv3=max(mv3,a); mnew=max(mnew,b)
print(f"max true/v3-target = {mv3:.4f}   max true/#55-bound = {mnew:.4f}")
