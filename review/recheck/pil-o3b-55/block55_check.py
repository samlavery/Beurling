# Independent check of #55 (S3)(a) with EXPLICIT content enumeration and adversarial pinned values.
# Slots: integer positions; primes at increasing slots sl_0<...<sl_{n-1} (gaps allowed), weight w_i=1/p_i.
# Eu(s) = E0 * prod_{sl_i < s} (1-w_i)^{-1}.  a = first slot (Eu(a)=E0).  K = m passing + j joining chain rows.
# Content: nonempty set S of primes, each with a nonempty support sigma_g in {0..K-1} (rows containing it);
#   exact exponent sum for support sigma: (w/(1-w))^{|sigma|}.
# chi(u) = 1(u <= gthr) (nested good events and s_max).  A_top := Eu(gthr) (smallest admissible top).
# Carried Phi_{t-1}(u) = G(Eu(u))/Eu(u)^m with G nonneg non-increasing, G=0 above A_top.
#   G = output of an earlier recursion (random composition of m) or random monotone polynomial pieces.
# LHS_a     = sum_content weight * chi(u_top) * Phi_{t-1}(u_top)                    (what (S3)(a) bounds)
# LHS_label = sum_content weight * sum_{s>top, G_{<s}} 1/(2h+1) 1(|q*-s|<=h) Phi_{t-1}(s)   (true label sum, toy)
#   q*(content) = Q + sum_g sum_{y in sigma_g} d[y][g]; passing rows d>0 (q* increasing: the dangerous case).
# RHS = Phi_t(a) = E0^{-K} int_{E0}^{A_top} K y^{j-1} G(y) dy.  theta_toy = 1.
import random, itertools, math, sys
from fractions import Fraction as Fr
def integ_poly(coef, j, lo, hi, K):   # int_lo^hi K y^{j-1} sum_d coef[d] y^d dy  (float, exact formula)
    s=0.0
    for d,c in coef.items():
        e=j-1+d
        if e==-1: s+=K*float(c)*math.log(hi/lo)
        else: s+=K*float(c)*(hi**(e+1)-lo**(e+1))/(e+1)
    return s
def recursion_poly(js, A):            # G for composition js (all >=1), as polynomial dict, valid on [0,A]
    G={0:Fr(1)}; K=0
    for j in js:
        K+=j; new={}
        # G_t(E) = int_E^A K x^{j-1} G(x) dx = K * sum_d c_d (A^{j+d} - E^{j+d})/(j+d)
        for d,c in G.items():
            new[0]=new.get(0,Fr(0))+K*c*A**(j+d)/(j+d)
            new[j+d]=new.get(j+d,Fr(0))-K*c/(j+d)
        G=new
    return G
def run(seed):
    rnd=random.Random(seed)
    n=rnd.randint(1,5); p=sorted(rnd.sample(range(2,40),n))
    w=[Fr(1,x) for x in p]
    sl=[]; s=0
    for _ in range(n): s+=rnd.randint(1,3); sl.append(s)
    E0=Fr(rnd.randint(1,4)); 
    def Eu(u):
        v=E0
        for i in range(n):
            if sl[i]<u: v/=(1-w[i])
        return v
    m=rnd.randint(0,2); j=rnd.randint(0,1)
    if m+j==0: j=1
    K=m+j
    gthr=rnd.randint(sl[0]+1, sl[-1]+3)            # G_{<u} holds iff u<=gthr (also plays s_max)
    A=Eu(gthr)
    if m>0 and rnd.random()<0.6:
        comp=[]; r=m
        while r>0: c=rnd.randint(1,r); comp.append(c); r-=c
        coef=recursion_poly(comp,A); Gf=lambda x: float(sum(c*x**d for d,c in coef.items())) if x<=A else 0.0
        Gcoef_pieces=[(coef,A)]; GP=None
    else:
        c0=Fr(rnd.randint(0,3)); bs=[(Fr(rnd.randint(1,4)),rnd.choice([E0,A,(E0+A)/2]),rnd.randint(0,2)) for _ in range(rnd.randint(0,2))]
        def Gf(x,c0=c0,bs=bs):
            if x>A: return 0.0
            return float(c0+sum(wt*(b-x)**d for (wt,b,d) in bs if x<=b))
        Gcoef_pieces=None; GP=(c0,bs)
    Phi=lambda u: Gf(Eu(u))/float(Eu(u))**m
    h=rnd.randint(0,2); Q=rnd.randint(-3,sl[-1]+3)
    d=[[ (rnd.randint(1,4) if y<m else rnd.randint(-3,3)) for _ in range(n)] for y in range(K)]
    supports=[sg for r in range(1,K+1) for sg in itertools.combinations(range(K),r)]
    lhs_a=0.0; lhs_l=0.0
    for r in range(1,n+1):
        for S in itertools.combinations(range(n),r):
            top=max(S); u=sl[top]+1
            for sup in itertools.product(supports, repeat=r):
                wt=Fr(1); q=Q
                for g,sg in zip(S,sup):
                    wt*=(w[g]/(1-w[g]))**len(sg); q+=sum(d[y][g] for y in sg)
                wt=float(wt)
                if u<=gthr: lhs_a+=wt*Phi(u)
                for s in range(sl[top]+1, gthr+1):
                    if abs(q-s)<=h: lhs_l+=wt*Phi(s)/(2*h+1)
    # RHS = E0^{-K} int_{E0}^{A} K y^{j-1} G(y) dy  (numerical, fine grid, upper Riemann for safety not needed: report ratio)
    lo,hi=float(E0),float(A)
    if hi<=lo: rhs=0.0
    elif Gcoef_pieces is not None:
        rhs=integ_poly(Gcoef_pieces[0][0], j, lo, hi, K)
    else:
        # exact: G is a polynomial between breakpoints b (pieces active for x<=b)
        from math import comb
        bps=sorted(set([E0,A]+[b for (_,b,_) in GP[1] if E0<b<A]))
        rhs=0.0
        for lo_,hi_ in zip(bps,bps[1:]):
            coef={0:GP[0]}
            for (wt,b,dd) in GP[1]:
                if b>=hi_:
                    for e in range(dd+1):
                        coef[e]=coef.get(e,Fr(0))+wt*comb(dd,e)*b**(dd-e)*(-1)**e
            rhs+=integ_poly(coef,j,float(lo_),float(hi_),K)
    rhs/=float(E0)**K
    v3=None
    return lhs_a,lhs_l,rhs,(m,j)
worst_a=0; worst_l=0; worst_lab_over_a=0; N=int(sys.argv[1]) if len(sys.argv)>1 else 1500; zero_viol=0
for s in range(N):
    la,ll,r,mj=run(s)
    if r<=1e-300:
        if la>1e-12 or ll>1e-12: zero_viol+=1
        continue
    worst_a=max(worst_a,la/r); worst_l=max(worst_l,ll/r)
    if la>0: worst_lab_over_a=max(worst_lab_over_a,ll/la)
print(f"{N} instances: max LHS_a/RHS={worst_a:.12f}  max LHS_label/RHS={worst_l:.12f}  max LHS_label/LHS_a={worst_lab_over_a:.6f}  zero-RHS violations={zero_viol}")
