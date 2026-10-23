# Independent brute-force check (exact rationals) of the block lemma of the u-chain repair.
# Toy: realised primes at slots 0..N-1 (slot range of the block starts at the cut b = 0, i.e. "u_{t+1}"),
# weights w_i = 1/p_i, Eu(i) = E0 * prod_{j<i} (1-w_j)^{-1} (primes decided before slot i).
# Good events nested: G_{<v} holds iff v <= g.  A := Eu(g) >= Eu(v) for all v <= g  (toy "sure bound").
# Type: m columns in decision order (latest first), owner row and exponent a>=1 per column (weight w^a).
# Rows: 'P' passing (carried 1/Eu(u)), 'F' fresh.  u := (top slot)+1.
# LHS = sum over strictly decreasing slot m-tuples of prod w^a * prod_P 1/Eu(u) * 1(u<=g)
# RHS = prod_P 1/E0 * prod_{F with >=1 column} A/E0
# Also: LHS_label = worst case over q* of the label sum, toy windows of half-width h on integer slots:
#   sum_data prod w^a * max_{q} sum_{s>top, s<=g, |q-s|<=h} (1/(2h+1)) prod_P 1/Eu(s);  theta_toy = 1.
import random, itertools, sys
from fractions import Fraction as Fr
def inst(rnd):
    N=rnd.randint(1,8); p=[rnd.randint(2,12) for _ in range(N)]; w=[Fr(1,x) for x in p]
    E0=Fr(rnd.randint(1,5),rnd.randint(1,3)); Eu=[E0]
    for x in w: Eu.append(Eu[-1]/(1-x))
    g=rnd.randint(0,N)
    nr=rnd.randint(1,4); kinds=[rnd.choice('PF') for _ in range(nr)]
    m=rnd.randint(1,min(4,N)); own=[rnd.randrange(nr) for _ in range(m)]; ex=[rnd.choice([1,1,1,2]) for _ in range(m)]
    return N,w,Eu,E0,g,kinds,own,ex
def run(seed,h=2):
    rnd=random.Random(seed); N,w,Eu,E0,g,kinds,own,ex=inst(rnd)
    A=Eu[g]; nP=kinds.count('P')
    lhs=Fr(0); lab=Fr(0)
    for tup in itertools.combinations(range(N),len(own)):
        t=sorted(tup,reverse=True); top=t[0]; u=top+1
        wt=Fr(1)
        for i,a in zip(t,ex): wt*=w[i]**a
        if u<=g: lhs+=wt/Eu[u]**nP
        # label sum, adversarial pinned value q (scan integer and half-integer q)
        best=Fr(0)
        for q2 in range(2*(top-h),2*(g+h)+2):
            q=Fr(q2,2); v=Fr(0)
            for s in range(top+1,g+1):
                if abs(q-s)<=h: v+=Fr(1,2*h+1)/Eu[min(s,N)]**nP
            best=max(best,v)
        lab+=wt*best
    owned=set(own)
    rhs=(1/E0)**nP
    for r,k in enumerate(kinds):
        if k=='F' and r in owned: rhs*=A/E0
    return lhs,lab,rhs
worst=Fr(0); worstlab=Fr(0)
n=int(sys.argv[1]) if len(sys.argv)>1 else 3000
for s in range(n):
    l,lab,r=run(s)
    if l/r>worst: worst=l/r; ws=s
    if lab/r>worstlab: worstlab=lab/r; wls=s
print('instances',n,'max LHS/RHS',float(worst),'seed',ws,' max LHS_label/RHS',float(worstlab),'seed',wls)
