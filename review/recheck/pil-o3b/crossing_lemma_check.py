# Exact check of the crossing lemma in the union reading (piece of ANY size), toy with sets.
# Slots 0..N-1 carry primes with weights w_i (toy 1/p); E(s)=E0*prod_{j<s}(1+w_j) (set Euler product).
# Pinned value q*(c) = Q + sum_{i in c} d_i (additive toy of log q*; d_i>0 <-> q* increasing <-> "negative row").
# LHS = sum_c prod w_c * sum_{s>top(c), s<=smax} 1/(2h+1) 1(|q*(c)-s|<=h) / E(s)   (one passing row, carried 1/E(s)).
# Crossing bound: LHS*E0 <= 1 + sum_{i: d_i>0} w_i/(1+w_i).  Claimed v3 bound (no loss): LHS*E0 <= 1.
import random, itertools, sys
from fractions import Fraction as Fr
def run(seed):
    rnd=random.Random(seed); N=rnd.randint(1,9); h=rnd.randint(0,2)
    w=[Fr(1,rnd.randint(2,9)) for _ in range(N)]
    E0=Fr(1); E=[E0]
    for x in w: E.append(E[-1]*(1+x))
    mode=rnd.choice(['inc','dec','mix'])
    d=[rnd.randint(1,4) if mode=='inc' else (-rnd.randint(0,3) if mode=='dec' else rnd.randint(-3,4)) for _ in range(N)]
    Q=rnd.randint(-2,N+2); smax=N+h+3
    lhs=Fr(0)
    for r in range(N+1):
        for c in itertools.combinations(range(N),r):
            wt=Fr(1)
            for i in c: wt*=w[i]
            top=max(c) if c else -1; q=Q+sum(d[i] for i in c)
            for s in range(top+1,smax+1):
                if abs(q-s)<=h: lhs+=wt*Fr(1,2*h+1)/E[min(s,N)]
    bound=1+sum(w[i]/(1+w[i]) for i in range(N) if d[i]>0)
    return lhs*E0, bound, mode
worst=0; worst_v3={'inc':0,'dec':0,'mix':0}
for s in range(int(sys.argv[1]) if len(sys.argv)>1 else 4000):
    l,b,m=run(s); worst=max(worst,l/b); worst_v3[m]=max(worst_v3[m],l)
print('max LHS/crossing-bound =',float(worst))
print('max LHS*E0 by mode (v3 claim is <=1):',{k:float(v) for k,v in worst_v3.items()})
