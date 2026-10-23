# Monte Carlo of E[#crossings] for the relaxed (union-over-free-structures) label sum at one boundary.
# R = random multiplicative set (squarefree relaxation): its primes g in [a,b] have y=log log g forming a rate-1
# Poisson process. Normalise x=log g/log a in [1,D]. Pinned value q*(c)=K*c^beta, log K = kappa*log a.
# A crossing = a split point s (in log scale X=log s/log a >= 1) with X = kappa + beta*sum_{g<s} x_g, lying in
# [x_i, x_{i+1}) between consecutive R-primes (x_0 := 1). E[#crossings] = loss factor relative to the claimed
# cancellation (which corresponds to exactly one crossing). Window fuzz H is ignored (relative size H/q ~ 0).
import random, math, sys
def trial(D,kappa,beta,rnd):
    ys=[]; y=0.0; ymax=math.log(D)
    while True:
        y+=rnd.expovariate(1.0)
        if y>ymax: break
        ys.append(y)
    xs=[math.exp(v) for v in ys]
    n=0; S=0.0; lo=1.0
    for i in range(len(xs)+1):
        hi=xs[i] if i<len(xs) else D
        X=kappa+beta*S
        if lo<=X<hi: n+=1
        if i<len(xs): S+=xs[i]; lo=xs[i]
    return n
rnd=random.Random(1)
for beta in (1.0,0.5,0.1):
  for kappa in (1.0,1.5):
    row=[]
    for D in (10,100,1000,10**4,10**6):
        N=20000; m=sum(trial(D,kappa,beta,rnd) for _ in range(N))/N
        row.append(f"D={D}:{m:.3f}")
    print(f"beta={beta} kappa={kappa}  "+"  ".join(row))
