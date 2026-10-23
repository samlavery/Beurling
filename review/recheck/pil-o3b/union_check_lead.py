# Union over all free structures owned by a passing row y1 in one block [a, smax):
# sum over nonempty multisets S of primes (slots = index order) of prod g^-e * 1/Eu(u(max S)),
# where Eu(x) = prod_{a<=slot<x} (1-1/g)^-1 (relative to Eu(a)=1). Compare with lambda = sum 1/g.
from fractions import Fraction as F
import itertools, math
primes=[101,103,107,109,113,127,131,137,139,149,151,157]
def Eu(k):  # product over first k primes
    r=F(1)
    for g in primes[:k]: r*=F(g,g-1)
    return r
EMAX=4
tot=F(0)
for k in range(len(primes)):           # index of max element f = primes[k]
    f=primes[k]
    fpart=sum(F(1,f**e) for e in range(1,EMAX+1))
    below=F(1)
    for g in primes[:k]: below*=sum(F(1,g**e) for e in range(0,EMAX+1))
    tot+=fpart*below/Eu(k+1)
lam=sum(F(1,g) for g in primes)
print("union sum =",float(tot)," lambda =",float(lam), " per-r exact count bound (r fixed) <= 1")
