# Step 2: max over z of  int_{[1,z]} dPi/u - log log z  for N = rational integers (z in [e, 1e7]),
# and the Lemma cm(iv)-route bound used for the realised system: 1/2 + log(1/log 2) + 2.20/log 2 + sum_p sum_{k>=2} 1/(k p^k).
import math
LIM = 10**7
sieve = bytearray([1])*(LIM+1); sieve[0]=sieve[1]=0
for i in range(2, int(LIM**0.5)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
ev = []
for p in range(2, LIM+1):
    if sieve[p]:
        q = p; k = 1
        while q <= LIM:
            ev.append((q, 1.0/(k*q))); q *= p; k += 1
ev.sort()
acc = 0.0; best = -1e9; bz = None
# the difference is maximal just after a jump (log log z increasing); check at each jump point z = q (and at z = e)
best = 0.5 - 0.0; bz = math.e  # at z = e: only p = 2 counted, log log e = 0
for q, w in ev:
    acc += w
    if q >= 3:
        d = acc - math.log(math.log(q))
        if d > best: best, bz = d, q
print(f"rational N: max_z>=e (int_[1,z] dPi/u - log log z) = {best:.5f} at z = {bz}  (paper allows 4.5)")
pp = sum(1.0/(k*p**k) for p in range(2, 10**6) if sieve[p] for k in range(2, 60) if p**k < 1e300)
route = 0.5 + math.log(1/math.log(2)) + 2.20/math.log(2) + pp
print(f"Lemma cm(iv) route (y0=2): 1/2 + log(1/log2) + 2.2/log2 + prime powers({pp:.5f}) = {route:.4f} <= 4.5")
