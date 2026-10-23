# Check prod_{p<=y}(1-p^{2/log y-1})^{-1} <= 2 e^gamma e^{Ein(2)} log y for rational primes (moderate y).
import math
N = 10**7
s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
for i in range(2, int(N ** .5) + 1):
    if s[i]: s[i*i::i] = bytearray(len(range(i*i, N + 1, i)))
ps = [i for i in range(N + 1) if s[i]]
g = 0.5772156649015329; Ein2 = 3.6838715105404120
for y in [1e3, 1e4, 1e5, 1e6, 1e7]:
    c = 2 / math.log(y)
    lp = sum(-math.log(1 - p ** (c - 1)) for p in ps if p <= y)
    ratio = math.exp(lp) / (math.exp(g) * math.exp(Ein2) * math.log(y))
    print(f"y={y:.0e}: prod / (e^g e^Ein2 log y) = {ratio:.4f}  (paper allows 2)")
