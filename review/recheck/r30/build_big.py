import sys, time, pickle, math
sys.path.insert(0, "/tmp/rhscratch/r30/indep")
from dickman import build
t=time.time(); logrho, C = build(270000)
print("built in", round(time.time()-t,1), "s; max terms", max(len(c) for c in C[1:]))
with open("/tmp/rhscratch/r30/indep/rho270k.pkl","wb") as f: pickle.dump((logrho, C), f)
