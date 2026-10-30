import sys, os, ast
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from x0gen import subs, nOf, hordv
DECL=int(sys.argv[1]); PERFILE=int(sys.argv[2]); OUT=sys.argv[3]
G=[ast.literal_eval(l) for l in open('/tmp/rhscratch/x0/genlist.txt').read().split('\n')]
assert len(G)==785
def cost(v): return len(subs(v))+10
decls=[]; cur=[]; c=0
for v in G:
    if cur and c+cost(v)>DECL:
        decls.append(cur); cur=[]; c=0
    cur.append(v); c+=cost(v)
decls.append(cur)
files=[decls[i:i+PERFILE] for i in range(0,len(decls),PERFILE)]
os.makedirs(OUT,exist_ok=True)
k=0
for fi,ds in enumerate(files):
    L=['module','','public import RequestProject.BSCert.Finite.X0Rep','',
       '/-! Kernel-checked slices %d–%d of the representatives of `x0band_exact.py` (`X0BandCert`). -/'%(k,k+len(ds)-1),'',
       '@[expose] public section','','namespace BSCert.X0Rep','']
    for vs in ds:
        hss=[]
        for v in vs:
            if all(a==0 for a in v): hss.append([]); continue
            h=hordv(v); hss.append([h[nOf(w)] for w in subs(v)])
        L.append('def sl%d : List (List ℕ) := [%s]'%(k,', '.join(str(v) for v in vs)))
        L.append('')
        L.append('def ct%d : List (List ℕ) := [%s]'%(k,', '.join(str(h) for h in hss)))
        L.append('')
        L.append('theorem ok%d : chkL sl%d ct%d = true := by decide +kernel'%(k,k,k))
        L.append('')
        k+=1
    L.append('end BSCert.X0Rep')
    open(os.path.join(OUT,'X0C%d.lean'%fi),'w').write('\n'.join(L)+'\n')
print(len(decls),'decls',len(files),'files')
