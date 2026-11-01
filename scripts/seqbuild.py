#!/usr/bin/python3 -I -B
"""Sequentially build the import closure of a target module, one Lean process at a time."""
import os, re, sys, subprocess, time
root = os.path.expanduser('~/work/beurling-paper/lean')
os.chdir(root)
imp = {}
for d, _, fs in os.walk('RequestProject'):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f); m = p[:-5].replace('/', '.')
            imp[m] = re.findall(r'^(?:public |meta )?import (RequestProject\S*)', open(p).read(), re.M)
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imp.get(m, []): visit(d)
    order.append(m)
for t in sys.argv[1:]: visit(t)
log = open('/tmp/rhscratch/seqbuild.log', 'a')
for m in order:
    r = subprocess.run(['lake', 'build', '--no-build', m], capture_output=True)
    if r.returncode == 0: continue
    t0 = time.time()
    subprocess.run(['/tmp/rhscratch/watch_build.sh', m, '/tmp/rhscratch/seq_one.out'])
    out = open('/tmp/rhscratch/seq_one.out').read()
    err = out.count('\nerror') + out.startswith('error')
    rss = re.findall(r'watch max rss KB: (\d+)', out)
    line = f"{m} secs={time.time()-t0:.0f} errors={err} killed={'KILLED' in out} rss={rss[-1] if rss else '?'}"
    print(line, flush=True); log.write(line + '\n'); log.flush()
    if err or 'KILLED' in out:
        open(f'/tmp/rhscratch/seqfail_{m}.out', 'w').write(out)
        print('STOP', flush=True); log.write('STOP\n'); break
print('DONE', flush=True); log.write('DONE\n')
