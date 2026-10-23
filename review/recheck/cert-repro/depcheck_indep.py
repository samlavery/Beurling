# Independent check of depcheck: re-read the edge list (only the dep() calls), Kahn topological sort on the same-time
# edges, duplicate edges, the sanity cycle of App B, and that every internal node name is a \label of the snapshot.
import re, glob, collections
src = open('/tmp/rhscratch/cert-repro/src/certificates/depcheck/depcheck.py').read()
E = []
for a, bs, kind in re.findall(r"dep\('([^']*)',\s*'([^']*)'(?:,\s*'([<=])')?\)", src):
    for b in bs.split(','):
        if b.strip(): E.append((a, b.strip(), kind or '='))
nodes = {a for a, _, _ in E} | {b for _, b, _ in E}
dups = [e for e, c in collections.Counter(E).items() if c > 1]
print('edges', len(E), 'distinct', len(set(E)), 'nodes', len(nodes), 'strictly-earlier', sum(k == '<' for *_, k in E), 'duplicates', dups)
def acyclic(edges):
    G = collections.defaultdict(set); indeg = collections.Counter()
    for a, b, k in edges:
        if k == '=' and b not in G[a]: G[a].add(b); indeg[b] += 1
    q = [n for n in nodes if indeg[n] == 0]; seen = 0
    while q:
        n = q.pop(); seen += 1
        for m in G[n]:
            indeg[m] -= 1
            if indeg[m] == 0: q.append(m)
    return seen == len(nodes), [n for n in nodes if indeg[n] > 0]
print('same-time acyclic (Kahn):', acyclic(E)[0])
ok, rest = acyclic(E + [('eq:sF3p+eq:sF4', 'thm:caplw(a)', '=')])
print('with eq:sF3p+eq:sF4 -> thm:caplw(a): acyclic =', ok, '; nodes on/after cycles:', sorted(rest))
labels = set()
for f in glob.glob('/tmp/rhscratch/cert-repro/src/paper/sections/*.tex'):
    labels |= set(re.findall(r'\\label\{([^}]*)\}', open(f).read()))
missing = []
for n in sorted(nodes):
    if n.startswith('cite:') or n in ('Rankin', 'Paley-Zygmund'): continue
    for part in re.split(r'\.\.|\+', re.sub(r'\([a-z]\)', '', n)):
        if part not in labels: missing.append((n, part))
print('node labels missing from the LaTeX source:', missing)
bib = open('/tmp/rhscratch/cert-repro/src/paper/refs.bib').read()
print('cite keys missing from refs.bib:', [n for n in nodes if n.startswith('cite:') and n[5:] not in bib])
