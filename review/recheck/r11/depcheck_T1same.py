# Dependency graph of the paper. An edge (A, B, kind) means: A uses B.
# kind '<' : B is used only at a strictly earlier time or a strictly smaller height (marked with a down-arrow in the paper).
# kind '=' : B is used at the same time.
# Node names are the LaTeX labels of the paper source. Conventions:
#   'a..b'      the consecutive results from label a to label b;
#   'a+b'       two items treated as one node;
#   'lab(a)(c)' parts (a) and (c) of the result with label lab;
#   'cite:key'  an external result, by its bibliography key; 'Rankin' and 'Paley-Zygmund' are the standard inequalities.
# Usage: python3 -I depcheck.py [--nodes]
import collections, sys

E = []
def dep(a, bs, kind='='):
    for b in bs.split(','):
        b = b.strip()
        if b: E.append((a, b, kind))

# Section 2 (construction), Section 3 (zeros), Section 7 (base range)
dep('lem:adapted', 'lem:C2')
dep('lem:G1', 'eq:huxley,eq:ampl')
dep('lem:T1', 'lem:lemmaP'); dep('lem:T1', 'Rankin')
dep('lem:count..lem:excess', 'sec:greedy')
dep('eq:huxley', 'cite:HeathBrown1988')
dep('lem:blin', 'eq:huxley')
dep('lem:margin', 'eq:huxley,lem:blin'); dep('lem:margin', 'lem:cm,lem:T1,prop:La', '<')
dep('lem:ZB', 'eq:rhodet')
dep('lem:ZA', 'lem:lemmaP,thm:caplw(b)(c)', '<')
dep('lem:ZBlow', 'eq:rhodet')
dep('lem:designedzero..lem:goodheights', 'lem:ZB,cite:MontgomeryVaughan1974,Paley-Zygmund,cite:BrouckeDebruyne2023')
dep('lem:designedzero..lem:goodheights', 'prop:La,lem:ZA', '<')
dep('thm:zeros', 'lem:designedzero..lem:goodheights,lem:ZB,prop:La,lem:ZA')
dep('prop:La', 'cor:lag,thm:queue,lem:budget')
dep('thm:A', 'lem:T1,prop:La,thm:zeros,lem:budget')

# Section 4 (noise response)
dep('lem:cm', 'eq:HBS'); dep('eq:HBS', 'thm:queue', '<'); dep('eq:HBS', 'lem:T1'); dep('eq:HBS', 'cor:lag', '<')
dep('lem:smooth-v', 'lem:cm')
dep('thm:bs', 'lem:cm,lem:smooth-v,lem:bs-profile')
dep('cor:saias', 'thm:bs,lem:lemmaM')
dep('thm:kr', 'lem:lemmaM,eq:RH,cor:saias')
dep('thm:kr-random', 'thm:kr')                                     # random widths (corrections log, #3)
dep('cor:kr-weights', 'thm:kr-random,lem:lemmaM,cor:saias,eq:RH')
dep('prop:true-kernels', 'thm:kr,lem:tau-near')
dep('prop:true-kernels', 'thm:kr-random,cor:kr-weights,cor:saias,lem:lemmaM')
dep('prop:true-kernels', 'cor:lag,lem:lemmaP,prop:ecl')              # the count of absorbed elements (#4)
dep('lem:tau-near', 'lem:cm,lem:smooth-v'); dep('lem:tau-near', 'cor:localcount', '<')
dep('lem:S', 'lem:smooth-v')
dep('lem:noise', 'cite:Freedman1975,lem:S'); dep('lem:noise', 'thm:queue,prop:ecl,lem:lemmaP', '<')
dep('lem:threshold-mass', 'lem:cm'); dep('lem:threshold-mass', 'cor:localcount,cor:lag,lem:lemmaP', '<')   # lag and Lemma P: case (i) (#61)
dep('thm:lp', 'lem:ZBlow,eq:Rhatbound,lem:T1,lem:cm'); dep('thm:lp', 'thm:queue', '<')
dep('eq:osc', 'eq:rhodet,lem:rhoA(c)')
dep('lem:rhoA(c)', 'lem:rhoA(a)(b)'); dep('lem:rhoA(a)(b)', 'lem:lemmaP', '<')
dep('prop:br', 'thm:kr,prop:true-kernels,cor:saias,lem:tau-near,eq:osc')
dep('lem:bs-profile', 'lem:cm,lem:smooth-v')
dep('lem:si', 'lem:bs-profile,thm:lp,lem:cm')
dep('lem:xb', 'thm:kr,prop:true-kernels,lem:tau-near,lem:si'); dep('lem:xb', 'cor:localcount,lem:lemmaP', '<')
dep('lem:xb', 'prop:br,thm:kr-random,cor:kr-weights')              # tau-term via the near-threshold argument (#5)
dep('lem:predictable', 'prop:true-kernels,lem:tau-near,lem:S,lem:noise,eq:osc')
dep('prop:g1', 'lem:margin,lem:lemmaM,lem:threshold-mass,lem:predictable,cor:saias,thm:lp,prop:br,eq:ampl,lem:xb')
dep('prop:g1', 'cor:localcount', '<')                              # Step 1 of range (B)
dep('thm:g2', 'lem:predictable,prop:br,prop:g1,lem:xb')
dep('prop:pointwise', 'lem:noise,lem:tau-near,lem:S,eq:osc,thm:g2,lem:xb,prop:g1,eq:huxley,lem:margin')
dep('cor:r1', 'prop:pointwise')

# Section 6 (queue) and Appendix A
dep('eq:sF1+eq:sF2', 'sec:greedy'); dep('eq:sF3p+eq:sF4', 'lem:cm', '<')
dep('eq:sF3p+eq:sF4', 'thm:caplw(b)(c)')                              # (F3') uses the size of H (#2)
dep('lem:landing', 'eq:sF1+eq:sF2,cite:Freedman1975,thm:caplw(b)(c)')
dep('cor:localcount', 'lem:landing,lem:count..lem:excess,cor:lag'); dep('cor:localcount', 'thm:queue', '<')
dep('thm:queue', 'cor:r1,eq:sF1+eq:sF2,lem:count..lem:excess,cite:Freedman1975,thm:caplw(b)(c)')
dep('thm:queue', 'prop:ecl,cor:increment,eq:sF3p+eq:sF4,thm:queue', '<')
dep('lem:budget', 'thm:queue,prop:ecl,lem:landing,lem:noise')
dep('prop:ecl', 'thm:R,lem:heavy,thm:caplw(a),thm:caplw(b)(c)')
dep('cor:increment', 'prop:ecl')
dep('prop:cover', 'lem:volume,lem:fac,thm:svl,lem:SC')
dep('lem:reduction', 'lem:heavy,lem:covering..thm:tcl,prop:cover')
dep('lem:rowweights', 'Rankin')
dep('thm:caplw(a)', 'lem:heavy,lem:reduction,lem:rowweights,lem:covering..thm:tcl')
dep('thm:caplw(b)(c)', '')                                            # deterministic facts about the parameters
dep('lem:lemmaP', 'lem:cm,thm:caplw(b)(c)'); dep('lem:lemmaP', 'prop:ecl,cor:localcount', '<')
dep('lem:rhoA', 'lem:lemmaP')
dep('prop:S1S2', 'lem:lemmaP,cor:increment')
dep('lem:raisedy', 'thm:caplw(a),thm:caplw(b)(c),lem:lemmaP,lem:rhoA')
dep('lem:pil', 'eq:sF3p+eq:sF4,eq:sF1+eq:sF2,lem:fac,thm:caplw(b)(c)'); dep('lem:fac', 'eq:sF3p+eq:sF4,thm:caplw(b)(c)')
dep('thm:svl', 'lem:volume,lem:SC')
dep('thm:R', 'lem:volume,lem:pil,lem:fac,lem:SC,thm:svl,eq:sF1+eq:sF2,thm:caplw(b)(c)')

G = collections.defaultdict(set)
for a, b, k in E:
    if k == '=':
        G[a].add(b)
nodes = set(a for a, _, _ in E) | set(b for _, b, _ in E)
for a, b, k in E:
    if a == b and k == '=':
        print('SAME-TIME SELF-LOOP:', a)
# cycle detection on the same-time edges
color = {}
def dfs(u, stack):
    color[u] = 1; stack.append(u)
    for v in sorted(G[u]):
        if color.get(v) == 1:
            print('CYCLE:', ' -> '.join(stack[stack.index(v):] + [v])); return True
        if color.get(v) is None and dfs(v, stack): return True
    color[u] = 2; stack.pop(); return False
found = any(dfs(n, []) for n in sorted(nodes) if color.get(n) is None)
if '--nodes' in sys.argv:
    print('\n'.join(sorted(nodes)))
print('same-time subgraph acyclic:', not found, '| nodes', len(nodes), '| edges', len(E),
      '| strictly-earlier edges', sum(k == '<' for _, _, k in E))
