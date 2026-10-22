# Dependency graph of v3; edge (A, B, kind): A uses B. kind '<' = B used only at strictly earlier time / smaller height.
E = []
def dep(a, bs, kind='='):
    for b in bs.split(','):
        b = b.strip()
        if b: E.append((a, b, kind))
# §1, §2, §5 (part-S)
dep('L1.1', 'C2')
dep('G1', '5.2,A')
dep('T1', 'L4.18', '<'); dep('T1', 'Rankin')
dep('L1.2-1.5', 'ruleG')
dep('5.2', 'HB88')
dep('L5.1', '5.2')
dep('L5.2', '5.2,L5.1'); dep('L5.2', 'L3.1,T1,La', '<')
dep('L2.0', 'B-lin'); dep('L2.0p', 'L4.18,T4.17', '<'); dep('L2.0pp', 'B-lin,Titchmarsh')
dep('L2.1-2.3', 'L2.0,MV,PZ,BD'); dep('L2.1-2.3', 'La,L2.0p', '<')
dep('T2.4', 'L2.1-2.3,L2.0,La,L2.0p')
dep('La', '1.5,T4.3,L4.5')
dep('ThmA', 'T1,La,T2.4,L4.5')
# §3 (part-F rows)
dep('L3.1', 'HBS'); dep('HBS', 'T4.3', '<')
dep('L3.2', 'L3.1')
dep('L3.3', '')
dep('T3.4', 'L3.1,L3.2'); dep('C3.5', 'T3.4,L3.3')
dep('T3.6', 'L3.3,RH,C3.5'); dep('P3.8', 'T3.6,L3.9')
dep('L3.9', 'L3.1,L3.2'); dep('L3.9', 'C4.2', '<')
dep('L3.10', 'L3.2')
dep('L3.11', 'Freedman,L3.10'); dep('L3.11', 'T4.3,P4.6,C4.2,L4.18', '<')
dep('L3.12', 'L3.1'); dep('L3.12', 'C4.2', '<')
dep('T3.13', 'L2.0pp,R2.2,T1,L3.1'); dep('T3.13', 'T4.3', '<')  # incl. Lemma 2.0'' fine form, Lemma 3.1(ii)
dep('Osc', 'B-lin,L4.19d')  # E2E NC-1: no current-height local count
dep('L4.19d', 'L4.19ac'); dep('L4.19ac', 'L4.18', '<')  # 4.19(d) <- (a),(c) <- Lemma 4.18 at heights < u
dep('P3.14', 'T3.6,P3.8,C3.5,L3.9,Osc')  # BR on the jump-free part T'_c
dep('L3.4A', 'L3.1,L3.2'); dep('T3.4', 'L3.4A')
dep('L3.14B', 'L3.4A,T3.13,L3.1')  # SI(Lambda)
dep('L3.14A', 'T3.6,P3.8,L3.9,L3.14B'); dep('L3.14A', 'C4.2,L4.18', '<')  # XB: the X0 jump
dep('L3.15', 'P3.8,L3.9,L3.10,L3.11,Osc')
dep('P3.16', 'L5.2,L3.3,L3.12,L3.15,C3.5,T3.13,P3.14,A,L3.14A')
dep('T3.17', 'L3.15,P3.14,P3.16,L3.14A')
dep('P3.18', 'L3.11,L3.9,L3.10,Osc,T3.17,L3.14A,P3.16,5.2,L5.2')
dep('C3.19', 'P3.18')
# §4 (part-G rows)
dep('F1F2', 'ruleG'); dep('F3F4', 'L3.1', '<')
dep('L4.1', 'F1F2,Freedman')
dep('C4.2', 'L4.1,L1.2-1.5'); dep('C4.2', 'T4.3', '<')
dep('T4.3', 'C3.19,F1F2,L1.2-1.5,Freedman'); dep('T4.3', 'P4.6,C4.7,F3F4', '<'); dep('T4.3', 'T4.3', '<')
dep('L4.5', 'T4.3,P4.6,L4.1,L3.11')  # E5 dropped: Thm 3.13 is used pathwise
dep('P4.6', 'TA.6,L4.8,T4.17'); dep('C4.7', 'P4.6')
dep('L4.9-4.12', ''); dep('P4.13', 'LA.1,LA.4,TA.5,LA.7')
dep('L4.14', 'L4.8,L4.9-4.12,P4.13'); dep('L4.15', 'Rankin')
dep('T4.17', 'L4.8,L4.14,L4.15,L4.9-4.12')
dep('L4.18', 'L3.1,T4.17'); dep('L4.18', 'P4.6', '<')
dep('L4.19', 'L4.18'); dep('L4.19', 'C4.2', '<')
dep('P4.20', 'L4.18,C4.7'); dep('L4.21', 'T4.17,L4.18,L4.19')
dep('LA.1', ''); dep('LA.3', 'F3F4'); dep('LA.4', 'F3F4'); dep('TA.5', 'LA.1,LA.7'); dep('LA.7', '')
dep('TA.6', 'LA.1,LA.3,LA.4,LA.7,TA.5,F1F2')
import collections
G = collections.defaultdict(set)
for a, b, k in E:
    if k == '=':
        G[a].add(b)
# cycle detection on same-time edges
color = {}
def dfs(u, stack):
    color[u] = 1; stack.append(u)
    for v in G[u]:
        if color.get(v) == 1:
            print('CYCLE:', ' -> '.join(stack[stack.index(v):] + [v])); return True
        if color.get(v) is None and dfs(v, stack): return True
    color[u] = 2; stack.pop(); return False
nodes = set(a for a, _, _ in E) | set(b for _, b, _ in E)
found = any(dfs(n, []) for n in sorted(nodes) if color.get(n) is None)
print('same-time subgraph acyclic:', not found, '| nodes', len(nodes), '| edges', len(E), '| strictly-earlier edges', sum(k == '<' for _, _, k in E))
# which same-time chains reach T4.3 from T4.3's same-time inputs (should not)
