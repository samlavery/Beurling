import re, sys
patch, txt = sys.argv[1], sys.argv[2]
raw = open(txt, encoding='utf-8', errors='replace').read()
norm = re.sub(r'-\n', '', raw)
norm = norm.replace('\ufb01', 'fi').replace('\ufb02', 'fl').replace('\u2019', "'").replace('\u201c', '"').replace('\u201d', '"')
norm = re.sub(r'\s+', ' ', norm)
hunks, cur = [], None
for line in open(patch, encoding='utf-8'):
    if line.startswith('@@'):
        cur = [line.strip(), []]; hunks.append(cur)
    elif line.startswith('+') and not line.startswith('+++') and cur is not None:
        s = line[1:].rstrip('\n')
        if s.lstrip().startswith('%'): continue
        cur[1].append(s)
def frags(s):
    s = re.sub(r'\$[^$]*\$', ' | ', s)                      # inline math
    s = re.sub(r'\\(?:ref|eqref|label|cite)\{[^}]*\}', ' | ', s)
    s = re.sub(r'~', ' ', s)
    s = re.sub(r'\\(?:emph|textup|text)\{([^}]*)\}', r'\1', s)
    s = re.sub(r'\\[A-Za-z]+\*?', ' | ', s)
    s = re.sub(r'[{}\\]', ' ', s)
    out = []
    for piece in s.split('|'):
        w = piece.split()
        w = [x for x in w if re.fullmatch(r"[A-Za-z][A-Za-z'\-]*[,;:.]?|\(?[A-Za-z]+\)?[,;:.]?", x)]
        if len(w) >= 3: out.append(' '.join(w).strip(' ,;:.'))
    return out
tot = miss = 0
for h, lines in hunks:
    for s in lines:
        for f in frags(s):
            tot += 1
            if f not in norm:
                miss += 1; print('MISS', h, '::', f)
print('fragments', tot, 'missed', miss)
