import re, sys
patches = sys.argv[1:-1]
txt = open(sys.argv[-1]).read()
def norm(s):
    s = s.replace('\u2010','-').replace('\u2011','-').replace('ﬁ','fi').replace('ﬂ','fl').replace('ﬀ','ff').replace('ﬃ','ffi').replace('ﬄ','ffl')
    s = re.sub(r'-\n', '', s)   # hyphenation
    s = re.sub(r'\s+', ' ', s)
    return s
T = norm(txt)
missing = 0; total = 0
for p in patches:
    lines = [l[1:] for l in open(p).read().splitlines() if l.startswith('+') and not l.startswith('+++')]
    for l in lines:
        if l.lstrip().startswith('%'): continue
        # strip math and commands
        t = re.sub(r'\$[^$]*\$', ' @ ', l)
        t = re.sub(r'\\(ref|eqref|label|cite)\{[^}]*\}', ' @ ', t)
        t = re.sub(r'\\[a-zA-Z]+\*?(\[[^\]]*\])?', ' ', t)
        t = t.replace('{',' ').replace('}',' ').replace('~',' ')
        # find runs of >=4 plain words
        for run in re.split(r'@|[()\[\];:]', t):
            words = re.findall(r"[A-Za-z][A-Za-z'\-]*[,.]?", run)
            if len(words) >= 4:
                frag = ' '.join(w.rstrip(',.') for w in words[:6])
                total += 1
                # loose search: words in order with arbitrary punctuation between
                pat = r'\W+'.join(re.escape(w.rstrip(',.')) for w in words[:6])
                if not re.search(pat, T):
                    missing += 1
                    print(f"MISSING [{p.split('/')[-1]}]: {frag!r}   <- {l.strip()[:120]}")
print(f"checked {total} fragments, missing {missing}")
