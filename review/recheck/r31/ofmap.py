import re, sys
log = open(sys.argv[1], encoding='latin-1').read()
stack = []
out = []
i = 0
tok = re.compile(r'\((\./[^\s()]+|/[^\s()]+)|\)|Overfull \\hbox \(([\d.]+)pt too wide\) (?:in paragraph |detected )?at lines? (\d+)(?:--(\d+))?')
for m in tok.finditer(log):
    if m.group(1):
        stack.append(m.group(1))
    elif m.group(0) == ')':
        if stack: stack.pop()
    else:
        f = [s for s in stack if 'sections' in s or s.endswith('.tex')]
        out.append((f[-1] if f else '?', m.group(3), m.group(4), m.group(2)))
for o in out: print(o)
