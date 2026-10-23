import re, sys
exec(open(sys.argv[3]).read().split("tot = miss = 0")[0].replace("patch, txt = sys.argv[1], sys.argv[2]", "patch, txt = sys.argv[1], sys.argv[2]"))
for h, lines in hunks:
    fs = [f for s in lines for f in frags(s)]
    hit = sum(1 for f in fs if f in norm)
    print(f"{h:40s} content-lines={len(lines):2d} fragments={len(fs):2d} found={hit:2d}")
print(len(hunks), "hunks")
