from flint import arb, ctx
ctx.prec = 120
def fb(a, b):
    a=arb(a); b=arb(b)
    u = arb(((a+b)/2).mid(), ((b-a)/2).upper())
    return (1+u)/(u+1).gamma()
stack = [(arb(0), arb(40))]
lim = arb("2.007"); ncell=0; worst=arb(0)
while stack:
    a,b = stack.pop()
    v = fb(a,b).upper()
    if v <= lim:
        ncell+=1
        if v>worst: worst=v
        continue
    if (b-a) < arb("1e-12"):
        print("FAIL near", a.str(15)); break
    m=(a+b)/2; stack.append((a,m)); stack.append((m,b))
print("cells", ncell, "all <= 2.007; worst cell upper", worst.str(10))
