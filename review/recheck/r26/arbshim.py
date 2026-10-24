from flint import arb, ctx
ctx.prec = 256
def mpf(x): return arb(x)
def log(x): return arb(x).log()
def exp(x): return arb(x).exp()
def sqrt(x): return arb(x).sqrt()
def ceil(x): return arb(x).ceil()
class _MP:
    pi = arb.pi()
    @staticmethod
    def nstr(x, n=8): return arb(x).str(n)
mp = _MP()
e = arb.const_e()
