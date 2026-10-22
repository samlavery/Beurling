# arb (python-flint) backend with the same interface as the binary64 interval class in bs_cert.py.
# Every enclosure is an arb ball; float conversions are rounded outward (nextafter) and are used only for
# table lookups (r_low/r_up) and reporting. Positivity tests use the outward float of the arb upper bound.
import math
from flint import arb
def _fdn(a): return math.nextafter(float(a), -math.inf)
def _fup(a): return math.nextafter(float(a), math.inf)
class I:
    __slots__ = ("b",)
    def __init__(s, lo, hi=None):
        if isinstance(lo, I): s.b = lo.b; return
        if isinstance(lo, arb) and hi is None: s.b = lo; return
        a = lo if isinstance(lo, arb) else arb(lo)
        s.b = a if hi is None else arb.union(a, hi if isinstance(hi, arb) else arb(hi))
    @staticmethod
    def _c(o): return o.b if isinstance(o, I) else (o if isinstance(o, arb) else arb(o))
    def __add__(s, o): return I(s.b + I._c(o))
    __radd__ = __add__
    def __neg__(s): return I(-s.b)
    def __sub__(s, o): return I(s.b - I._c(o))
    def __rsub__(s, o): return I(I._c(o) - s.b)
    def __mul__(s, o): return I(s.b * I._c(o))
    __rmul__ = __mul__
    def __truediv__(s, o):
        d = I._c(o); assert d > 0 or d < 0, "division by ball containing 0"; return I(s.b / d)
    def __rtruediv__(s, o):
        assert s.b > 0 or s.b < 0, "division by ball containing 0"; return I(I._c(o) / s.b)
    @property
    def lo(s): return _fdn(s.b.lower())
    @property
    def hi(s): return _fup(s.b.upper())
    def __repr__(s): return f"[{s.lo:.6g},{s.hi:.6g}]"
def _b(x): return x.b if isinstance(x, I) else arb(x)
def iexp(x): return I(_b(x).exp())
def iexpm1(x): return I(_b(x).expm1())
def ilog(x): return I(_b(x).log())
def isqrt(x): return I(_b(x).sqrt())
def ipos(x): return I(_b(x).nonnegative_part())
def isq(x):
    b = _b(x)
    if b >= 0 or b <= 0: return I((b * b).nonnegative_part())
    a = abs(b); return I((a * a).nonnegative_part())
def lo_(x): return x.lo if isinstance(x, I) else x
def hi_(x): return x.hi if isinstance(x, I) else x
def aexp_up(x):  # float upper bound of exp(x) for an arb/I/float x
    return _fup(_b(x).exp().upper())
