# Range of L for which cor:R-Ecl survives the crossing loss of the union-reading PIL.
# Inequality (paper): log(2z/delta * RHS) <= L + 6 ell + r0*log(per-element) <= -4 ell, with per-element
#   theta*A_R*delta*e^{(3H+2)/X0}*(1+r0/X0)^{1.02}*e^{2.2/Lambda},  A_R=1.8(L+4), delta=4L^-6, theta e^.. <= 1.01.
# Loss options per element:  E2 (crude): (1/k) * sum_{t<k} log(1+t*lam) <= ((1+k lam)log(1+k lam)-k lam)/(k lam)
#   E1 (excess charging): replace 1.02*log(1+k/X0)+(3H+2)/X0 by B(1+2B/X0)*(same), B=1+(k-1)lam; needs B<X0/2.
# Everything is divided by L (L may be astronomically large); L=e^ell. H(X0)/X0 <= e^{-0.98 Lambda} is dropped.
import math
def check(ell,Lam,mode):
    L=math.exp(ell) if ell<700 else float('inf')
    # k/L and log terms via ell only
    kL=1/(3*ell)                         # r0/L (the +4 is negligible for the scan; added below when L finite)
    k_log=ell-math.log(3*ell)            # log r0
    if L!=float('inf'): k=L/(3*ell)+4; kL=k/L; k_log=math.log(k)
    lam=math.log(1+ (math.exp(ell-math.log(Lam)) if ell<700 else 0)) if ell<700 else ell-math.log(Lam)
    lam=max(lam,1e-9)+2.2/Lam
    # log(1+k/X0)
    x=k_log-Lam
    l1p=math.log1p(math.exp(x)) if x<30 else x
    base=math.log(1.01)+math.log(1.8)+ (math.log(L+4) if L!=float('inf') else ell)+math.log(4)-6*ell
    if mode=='none': extra=0.0; pat=1.02*l1p
    elif mode=='E2':
        klam_log=k_log+math.log(lam)
        if klam_log<30:
            kl=math.exp(klam_log); extra=((1+kl)*math.log1p(kl)-kl)/kl
        else: extra=klam_log-1+klam_log*math.exp(-klam_log)
        pat=1.02*l1p
    else:
        Blog=math.log(1+math.exp(k_log+math.log(lam))) if k_log<700 else k_log+math.log(lam)
        if Blog>Lam-math.log(2): return None
        B=math.exp(Blog-Lam)               # B/X0
        a1=math.log(1.02)+(math.log(l1p) if x>-30 else x); a2=math.log(2)-Lam
        m=max(a1,a2); lse=m+math.log(math.exp(a1-m)+math.exp(a2-m))
        pl=Blog+math.log1p(2*B)+lse
        if pl>700: return 1.0
        pat=math.exp(pl)
        extra=0.0
    per=base+pat+extra
    # f = [L + 6 ell + r0*per + 4 ell]/L
    f=1+kL*per+(10*ell/L if L!=float('inf') else 0)
    return f
def main():
  for Lam in (1e8,1e9):
    for mode in ('none','E1','E2'):
        ok=[];
        ells=[math.log(465)]+[x*Lam/100 for x in range(1,10001)]
        last=None; first_fail=None
        for e in ells:
            f=check(e,Lam,mode)
            good=(f is not None and f<=0)
            if good: last=e
            elif first_fail is None and e>math.log(465): first_fail=e
        print(f"Lambda={Lam:.0e} mode={mode}: first failure at ell/Lambda={None if first_fail is None else first_fail/Lam:.4g}, last ok ell/Lambda={last/Lam:.4g}")
