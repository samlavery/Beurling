import math
LOG2 = math.log(2)
def logsumexp(*a):
    m = max(a); return m + math.log(sum(math.exp(x - m) for x in a))
for Lam in [1e8, 1e9, 1e12]:
    X0log = Lam  # log X0
    # (1) weights: sum over dyadic v in [X0/2, X0^Lam) of log(2v), v = (X0/2) 2^j
    J = math.floor((Lam*Lam - (Lam - LOG2)) / LOG2)
    W = (J + 1) * Lam + LOG2 * J * (J + 1) / 2
    # (2) Rankin tail: sum over dyadic v=2^m with log v >= Lam^2 of log(2v)*30 Lam^1.65 e^{-u/2} / kappa, 1/kappa <= X0^{5/12}
    a = LOG2 / (2 * Lam); M = math.ceil(Lam * Lam / LOG2); r = math.exp(-a)
    # sum_{m>=M} (m+1) log2 r^m = log2 r^M [ (M+1)/(1-r) + r/(1-r)^2 ]
    logtail = math.log(LOG2) - a * M + math.log((M + 1) / (1 - r) + r / (1 - r) ** 2) + math.log(30) + 1.65 * math.log(Lam) + 5 * Lam / 12
    claim2 = math.log(90) + 4.7 * math.log(Lam) - Lam / 12
    # (3) first part: 1.5 Lam^4 (4.0001 delta + 2/X0)/kappa with delta <= X0^{-1/2}
    first = math.log(1.5) + 4 * math.log(Lam) + logsumexp(math.log(4.0001) - Lam / 2, math.log(2) - Lam) + 5 * Lam / 12
    claim1 = math.log(7) + 4 * math.log(Lam) - Lam / 12
    CS = math.log(77)
    total = CS + logsumexp(claim1, claim2)
    print(f"Lam={Lam:.0e}: weights/Lam^4={W/Lam**4:.4f} (<=1.5)  "
          f"tail: log actual={logtail:.3f} log claim={claim2:.3f} ok={logtail<=claim2}  "
          f"first: log actual={first:.3f} log claim={claim1:.3f} ok={first<=claim1}  "
          f"log total={total:.4e}  <=-1e6:{total<=-1e6}  <= -0.08Lam:{total<=-0.08*Lam}  margin={-0.08*Lam-total:.3e}")
    # ratio of tail to 90 Lam^4.7 e^{-Lam/12}
    print("   tail/(Lam^4.65 e^{-Lam/12}) =", math.exp(logtail - (4.65*math.log(Lam) - Lam/12)))
# exact constants
print("1.5*4.0001 =", 1.5*4.0001, " 1.5*2 coefficient on X0^{-7/12} =", 3.0)
# log of bound at Lam=1e8 exactly
Lam = 1e8
print("log bound at 1e8:", math.log(77) + math.log(7*Lam**4 + 90*Lam**4.7) - Lam/12)
# sigma_A item: 4 C_S sum_{L_v>391 Lam^2} log(2v) L_v^{-4}, v dyadic, L_v = log v
Lam = 1e8; L0 = 391 * Lam**2
m0 = math.ceil(L0 / LOG2)
# sum_{m>=m0} (m+1)log2 / (m log2)^4 ~ integral
s = sum(((m + 1) * LOG2) / (m * LOG2) ** 4 for m in range(m0, m0 + 10)) # leading terms check
approx = (1 / LOG2) * (1 / (2 * L0 ** 2) + LOG2 / (3 * L0 ** 3)) + (L0 + LOG2) / L0 ** 4
print("sigma_A item / Lam^-4:", 4 * 77 * approx * Lam ** 4, "(claim <= 1.5e-3)")
print("e^{5.97} =", math.exp(5.97))
