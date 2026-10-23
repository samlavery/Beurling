import math
eg = math.exp(0.5772156649015329)
# (S3)(d): A_top <= A_R e^{2.2/Lambda}, worst at small log z, Lambda = 1e8
Lam = 1e8
for logz in [Lam - math.log(2), Lam, 1e9, 1e20]:
    Atop_over = eg*(logz + 0.7)*math.exp(2.21/Lam)*(1+1e-8)
    AR = 1.8*(logz+4)*math.exp(2.2/Lam)
    assert Atop_over <= AR
print("A_top <= A_R e^{2.2/Lambda}: ok; log(2z+H(2z)) <= log z + 0.7 needs log 2 + H(2z)/(2z) <= 0.7:", math.log(2) < 0.7)

# cor:R-Ecl: exact per-element factor and full chain vs -4 ell, using exact r0 and the paper's relaxed chain
def chk(L):
    l = math.log(L)
    r0 = math.ceil(L/(3*l)) + 3
    theta_etc = 1.01
    fac_exact = math.e*1.8*(L+4)*4*L**-6*(2*L)**1.02*theta_etc
    fac_paper = 15*math.e*L**-3.98
    assert fac_exact <= fac_paper, (L, fac_exact, fac_paper)
    lhs_exact = L + 6*l - math.log(2) + r0*math.log(fac_exact)
    chain = L*(-0.32666 + 1.2361/l) - 5.94*l + 11.13
    return lhs_exact, chain, -4*l
for L in [465, 470, 500, 1000, 1e4, 1e8, 1e12, 1e20]:
    a, b, c = chk(L)
    assert a <= b + 1e-9 and b <= c, (L, a, b, c)
print("cor:R-Ecl chain ok at L in {465,...,1e20}; at L=465: exact %.2f, chain %.2f, target %.2f" % chk(465))

# Lemma reduction (ii) constants at L = 60 and larger
for L in [60, 100, 1e3, 1e8, 1e20]:
    l = math.log(L)
    B = 2.1*L**1.02
    Ch = eg*(L+0.7)*(1+1e-7)
    assert Ch <= 2*L
    Cp = 2*math.e*L*math.e*2*L*B**2   # 2 * eD * e * Ch * B^2 with D<=L, Ch<=2L
    assert Cp <= 131*L**4.04*1.0001 and 131*L**4.04 <= 6*L**5.1, L
    theta = 1 + 1e-8
    assert theta*4*L**-6*6*L**5.1 <= 1
    kap = L/(3*l) + 2
    lam = math.log(2*L)
    assert 1 + kap*lam <= L, (L, 1+kap*lam)
    assert 8*math.e*theta*L**-3 <= 1
print("Lemma reduction(ii) constants ok for L in {60,100,1e3,1e8,1e20}; (1+kappa*lambda)/L at L=60: %.3f" % ((1+(60/(3*math.log(60))+2)*math.log(120))/60))
# (iii): r0*13*L^5.1*z*w^{1+j} <= L^-3 iff (1+j) log(1/w) >= L + log(13 r0) + 8.1 ell ; r0 <= L
for L in [60, 1e3, 1e8]:
    l = math.log(L)
    assert math.log(13) + l + 5.1*l + 3*l <= 10*l + 10 - 0 and math.log(13) <= 2.6
print("criterion (iii) ok")
