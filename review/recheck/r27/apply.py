import sys
p = sys.argv[1]
s = open(p).read()
R = [
# F1
(r"""\item \emph{$\rhodet$, smooth change:} for $y\in J$ the points $v:=x/n$ and $v':=y/n$ satisfy $|v-v'|\le2\delta v$, and then""",
 r"""\item \emph{$\rhodet$, smooth change:} for $y\in J$ and $x/n\ge X_0$ put $v:=x/n$ and $v':=\max(y/n,X_0)$, so that $|v-v'|\le2\delta v$
  (if $y/n<X_0$, then $T'(x/n)-T'(y/n)=\jz+\rhodet(X_0)-\rhodet(x/n)$, as $R'$ and $\sigma_{\Abs}$ vanish near $X_0$, and $\jz$ is the
  previous item); then"""),
# C1
(r"""  $[v,(1+\kappa)v]$ and $[v',(1+\kappa)v']$ differ by two intervals of length $\le2\delta(1+\kappa)v$, so the counts differ by at most""",
 r"""  $[v,(1+\kappa)v]$ and $[v',(1+\kappa)v']$ overlap (as $2\delta<\kappa$) and differ by two intervals of length $\le2\delta(1+\kappa)v$,
  which enter the difference of the counts with opposite signs; so the counts differ by at most"""),
# C3(a)
(r"""  ($\sum_{v<X_0^{U_0}}\log(2v)\le1.5(U_0\Lambda)^2$) and $1/\kappa\le X_0^{5/12}$, the weighted sum is at most""",
 r"""  ($\sum_{v<X_0^{U_0}}\log(2v)\le1.5(U_0\Lambda)^2$) and $1/\kappa\le X_0^{5/12}$, $\log x$ times this part of $\rhosh(x)-\rhosh(y)$
  is at most"""),
# C2
(r"""\item \emph{Resolvable $R_j'$, smooth change:} the bound is linear in the displacement, which is at most $2\delta$ in relative
  terms, so it is at most $2\delta\gamma_j\kappa_j/(1-\theta)\le2\kappa_j/((1-\theta)\gamma_j\log^4x)$, as $\delta\gamma_j^2\le\log^{-4}x$ for
  resolvable $\gamma_j\le\gamma_*$. This is summable over $j$.""",
 r"""\item \emph{Resolvable $R_j'$, smooth change:} by \eqref{eq:Rk} and \eqref{eq:ampl},
  $|R_j''(w)|\le\alpha_j\gamma_j^2w^{\theta-2}(1+O(1/\gamma_j))$, so at a level with $|v-v'|\le2\delta v$,
  $|R_j'(v)-R_j'(v')|\le1.01\,\delta\gamma_j\kappa_j(v/x_j)^{\theta-1}$. Summed with the weights $\mu^2(n)/n$ over $n\le x/x_j$, this is at
  most $1.01F_\theta\,\delta\gamma_j\kappa_j\le2\delta\gamma_j\kappa_j/(1-\theta)\le2\kappa_j/((1-\theta)\gamma_j\log^4x)$, as $F_\theta\le1.33$
  and $\delta\gamma_j^2\le\log^{-4}x$ for resolvable $\gamma_j\le\gamma_*$. This is summable over $j$."""),
# C3(b)
(r"""\item By Theorem~\ref{thm:lp}(ii), $\Pi(J)=\delta x\,\pi_0(x)(1+O(\delta))+O(Kxe^{-c_{\mathrm{LP}}\sqrt{\log x}})$, where
  $\pi_0(x):=(1-1/x)/\log x$.""",
 r"""\item By Theorem~\ref{thm:lp}(ii), $\Pi(J)=\delta x\,\pi_0(x)(1+\eps_J)+O(Kxe^{-c_{\mathrm{LP}}\sqrt{\log x}})$ with
  $0\le\eps_J\le2.01\,\delta/\log x$, where $\pi_0(x):=(1-1/x)/\log x$ (which decreases, and $J\subset[x(1-2\delta),x]$)."""),
]
for old, new in R:
    c = s.count(old)
    assert c == 1, (c, old[:60])
    s = s.replace(old, new)
open(p, "w").write(s)
print("applied", len(R))
