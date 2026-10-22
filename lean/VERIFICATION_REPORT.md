# Verification report: "Discrete Beurling number systems with integer error O(x^θ), θ < 1/2, whose zeta function has no zero-free half-plane" (S. Lavery, draft of 22 Oct 2026)

## Bottom line

The paper's main result (Theorem 2.1 / Corollary 2.2) is **not** formally verified. The proof
runs to about 100 pages: a randomised greedy construction, a martingale/queue analysis
(Sections 5–6, Appendix A) and several computer-assisted certificates (Appendix B). Formalizing
all of that in Lean is far beyond a single session. What was done instead:

1. The **exact claim** is now a precise Lean statement, so it is clear what would have to be
   proved. It is recorded with `sorry`.
2. The **analytic setup** the claim depends on is formalized and **proved**: the definitions of
   `N_P` and `ζ_P`, and the partial-summation continuation of `ζ_P` past `Re s = 1`.
3. Several **self-contained steps** of the paper are machine-checked.
4. Sections 2–4 and parts of Section 6 were **read by hand** (not formally). No error was found
   in the parts read; details below.

All Lean files build. Apart from the main theorem, which is deliberately left as `sorry`, they
use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Lean files

| File | Contents | Status |
|---|---|---|
| `RequestProject/Beurling/Defs.lean` | `BeurlingSystem` (non-decreasing `p j > 1`, `p j → ∞`), the value of an exponent vector, `N` (counted with multiplicity), `zeta` (Dirichlet series), `zetaCont` (\( \tfrac{s}{s-1} + s\int_1^\infty (N(x)-x)x^{-s-1}\,dx \)) | definitions |
| `RequestProject/Beurling/Basic.lean` | `finite_le`, `differentiableAt_zetaCont`, `zeta_eq_zetaCont` | proved |
| `RequestProject/Beurling/ZeroCriterion.lean` | `exists_zero_of_near_model` (Rouché-type zero criterion, the tool of Theorem 4.9) | proved |
| `RequestProject/Beurling/MainTheorem.lean` | `exists_no_zeroFree_halfPlane` (Corollary 2.2), proved from `exists_system_near_model` | **conditional: `exists_system_near_model` is `sorry`** |
| `RequestProject/Beurling/Checks.lean` | `re_Phi_ge`, `zeta2_pow4_div_zeta4_le`, `prop41_numeric`, `eta_ge` | proved |

### The main statement (unproved)

```lean
theorem exists_no_zeroFree_halfPlane :
    ∃ P : BeurlingSystem, ∃ θ C : ℝ, θ < 1 / 2 ∧
      (∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ) ∧
      ∀ ε > 0, ∃ s : ℂ, s ≠ 1 ∧ θ < s.re ∧ 1 - ε < s.re ∧ P.zetaCont s = 0
```

Theorem 2.1(i) of the paper gives \( |N(x)-x| \le C x^\theta + 3x^\theta\log^* x + x^\eta \).
That is \( O(x^{\theta'}) \) for every \( \theta' \in (\theta, 1/2) \), so the form above is what
the paper claims.

### Why `zetaCont` is the right zeta function (proved)

* `zeta_eq_zetaCont`: if \( |N(x)-x| \le Cx^\theta \) with \( \theta\le 1 \), then for
  \( \operatorname{Re}s>1 \) the Dirichlet series \( \sum_n n^{-s} \), summed over all exponent
  vectors, equals `zetaCont s`.
* `differentiableAt_zetaCont`: under the same bound, `zetaCont` is holomorphic at every \( s \)
  with \( \operatorname{Re}s>\theta \), \( s\ne1 \).

So `zetaCont` is the analytic continuation of \( \zeta_P \) to \( \operatorname{Re}s>\theta \),
and "no zero-free half-plane" is stated for that continuation. This is the meromorphic-continuation
part of Remark 1.2.

### Paper steps that were machine-checked

* **§4.2, bullet 2:** \( \operatorname{Re}\Phi(w)\ge e^{-1}\cos 1 \) for
  \( 0\le\operatorname{Re}w\le1 \), \( |\operatorname{Im}w|\le1 \), for any density
  \( \varphi'\ge0 \) on \([0,1]\) with total mass 1.
* **Lemma 4.8(i):** \( \zeta(2)^4/\zeta(4) = 5\pi^4/72 \le 6.8 \), and the Paley–Zygmund
  density \( (1/4)/6.8 > 0.036 \).
* **Proposition 4.1:** \( 8(\log L)^2 + 10^{-6}L + 2 \le 2.82\cdot10^{-5}L \) for all
  \( L\ge 10^8-1 \). Also \( \eta=\min(\theta,1/2-\theta)/2 \ge 5\cdot10^{-5} > 2.82\cdot10^{-5} \)
  for \( \theta\in[1/4,\,1/2-10^{-4}] \). This is the step where \( \theta\le\theta_1 \) is used.
  The margin is tight: at \( L = 10^8 \) the left side is about \( 2.817\cdot10^{-5}L \).

## Informal reading (not machine-checked)

These checks were done by hand. They are **not** formal verification.

* **§3 (construction), Lemmas 3.3–3.7, Corollary 3.8:** the positivity margin
  \( 0.99-0.1-0.8 = 0.09 \), \( 1/(\kappa u)\le X_0^{-7/12} \), the causality argument (every prime
  factor of a composite is at most \( n/2 \)) and the Lindley recursion all check out. The
  windows \( [u,(1+\kappa)u] \) are long enough for Heath-Brown's short-interval PNT, since
  \( \kappa = X_0^{-5/12+2\varepsilon} \).
* **§4 (zeros):** the Mellin formula (15) for \( \hat R_k \) was re-derived. So was the zero
  location \( 1-\operatorname{Re}\rho_k\approx 3\log\log x_k/\log x_k \), which comes from
  balancing \( \alpha_k\gamma_k x_k^{\theta-\sigma}\asymp 1 \) using the amplitude condition (2).
  Also checked: the bound (16), the Paley–Zygmund density, and the density bookkeeping in
  Lemma 4.8 (\( 0.036 - 0.018 \)). The Rouché constant holds: \( \min_{|\xi|=1}|1-e^{-\xi}| = 1-e^{-1} \),
  attained at \( \xi=1 \), so \( |Z_B+M_k|\ge\tfrac12(1-e^{-1})>\tfrac14 \). The mean-square
  exponent \( \theta+\eta-1/2<0 \) holds because \( \eta\le(1/2-\theta)/2 \).
  A simple pointwise bound on \( \hat D(s) \) at height \( \gamma_k \) would be far too large.
  The paper avoids this by choosing \( \gamma_k \) by a mean-value argument (Lemma 4.8(ii)),
  which looks sound in outline.
* **Consistency with known results:** the zeros satisfy
  \( 1-\operatorname{Re}\rho_k \asymp 3(1-\theta)\log\log\gamma_k/\log\gamma_k \). That lies
  outside Landau's zero-free region \( 1-c(1-\theta)/\log|t| \), so there is no conflict. Since
  \( \alpha=1 \), Hilberdink's \( \max(\alpha,\beta)\ge 1/2 \) is also respected.
* **§6.3 (Theorem 6.6):** the constants in (70) and (71) were rechecked, and they are consistent:
  \( \sqrt{768}\approx27.71 \), \( 48-27.72=20.28 \), \( 20.28/0.15\approx135 \), the maximiser
  \( b/(4a) = 4M_1L^2/c' \), and the union bound \( \lesssim 30L L_0^2 x^{-3}\le x^{-2} \).
  The probability budget in Lemma 6.9 is also consistent:
  \( \sum_m(\Lambda+m\log2)^{-2}\approx 1.443/\Lambda \le 1.5/\Lambda \).
* **Not checked:** most of Section 5 (the noise response, the Beurling–Saias resolvent bound
  and the local PNT for the realised system), Sections 6.4–6.9, Appendix A (rank-full
  configurations) and the computer certificates of Appendix B. Together these carry the
  positive-drift and queue-bound arguments, which are the heart of the paper. As the paper itself
  says (Appendix C), none of it has yet been reviewed by a human expert.

## Possible next steps

* Formalize Remark 1.2 in full, i.e. that (b) implies (a).
* Formalize the "zeros reduce to the lag bound" argument of Section 4 as a conditional theorem:
  assume the lag bound (11) and the target structure, and derive the zeros by Rouché.
* Have a specialist in Beurling systems and probabilistic number theory review Sections 5–6 and
  Appendix A.

## Follow-up: the main theorem

The main theorem `exists_no_zeroFree_halfPlane` is now derived in Lean from one unproved
input, `exists_system_near_model`. The derivation is the final Rouché step of the paper
(Theorem 4.9). It uses a zero criterion proved from the maximum modulus principle
(`exists_zero_of_near_model`): if a model `g` vanishes at the centre of a disc, `|g| ≥ M` on the
boundary circle, `|ζ_P - g| ≤ m` there, and `2m < M`, then `ζ_P` has a zero in the disc. The
paper's constants fit this criterion: `|Z_B + M_k| ≥ 1/4` on the circle and a perturbation of at most `1/16 + o(1) < 1/8`.

`exists_system_near_model` is still unproved. It contains everything the paper proves before
the Rouché step: the construction, the lag bound (Sections 5–7, Appendices A–B) and
Lemmas 4.2–4.8. That material depends on, among other things, the Huxley–Heath-Brown
short-interval prime number theorem and the Montgomery–Vaughan mean value theorem, neither of
which is in Mathlib, and on computer certificates. So the main theorem is **not** formally verified.
