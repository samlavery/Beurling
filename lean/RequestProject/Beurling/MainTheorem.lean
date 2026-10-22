module

public import RequestProject.Beurling.Basic
public import RequestProject.Beurling.ZeroCriterion

/-!
# The main claim of the paper (Theorem A / Corollary 2.2)

There is a discrete Beurling system with `N_P(x) = x + O(x^θ)` for some `θ < 1/2` whose zeta
function (continued to `Re s > θ` by `zetaCont`, see `differentiableAt_zetaCont` and
`zeta_eq_zetaCont`) has zeros with real part arbitrarily close to `1`; i.e. it is zero-free in
no half-plane `Re s > 1 - ε`. This refutes "Question Q" of the paper (with `A = 1`).

Theorem 2.1 of the paper gives `|N_P(x) - x| ≤ C x^θ + 3 x^θ log* x + x^η`, which is
`O(x^{θ'})` for every `θ' ∈ (θ, 1/2)`, so the form below follows from it.

## Structure

The main theorem `exists_no_zeroFree_halfPlane` is **proved** from one remaining input,
`exists_system_near_model`, by the zero criterion `exists_zero_of_near_model` (this is the
final Rouché step, Theorem 4.9 of the paper).

`exists_system_near_model` is **NOT formally proved**. It packages everything the paper proves
before that Rouché step: the construction (Section 3), the lag bound (Proposition 4.1, which
rests on Sections 5–7, Appendix A and the computer certificates of Appendix B), and
Lemmas 4.2–4.8. In the paper, for the `k`-th designed zero the model is `g = Z_B + M_k`, the
centre is `s*_k`, the radius is `1 / log x_k`, `M = 1/4` and `m = 1/16 + o(1)`.
-/

@[expose] public section

open Metric Set

namespace BeurlingSystem

/-- **The paper's construction and Lemmas 4.2–4.8 (unproved input).** There is a discrete
Beurling system with `|N(x) - x| ≤ C x^θ`, `θ < 1/2`, such that for every `ε > 0` there is a
closed disc in `{θ < Re s, 1 - ε < Re s, s ≠ 1}` and a holomorphic model `g` vanishing at its
centre with `‖g‖ ≥ M` and `‖ζ_P - g‖ ≤ m` on the boundary circle, where `2 m < M`.

Not formally proved: this is the content of Sections 3, 5–7, Appendices A–B and
Lemmas 4.2–4.8 of the paper. -/
theorem exists_system_near_model :
    ∃ P : BeurlingSystem, ∃ θ C : ℝ, θ < 1 / 2 ∧
      (∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ) ∧
      ∀ ε > 0, ∃ (c : ℂ) (r m M : ℝ) (g : ℂ → ℂ), 0 < r ∧ 2 * m < M ∧
        closedBall c r ⊆ {s : ℂ | θ < s.re ∧ 1 - ε < s.re ∧ s ≠ 1} ∧
        DifferentiableOn ℂ g (closedBall c r) ∧ g c = 0 ∧
        (∀ z ∈ sphere c r, ‖P.zetaCont z - g z‖ ≤ m) ∧
        (∀ z ∈ sphere c r, M ≤ ‖g z‖) := by
  sorry

/-- **Corollary 2.2 (Theorem A, existence form).** Proved from `exists_system_near_model` by
the zero criterion `exists_zero_of_near_model` (Theorem 4.9 of the paper); the remaining
input `exists_system_near_model` is not formally proved. -/
theorem exists_no_zeroFree_halfPlane :
    ∃ P : BeurlingSystem, ∃ θ C : ℝ, θ < 1 / 2 ∧
      (∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ) ∧
      ∀ ε > 0, ∃ s : ℂ, s ≠ 1 ∧ θ < s.re ∧ 1 - ε < s.re ∧ P.zetaCont s = 0 := by
  obtain ⟨P, θ, C, hθ, hN, hmodel⟩ := exists_system_near_model
  refine ⟨P, θ, C, hθ, hN, fun ε hε => ?_⟩
  obtain ⟨c, r, m, M, g, hr, hmM, hsub, hg, hgc, hfg, hgM⟩ := hmodel ε hε
  have hf : DifferentiableOn ℂ P.zetaCont (closedBall c r) := fun z hz =>
    (P.differentiableAt_zetaCont hN (hsub hz).1 (hsub hz).2.2).differentiableWithinAt
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_near_model hr hf hg hgc hmM hfg hgM
  have hzs := hsub (ball_subset_closedBall hz)
  exact ⟨z, hzs.2.2, hzs.1, hzs.2.1, hz0⟩

end BeurlingSystem

end
