module

public import RequestProject.Beurling.ZinfMoments
public import RequestProject.Beurling.Lemma48

/-!
# Lemma 4.8 for the concrete base factor

Combining `ZMoments.lemma_4_8_i` (the density bound of Lemma 4.8(i), now proved for the concrete
`Z_B = ZBcont X₀ κ`) with `GoodHeights.lemma_4_8`, the conclusion of Lemma 4.8 follows from its
single remaining analytic input, the `L²` bound of part (ii) on `f = D̂_{<a_k}`.
-/

@[expose] public section

open Complex Metric Set MeasureTheory

namespace GoodHeights

lemma twentyfour_le_of_exp_le {X₀ : ℕ} (hX : Real.exp 50 ≤ X₀) : 24 ≤ X₀ := by
  have h1 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
  have : (24 : ℝ) ≤ X₀ := by linarith
  exact_mod_cast this

/-- **Lemma 4.8 (Good heights exist)** for the concrete base factor: if `X₀ ≥ e^{50}`,
`0 < κ ≤ 1`, `κΓ ≥ e^{X₀²/3}`, and the entire function `f` satisfies the `L²` bound of part (ii),
then the set `S_k` of `γ ∈ [Γ, 2Γ]` with `|Z_B(1+iγ)| ≥ 0.6` and `|f| ≤ 1/16` on
`|s - (1+iγ)| ≤ 1/8` has measure at least `0.018 Γ`. -/
theorem lemma_4_8_ZB {X₀ : ℕ} (hX : Real.exp 50 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hii : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (144 * (X₀ : ℝ) ^ (-(3 / 8 : ℝ)) * Γ)) :
    ENNReal.ofReal (0.018 * Γ) ≤ volume {γ ∈ Icc Γ (2 * Γ) |
      0.6 ≤ ‖BaseFactor.ZBcont X₀ κ (1 + γ * I)‖ ∧
        ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  exact lemma_4_8 hf hΓ0 hX (ZMoments.lemma_4_8_i (twentyfour_le_of_exp_le hX) hκ hκ1 hΓ) hii

/-- A good height exists (`S_k ≠ ∅`), for the concrete base factor. -/
theorem lemma_4_8_ZB_exists {X₀ : ℕ} (hX : Real.exp 50 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hii : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (144 * (X₀ : ℝ) ^ (-(3 / 8 : ℝ)) * Γ)) :
    ∃ γ ∈ Icc Γ (2 * Γ), 0.6 ≤ ‖BaseFactor.ZBcont X₀ κ (1 + γ * I)‖ ∧
      ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16 := by
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  exact lemma_4_8_exists hf hΓ0 hX (ZMoments.lemma_4_8_i (twentyfour_le_of_exp_le hX) hκ hκ1 hΓ)
    hii

end GoodHeights

end
