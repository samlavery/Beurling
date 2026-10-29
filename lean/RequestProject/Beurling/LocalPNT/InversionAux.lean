module

public import Mathlib

/-!
# Contour shifts for vertical line integrals

Auxiliary contour-integration tools for Steps 9–10 of the proof of Theorem 5.24
(paper, `04e-lp.tex`).

* `integral_rect_shift_left`: Cauchy's theorem on the rectangle `[c', c] × [-T, T]`, rewritten as
  "the vertical integral on `Re s = c` equals the one on `Re s = c'` plus the horizontal sides".
* `integral_vertical_eq_zero`: a vertical line integral of a function holomorphic on a right
  half-plane and decaying like `B(σ)/(1 + t²)` with `B(σ) → 0` vanishes (shift to `σ = +∞`).
-/

@[expose] public section

open Set Real MeasureTheory Complex Filter Topology intervalIntegral
open scoped Interval

namespace LocalPNT

/-- **Shifting a truncated vertical integral to the left.** If `F` is holomorphic on the closed
rectangle `[c', c] × [-T, T]`, then
`∫_{-T}^{T} F(c + it) dt = ∫_{-T}^{T} F(c' + it) dt + I⁻¹ (∫_{c'}^{c} F(σ + iT) dσ
- ∫_{c'}^{c} F(σ - iT) dσ)`. -/
theorem integral_rect_shift_left {F : ℂ → ℂ} {c c' T : ℝ}
    (hF : DifferentiableOn ℂ F ([[c', c]] ×ℂ [[-T, T]])) :
    ∫ t in -T..T, F (c + t * I) =
      (∫ t in -T..T, F (c' + t * I)) +
        I⁻¹ * ((∫ σ in c'..c, F (σ + T * I)) - ∫ σ in c'..c, F (σ - T * I)) := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn F ⟨c', -T⟩ ⟨c, T⟩ hF
  simp only [smul_eq_mul, ofReal_neg, neg_mul, ← sub_eq_add_neg] at h
  rw [inv_I]
  linear_combination (-I) * h +
    ((∫ t in -T..T, F (c + t * I)) - ∫ t in -T..T, F (c' + t * I)) * I_sq

/-- The same identity with the sides of the rectangle `[c', c] × [-T, T]` written out as in
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (bottom − top + I·right − I·left). -/
theorem integral_rect_boundary_eq_zero {F : ℂ → ℂ} {c c' T : ℝ}
    (hF : DifferentiableOn ℂ F ([[c', c]] ×ℂ [[-T, T]])) :
    (∫ σ in c'..c, F (σ - T * I)) - (∫ σ in c'..c, F (σ + T * I)) +
      I * (∫ t in -T..T, F (c + t * I)) - I * (∫ t in -T..T, F (c' + t * I)) = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn F ⟨c', -T⟩ ⟨c, T⟩ hF
  simpa only [smul_eq_mul, ofReal_neg, neg_mul, ← sub_eq_add_neg] using h

/-- A function on the vertical line `Re s = σ` bounded by `B/(1 + t²)` is integrable there,
with integral of norm at most `π B`. -/
theorem integrable_vertical_of_bound {F : ℂ → ℂ} {σ B : ℝ}
    (hF : Continuous fun t : ℝ => F (σ + t * I)) (hB : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ B / (1 + t ^ 2)) :
    Integrable (fun t : ℝ => F (σ + t * I)) := by
  refine (integrable_inv_one_add_sq.const_mul B).mono' hF.aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa [div_eq_mul_inv] using hB t

theorem norm_integral_vertical_le {F : ℂ → ℂ} {σ B : ℝ}
    (hB : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ B / (1 + t ^ 2)) :
    ‖∫ t : ℝ, F (σ + t * I)‖ ≤ π * B := by
  calc ‖∫ t : ℝ, F (σ + t * I)‖ ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul B)
          (Eventually.of_forall fun t => by simpa [div_eq_mul_inv] using hB t)
    _ = π * B := by rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq, mul_comm]

/-- **Shifting a vertical line integral to `+∞`.** If `F` is holomorphic on `Re s > c₀` and
`‖F(σ + it)‖ ≤ B(σ)/(1 + t²)` for `σ ≥ c > c₀`, with `B` bounded and `B(σ) → 0`, then
`∫ F(c + it) dt = 0`. -/
theorem integral_vertical_eq_zero {F : ℂ → ℂ} {c c₀ : ℝ} (hc : c₀ < c)
    (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re}) {B : ℝ → ℝ} {C : ℝ}
    (hB : ∀ σ ≥ c, ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ B σ / (1 + t ^ 2))
    (hBC : ∀ σ ≥ c, B σ ≤ C) (hB0 : Tendsto B atTop (𝓝 0)) :
    ∫ t : ℝ, F (c + t * I) = 0 := by
  have hcont : ∀ σ, c₀ < σ → Continuous fun t : ℝ => F (σ + t * I) := fun σ hσ =>
    hF.continuousOn.comp_continuous (by fun_prop) fun t => by simpa using hσ
  have hint : ∀ σ ≥ c, Integrable (fun t : ℝ => F (σ + t * I)) := fun σ hσ =>
    integrable_vertical_of_bound (hcont σ (hc.trans_le hσ)) (hB σ hσ)
  -- the vertical integrals at `σ = X ≥ c` and `σ = c` agree
  have hshift : ∀ X ≥ c, ∫ t : ℝ, F (X + t * I) = ∫ t : ℝ, F (c + t * I) := by
    intro X hX
    have hrect : ∀ T : ℝ, (∫ t in -T..T, F (X + t * I)) - ∫ t in -T..T, F (c + t * I) =
        I⁻¹ * ((∫ σ in c..X, F (σ + T * I)) - ∫ σ in c..X, F (σ - T * I)) := by
      intro T
      have hd : DifferentiableOn ℂ F ([[c, X]] ×ℂ [[-T, T]]) := hF.mono fun z hz => by
        have := hz.1
        rw [mem_preimage, uIcc_of_le hX] at this
        exact hc.trans_le this.1
      rw [integral_rect_shift_left hd]
      ring
    have hlim1 : Tendsto (fun T : ℝ => (∫ t in -T..T, F (X + t * I)) -
        ∫ t in -T..T, F (c + t * I)) atTop
        (𝓝 ((∫ t : ℝ, F (X + t * I)) - ∫ t : ℝ, F (c + t * I))) :=
      (intervalIntegral_tendsto_integral (hint X hX) tendsto_neg_atTop_atBot tendsto_id).sub
        (intervalIntegral_tendsto_integral (hint c le_rfl) tendsto_neg_atTop_atBot tendsto_id)
    -- the horizontal sides are `O((X - c)/(1 + T²))`
    have hhor : ∀ T : ℝ, ∀ s : ℝ, s = T ∨ s = -T →
        ‖∫ σ in c..X, F (σ + s * I)‖ ≤ C * (1 + T ^ 2)⁻¹ * |X - c| := by
      intro T s hs
      refine norm_integral_le_of_norm_le_const fun σ hσ => ?_
      rw [uIoc_of_le hX] at hσ
      have hσc : σ ≥ c := hσ.1.le
      calc ‖F (σ + s * I)‖ ≤ B σ / (1 + s ^ 2) := hB σ hσc s
        _ ≤ C / (1 + s ^ 2) := by gcongr; exact hBC σ hσc
        _ = C * (1 + T ^ 2)⁻¹ := by rcases hs with rfl | rfl <;> simp [div_eq_mul_inv]
    have hlim0 : Tendsto (fun T : ℝ => C * (1 + T ^ 2)⁻¹ * |X - c|) atTop (𝓝 0) := by
      have : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp <| tendsto_atTop_add_const_left _ _ <|
          tendsto_pow_atTop two_ne_zero
      simpa using (this.const_mul C).mul_const |X - c|
    have hlim2 : Tendsto (fun T : ℝ => (∫ t in -T..T, F (X + t * I)) -
        ∫ t in -T..T, F (c + t * I)) atTop (𝓝 0) := by
      simp_rw [hrect]
      rw [← mul_zero I⁻¹]
      refine Tendsto.const_mul _ ?_
      rw [← sub_zero (0 : ℂ)]
      refine Tendsto.sub ?_ ?_ <;> refine squeeze_zero_norm (fun T => ?_) hlim0
      · exact hhor T T (Or.inl rfl)
      · simpa [sub_eq_add_neg] using hhor T (-T) (Or.inr rfl)
    exact sub_eq_zero.mp (tendsto_nhds_unique hlim1 hlim2)
  -- and the former is at most `π B(X) → 0`
  refine norm_le_zero_iff.mp <| ge_of_tendsto (by simpa using hB0.const_mul π) ?_
  filter_upwards [eventually_ge_atTop c] with X hX
  rw [← hshift X hX]
  exact norm_integral_vertical_le (hB X hX)

end LocalPNT

end
