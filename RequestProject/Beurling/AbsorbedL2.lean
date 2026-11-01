module

public import RequestProject.Beurling.BoxL2
public import RequestProject.Beurling.FourierMeanSquare

/-!
# The `ρ̄_A` part in the proof of Lemma 4.8(ii)

The `ρ̄_A` part of `D̂_{<a_k}` is `∫_{X₀}^{a_k} x^{-s} ρ̄_A(x) dx`; in the variable `u = log x` it is
`∫_α^β w(u) e^{(1-s)u} du` with `w(u) = ρ̄_A(e^u)`, `α = log X₀`, `β = log a_k`. The paper bounds
its `L²(Q)` norm by Plancherel; here (`box_fourier_part`) the substitute `fourier_mean_square`
gives, for `|w| ≤ c` on `[α, β]`, `0 ≤ α ≤ β`, `Γ ≥ 0` and `(β - α)(Γ + 1/2) ≥ 1`,

  `∬_Q |∫_α^β w(u) e^{(1-s)u} du|² ≤ 4 (1 + log((β - α)(Γ + 1/2))) c² e^{β/2}`,

with `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`. (The paper's bound is `π c² e^{β/2}` without the
logarithm; with `c = 0.1/log X₀`, `e^{β/2} = a_k^{1/2}` and `Γ ≥ a_k^{1-θ}/(2X₀V³)`, either is
`o(Γ X₀^{-3/8})`.)
-/

@[expose] public section

open Complex MeasureTheory Set GoodHeights

namespace GoodHeights

lemma integral_exp_half_le {α β : ℝ} (hαβ : α ≤ β) :
    ∫ u in Icc α β, Real.exp (u / 2) ≤ 2 * Real.exp (β / 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hαβ]
  have := intervalIntegral.integral_comp_div (a := α) (b := β) Real.exp (c := 2) (by norm_num)
  rw [this, integral_exp, smul_eq_mul]
  have := Real.exp_pos (α / 2)
  linarith

lemma measurable_fourier_part {w : ℝ → ℝ} (hw : Measurable w) (α β : ℝ) :
    Measurable fun z : ℂ => ∫ u in Icc α β, (w u : ℂ) * cexp ((1 - z) * u) := by
  set f : ℂ → ℝ → ℂ := fun z u => (w u : ℂ) * cexp ((1 - z) * u)
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Measurable fun q : ℂ × ℝ => (w q.2 : ℂ) :=
      Complex.measurable_ofReal.comp (hw.comp measurable_snd)
    have h2 : Measurable fun q : ℂ × ℝ => cexp ((1 - q.1) * q.2) := by
      apply Continuous.measurable; fun_prop
    exact h1.mul h2
  exact (hfm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Icc α β))).measurable

/-- **The `ρ̄_A` part of Lemma 4.8(ii).** For a measurable `w` with `|w| ≤ c` on `[α, β]`,
`0 ≤ α ≤ β`, `Γ ≥ 0` and `(β - α)(Γ + 1/2) ≥ 1`:
`∬_Q |∫_α^β w(u) e^{(1-s)u} du|² ≤ 4 (1 + log((β - α)(Γ + 1/2))) c² e^{β/2}`. -/
theorem box_fourier_part {w : ℝ → ℝ} (hw : Measurable w) {α β c Γ : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hc : ∀ u ∈ Icc α β, |w u| ≤ c) (hΓ : 0 ≤ Γ)
    (hL : 1 ≤ (β - α) * (Γ + 1 / 2)) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4),
        ENNReal.ofReal (‖∫ u in Icc α β, (w u : ℂ) * cexp ((1 - z) * u)‖ ^ 2) ≤
      ENNReal.ofReal (4 * (1 + Real.log ((β - α) * (Γ + 1 / 2))) * c ^ 2 *
        Real.exp (β / 2)) := by
  set μ : Measure ℝ := volume.restrict (Icc α β)
  set T := Γ + 1 / 2 with hTdef
  have hT : 0 < T := by positivity
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc α ⟨le_rfl, hαβ⟩)
  have hlog : 0 ≤ Real.log ((β - α) * T) := Real.log_nonneg hL
  set f : ℂ → ℝ → ℂ := fun z u => (w u : ℂ) * cexp ((1 - z) * u)
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Measurable fun q : ℂ × ℝ => (w q.2 : ℂ) :=
      Complex.measurable_ofReal.comp (hw.comp measurable_snd)
    have h2 : Measurable fun q : ℂ × ℝ => cexp ((1 - q.1) * q.2) := by
      apply Continuous.measurable; fun_prop
    exact h1.mul h2
  have hIm : Measurable fun z : ℂ => ∫ u, f z u ∂μ :=
    (hfm.stronglyMeasurable.integral_prod_right (ν := μ)).measurable
  have hF : Measurable fun z : ℂ => ENNReal.ofReal (‖∫ u, f z u ∂μ‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hIm.norm.pow_const 2)
  rw [lintegral_box_eq hF]
  set B := (4 + 4 * Real.log ((β - α) * T)) * (c ^ 2 * (2 * Real.exp (β / 2)))
  have hB : 0 ≤ B := by positivity
  have hinner : ∀ σ ∈ Icc (3 / 4 : ℝ) (5 / 4), ∫⁻ t in Icc (Γ - 1 / 4) (2 * Γ + 1 / 4),
      ENNReal.ofReal (‖∫ u, f ((σ : ℂ) + t * I) u ∂μ‖ ^ 2) ≤ ENNReal.ofReal B := by
    intro σ hσ
    set G : ℝ → ℂ := fun u => ((w u * Real.exp ((1 - σ) * u) : ℝ) : ℂ)
    have hGm : Measurable G := by
      apply Complex.measurable_ofReal.comp
      exact hw.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
    have hfG : ∀ t u : ℝ, f ((σ : ℂ) + t * I) u = G u * cexp (-(I * t * u)) := by
      intro t u
      simp only [f, G]
      push_cast
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; ring
    have hGb : ∀ u ∈ Icc α β, ‖G u‖ ≤ c * Real.exp (β / 4) := by
      intro u hu
      simp only [G, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      apply mul_le_mul (hc u hu) _ (Real.exp_pos _).le hc0
      apply Real.exp_le_exp.mpr
      have := hu.1; have := hu.2
      nlinarith [hσ.1]
    have hGsq : ∫ u, ‖G u‖ ^ 2 ∂μ ≤ c ^ 2 * (2 * Real.exp (β / 2)) := by
      have hb : ∀ u ∈ Icc α β, ‖G u‖ ^ 2 ≤ c ^ 2 * Real.exp (u / 2) := by
        intro u hu
        simp only [G, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp, mul_pow]
        apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hc u hu) 2) _ (by positivity)
          (sq_nonneg _)
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have := hu.1
        push_cast; nlinarith [hσ.1]
      calc ∫ u, ‖G u‖ ^ 2 ∂μ ≤ ∫ u in Icc α β, c ^ 2 * Real.exp (u / 2) := by
            apply setIntegral_mono_on _ _ measurableSet_Icc hb
            · exact Integrable.mono' (integrable_const ((c * Real.exp (β / 4)) ^ 2))
                (hGm.norm.pow_const 2).aestronglyMeasurable
                ((ae_restrict_mem measurableSet_Icc).mono fun u hu => by
                  rw [Real.norm_of_nonneg (sq_nonneg _)]
                  exact pow_le_pow_left₀ (norm_nonneg _) (hGb u hu) 2)
            · exact (Continuous.integrableOn_Icc (by fun_prop))
        _ = c ^ 2 * ∫ u in Icc α β, Real.exp (u / 2) := integral_const_mul _ _
        _ ≤ c ^ 2 * (2 * Real.exp (β / 2)) :=
            mul_le_mul_of_nonneg_left (integral_exp_half_le hαβ) (sq_nonneg _)
    have hfms := FourierMS.fourier_mean_square hGm hαβ hGb hT hL (Γ - 1 / 4)
    rw [show Γ - 1 / 4 + T = 2 * Γ + 1 / 4 by rw [hTdef]; ring] at hfms
    have heq : ∀ t : ℝ, ‖∫ u, f ((σ : ℂ) + t * I) u ∂μ‖ ^ 2 =
        ‖∫ u in Icc α β, G u * cexp (-(I * t * u))‖ ^ 2 := by
      intro t; simp only [hfG]; rfl
    simp only [heq]
    have hmeas : Measurable fun t : ℝ => ‖∫ u in Icc α β, G u * cexp (-(I * t * u))‖ ^ 2 := by
      have : Measurable fun t : ℝ => ∫ u, f ((σ : ℂ) + t * I) u ∂μ :=
        hIm.comp (by fun_prop)
      simp only [hfG] at this
      exact this.norm.pow_const 2
    have hbdd : ∀ t : ℝ, ‖∫ u in Icc α β, G u * cexp (-(I * t * u))‖ ^ 2 ≤
        (c * Real.exp (β / 4) * (β - α)) ^ 2 := by
      intro t
      apply pow_le_pow_left₀ (norm_nonneg _)
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc α β)
        (f := fun u => G u * cexp (-(I * t * u))) (C := c * Real.exp (β / 4)) measure_Icc_lt_top
        (fun u hu => by
          rw [norm_mul, FourierMS.norm_cexp_neg_I_mul, mul_one]; exact hGb u hu)
      rwa [Real.volume_real_Icc_of_le hαβ] at this
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · apply ENNReal.ofReal_le_ofReal
      refine hfms.trans ?_
      exact mul_le_mul_of_nonneg_left hGsq (by positivity)
    · exact Integrable.mono' (integrable_const _) hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbdd t)
    · exact Filter.Eventually.of_forall fun t => sq_nonneg _
  calc ∫⁻ σ in Icc (3 / 4 : ℝ) (5 / 4), ∫⁻ t in Icc (Γ - 1 / 4) (2 * Γ + 1 / 4),
        ENNReal.ofReal (‖∫ u, f ((σ : ℂ) + t * I) u ∂μ‖ ^ 2)
      ≤ ∫⁻ σ in Icc (3 / 4 : ℝ) (5 / 4), ENNReal.ofReal B :=
        setLIntegral_mono' measurableSet_Icc hinner
    _ = ENNReal.ofReal (1 / 2 * B) := by
        rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hB]
        congr 1; ring
    _ = _ := by congr 1; simp only [B]; ring

end GoodHeights

end
