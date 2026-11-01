module

public import RequestProject.Beurling.Noise.KRTrueTV
public import RequestProject.Beurling.Noise.KRVarStep

/-!
# The step on densities (§5.9.4)

For the true kernels of Proposition 5.18 the scalar filter is evaluated at the actual centre
`v/w` of each window, so it is a function of the position `v` and not a constant. The kernels
`C_n`, `n ≥ 2`, are absolutely continuous (each is a mixture of windows), so we represent them by
their densities. A measure `f(v) dv` is sent by the step to

  `Qd H w f (t) = ∫ f(v) k(t; v/w) dv`,   `k(t; c) = H(c)⁻¹ 1[c - H(c)/2 ≤ t < c + H(c)/2]`,

the density of `∫ bx_{H(v/w)}(· - v/w) f(v) dv` (`kd` is the density of the half-open box of
§5.1). Main facts:

* `cdf_kd` : the distribution function of `k(·; c)` is the box ramp, `= Kv H w t (c w)`;
* `lintegral_Qd_le` : `∫ |Qd f| ≤ ∫ |f|` (the windows are probabilities; this is (K5) together
  with the mass of the box);
* `cdf_Qd` : `cdf (Qd H w f) = Qv H w (cdf f)`: on densities the step `Qv` of `KRVarStep.lean`
  (the variable-width step in distribution-function form) is `Qd`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace KR

variable {H : ℝ → ℝ}

/-- The density of the box `bx_{H(c)}(· - c)` (half-open, §5.1). -/
noncomputable def kd (H : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (H c)⁻¹ * (Ico (c - H c / 2) (c + H c / 2)).indicator (fun _ => (1 : ℝ)) t

/-- The step on densities: `Qd H w f (t) = ∫ f(v) k(t; v/w) dv`. -/
noncomputable def Qd (H : ℝ → ℝ) (w : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ v, f v * kd H (v / w) t

lemma kd_nonneg (hH : WidthReg H) (c t : ℝ) : 0 ≤ kd H c t := by
  unfold kd
  have := hH.pos c
  apply mul_nonneg (inv_pos.mpr this).le
  unfold Set.indicator; split_ifs <;> norm_num

lemma kd_le (hH : WidthReg H) (c t : ℝ) : kd H c t ≤ (H c)⁻¹ := by
  unfold kd
  have := hH.pos c
  have h1 : (Ico (c - H c / 2) (c + H c / 2)).indicator (fun _ => (1 : ℝ)) t ≤ 1 := by
    unfold Set.indicator; split_ifs <;> norm_num
  calc (H c)⁻¹ * _ ≤ (H c)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr this).le
    _ = (H c)⁻¹ := mul_one _

/-- In its window, `H(c) ≥ (2/3) H(t)` (`H` is `1`-Lipschitz), so `k(t; c) ≤ (3/2) H(t)⁻¹`. -/
lemma kd_le_window (hH : WidthReg H) (c t : ℝ) : kd H c t ≤ 3 / 2 * (H t)⁻¹ := by
  have hc := hH.pos c
  have ht := hH.pos t
  unfold kd Set.indicator
  split_ifs with h
  · rw [mul_one]
    have h1 : |t - c| ≤ H c / 2 := by
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have h2 := hH.abs_sub t c
    have h3 : H t ≤ 3 / 2 * H c := by
      have := (abs_le.mp h2).2; linarith
    rw [inv_le_iff_one_le_mul₀ hc]
    calc (1 : ℝ) = H t * (H t)⁻¹ := (mul_inv_cancel₀ ht.ne').symm
      _ ≤ 3 / 2 * H c * (H t)⁻¹ := mul_le_mul_of_nonneg_right h3 (inv_pos.mpr ht).le
      _ = 3 / 2 * (H t)⁻¹ * H c := by ring
  · rw [mul_zero]; positivity

lemma measurable_kd (hH : WidthReg H) : Measurable (Function.uncurry (kd H)) := by
  have hc := hH.continuous
  have hHm : Measurable fun p : ℝ × ℝ => H p.1 := hc.measurable.comp measurable_fst
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 - H p.1 / 2 ≤ p.2 ∧ p.2 < p.1 + H p.1 / 2} :=
    (measurableSet_le (measurable_fst.sub (hHm.div_const 2)) measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.add (hHm.div_const 2)))
  have e : Function.uncurry (kd H) = fun p : ℝ × ℝ =>
      (H p.1)⁻¹ * {p : ℝ × ℝ | p.1 - H p.1 / 2 ≤ p.2 ∧ p.2 < p.1 + H p.1 / 2}.indicator
        (fun _ => (1 : ℝ)) p := by
    funext p
    simp only [Function.uncurry, kd, Set.indicator, Set.mem_Ico, Set.mem_setOf_eq]
  rw [e]
  exact hHm.inv.mul (measurable_const.indicator hS)

/-- `(t, v) ↦ k(t; v/w)` is measurable. -/
lemma measurable_kd_step (hH : WidthReg H) (w : ℝ) :
    Measurable fun p : ℝ × ℝ => kd H (p.2 / w) p.1 :=
  (measurable_kd hH).comp ((measurable_snd.div_const w).prodMk measurable_fst)

lemma measurable_kd_left (hH : WidthReg H) (c : ℝ) : Measurable (kd H c) :=
  (measurable_kd hH).comp (measurable_const.prodMk measurable_id)

lemma lintegral_kd (hH : WidthReg H) (c : ℝ) : ∫⁻ t, ‖kd H c t‖ₑ = 1 := by
  have hp := hH.pos c
  have e : (fun t => ‖kd H c t‖ₑ) = (Ico (c - H c / 2) (c + H c / 2)).indicator
      (fun _ => ENNReal.ofReal (H c)⁻¹) := by
    funext t
    unfold kd Set.indicator
    split_ifs
    · rw [mul_one, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hp)]
    · simp
  rw [e, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico,
    ← ENNReal.ofReal_mul (inv_pos.mpr hp).le]
  rw [show c + H c / 2 - (c - H c / 2) = H c by ring, inv_mul_cancel₀ hp.ne',
    ENNReal.ofReal_one]

lemma integrable_kd (hH : WidthReg H) (c : ℝ) : Integrable (kd H c) := by
  refine ⟨((measurable_kd hH).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
    ?_⟩
  unfold HasFiniteIntegral
  simp_rw [← ofReal_norm_eq_enorm] at *
  have := lintegral_kd hH c
  simp_rw [ofReal_norm_eq_enorm]
  rw [this]; exact ENNReal.one_lt_top

/-- The distribution function of the box density is the box ramp. -/
lemma cdf_kd (hH : WidthReg H) (c t : ℝ) :
    cdf (kd H c) t = boxAvg (H c) (stepF c) t := by
  have hp := hH.pos c
  rw [boxAvg_stepF hp]
  unfold cdf kd
  rw [integral_const_mul, integral_indicator measurableSet_Ico, Measure.restrict_restrict
    measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one]
  set h := H c
  congr 1
  rcases lt_or_ge t (c - h / 2) with h1 | h1
  · rw [show Ico (c - h / 2) (c + h / 2) ∩ Iic t = ∅ by
      ext s; simp only [mem_inter_iff, mem_Ico, mem_Iic, mem_empty_iff_false, iff_false]
      intro hs; linarith [hs.1.1, hs.2]]
    rw [measureReal_empty, max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  rcases lt_or_ge t (c + h / 2) with h2 | h2
  · rw [show Ico (c - h / 2) (c + h / 2) ∩ Iic t = Icc (c - h / 2) t by
      ext s; simp only [mem_inter_iff, mem_Ico, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨⟨a, -⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, by linarith⟩, b⟩]
    rw [Real.volume_real_Icc, max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_left (by linarith)]
    ring
  · rw [show Ico (c - h / 2) (c + h / 2) ∩ Iic t = Ico (c - h / 2) (c + h / 2) by
      ext s; simp only [mem_inter_iff, mem_Ico, mem_Iic]
      constructor
      · rintro ⟨a, -⟩; exact a
      · intro a; exact ⟨a, by linarith [a.2]⟩]
    rw [Real.volume_real_Ico, max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring

lemma cdf_kd_eq_Kv (hH : WidthReg H) (w v t : ℝ) : cdf (kd H (v / w)) t = Kv H w t v := by
  rw [cdf_kd hH, Kv_eq_boxAvg hH]

/-! ## The step `Qd` -/

lemma measurable_Qd_integrand (hH : WidthReg H) (w : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (Function.uncurry fun t v => f v * kd H (v / w) t) :=
  (hf.comp measurable_snd).mul (measurable_kd_step hH w)

lemma measurable_Qd (hH : WidthReg H) (w : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (Qd H w f) :=
  ((measurable_Qd_integrand hH w hf).stronglyMeasurable.integral_prod_right).measurable

/-- `∫ |Qd f| ≤ ∫ |f|`. -/
theorem lintegral_Qd_le (hH : WidthReg H) (w : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ t, ‖Qd H w f t‖ₑ ≤ ∫⁻ v, ‖f v‖ₑ := by
  have hj : Measurable (Function.uncurry fun t v => ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ) :=
    (hf.comp measurable_snd).enorm.mul (measurable_kd_step hH w).enorm
  calc ∫⁻ t, ‖Qd H w f t‖ₑ ≤ ∫⁻ t, ∫⁻ v, ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := by
        refine lintegral_mono fun t => ?_
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1; funext v; rw [enorm_mul]
    _ = ∫⁻ v, ∫⁻ t, ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ v, ‖f v‖ₑ := by
        congr 1; funext v
        rw [lintegral_const_mul _ (measurable_kd_left hH _).enorm, lintegral_kd hH, mul_one]

lemma integrable_Qd (hH : WidthReg H) (w : ℝ) {f : ℝ → ℝ} (hf : Integrable f)
    (hfm : Measurable f) : Integrable (Qd H w f) := by
  refine ⟨(measurable_Qd hH w hfm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_Qd_le hH w hfm) hf.2

lemma integrable_prod_Qd (hH : WidthReg H) (w : ℝ) {f : ℝ → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (S : Set ℝ) :
    Integrable (Function.uncurry fun t v => f v * kd H (v / w) t)
      ((volume.restrict S).prod volume) := by
  refine ⟨(measurable_Qd_integrand hH w hfm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hj : Measurable (Function.uncurry fun t v => ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ) :=
    (hfm.comp measurable_snd).enorm.mul (measurable_kd_step hH w).enorm
  calc ∫⁻ p, ‖Function.uncurry (fun t v => f v * kd H (v / w) t) p‖ₑ
        ∂((volume.restrict S).prod volume)
      = ∫⁻ t in S, ∫⁻ v, ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := by
        have e : (fun p : ℝ × ℝ => ‖Function.uncurry (fun t v => f v * kd H (v / w) t) p‖ₑ) =
            Function.uncurry fun t v => ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := by
          funext p; simp only [Function.uncurry, enorm_mul]
        rw [e, lintegral_prod _ hj.aemeasurable]
        rfl
    _ ≤ ∫⁻ t, ∫⁻ v, ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ v, ∫⁻ t, ‖f v‖ₑ * ‖kd H (v / w) t‖ₑ := lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ v, ‖f v‖ₑ := by
        congr 1; funext v
        rw [lintegral_const_mul _ (measurable_kd_left hH _).enorm, lintegral_kd hH, mul_one]
    _ < ⊤ := hf.2

/-- `cdf f (v) = ∫ stepF s v · f(s) ds` (the form of `Qv_density`). -/
lemma cdf_eq_stepF (f : ℝ → ℝ) (v : ℝ) : cdf f v = ∫ s, stepF s v * f s := by
  unfold cdf
  rw [← integral_indicator measurableSet_Iic]
  congr 1; funext s
  unfold stepF Set.indicator
  simp only [mem_Iic]
  split_ifs <;> ring

/-- **The step on densities is `Qv`**: `cdf (Qd f) = Qv (cdf f)`. -/
theorem cdf_Qd (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {f : ℝ → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (t : ℝ) : cdf (Qd H w f) t = Qv H w (cdf f) t := by
  have hQ : Qv H w (cdf f) t = ∫ s, f s * Kv H w t s := by
    have e : cdf f = fun v => ∫ s, stepF s v * f s := funext (cdf_eq_stepF f)
    rw [e, Qv_density hH hw hf t]
  rw [hQ]
  unfold cdf Qd
  rw [integral_integral_swap (integrable_prod_Qd hH w hf hfm _)]
  congr 1; funext v
  rw [integral_const_mul]
  congr 1
  rw [← cdf_kd_eq_Kv hH]; rfl

end KR

end
