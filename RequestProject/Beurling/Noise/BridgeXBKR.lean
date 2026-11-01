module

public import RequestProject.Beurling.Noise.KRTrueTV
public import RequestProject.Beurling.Noise.KRFacts

/-!
# Two estimates for a measure of mass `0` (proof of Lemma 5.27, Step 2)

For an integrable density `g` with mass `c = ∫ g`, the measure `g dt - c δ_a` has mass `0` and
distribution function `F = cdf g - c 1[a ≤ ·]`.

* `abs_sub_half_le` : **the half-TV bound**: for `Ψ` with values in `[0, 1]`,
  `|∫ g Ψ - c Ψ(a)| ≤ ½ (∫ |g| + |c|)` ("the defect of a mass-`0` measure against a
  `[0, 1]`-valued function is at most half its total variation");
* `kr_dual` : **the Kantorovich–Rubinstein duality** (Lemma 5.13, the definition of `‖·‖_KR`):
  if `g` vanishes outside `[a - R, a + R]` and `Φ` is `L`-Lipschitz, then
  `|∫ g (Φ - Φ(a))| ≤ L ∫ |F|`. The proof is the paper's integration by parts:
  `Φ(v) - Φ(a) = ∫_a^v Φ'` (Lipschitz functions are absolutely continuous), Fubini, and
  `∫ g(v) (1[a < s ≤ v] - 1[v < s ≤ a]) dv = -F(s)` for `s ≠ a`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace KR

/-- **The half-TV bound.** -/
lemma abs_sub_half_le {g Ψ : ℝ → ℝ} (hg : Integrable g) (hΨm : Measurable Ψ)
    (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1) (a : ℝ) :
    |(∫ v, g v * Ψ v) - (∫ v, g v) * Ψ a| ≤
      1 / 2 * ((∫⁻ v, ‖g v‖ₑ).toReal + |∫ v, g v|) := by
  have hb : ∀ᵐ v ∂volume, ‖Ψ v‖ ≤ 1 := Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hΨ v).1, (hΨ v).2]
  have hi : Integrable (fun v => g v * Ψ v) := by
    simpa [mul_comm] using hg.bdd_mul (c := 1) hΨm.aestronglyMeasurable hb
  have hi2 : Integrable (fun v => g v * (Ψ v - 1 / 2)) := by
    have := hi.sub (hg.mul_const (1 / 2))
    simpa [mul_sub, Pi.sub_def] using this
  have e : (∫ v, g v * Ψ v) - (∫ v, g v) * Ψ a =
      (∫ v, g v * (Ψ v - 1 / 2)) - (∫ v, g v) * (Ψ a - 1 / 2) := by
    rw [show (fun v => g v * (Ψ v - 1 / 2)) = fun v => g v * Ψ v - g v * (1 / 2) by
      funext v; ring, integral_sub hi (hg.mul_const _), integral_mul_const]
    ring
  rw [e]
  have h1 : |∫ v, g v * (Ψ v - 1 / 2)| ≤ 1 / 2 * (∫⁻ v, ‖g v‖ₑ).toReal := by
    rw [← integral_norm_eq_lintegral_enorm hg.1, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans
      (integral_mono hi2.abs (hg.norm.const_mul _) fun v => ?_)
    simp only [abs_mul, Real.norm_eq_abs]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith [(hΨ v).1, (hΨ v).2]
  have h2 : |(∫ v, g v) * (Ψ a - 1 / 2)| ≤ 1 / 2 * |∫ v, g v| := by
    rw [abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith [(hΨ a).1, (hΨ a).2]
  calc _ ≤ |∫ v, g v * (Ψ v - 1 / 2)| + |(∫ v, g v) * (Ψ a - 1 / 2)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The kernel of the integration by parts: `1[a < s ≤ v] - 1[v < s ≤ a]`. -/
noncomputable def ibpK (a v s : ℝ) : ℝ :=
  (Ioc a v).indicator (fun _ => (1 : ℝ)) s - (Ioc v a).indicator (fun _ => (1 : ℝ)) s

lemma abs_ibpK_le (a v s : ℝ) : |ibpK a v s| ≤ 1 := by
  unfold ibpK
  simp only [Set.indicator, mem_Ioc]
  split_ifs with h1 h2 h2
  · exfalso; linarith [h1.1, h1.2, h2.1, h2.2]
  all_goals norm_num

lemma ibpK_ne_zero {a v s : ℝ} (h : ibpK a v s ≠ 0) : |s - a| ≤ |v - a| := by
  unfold ibpK at h
  simp only [Set.indicator, mem_Ioc] at h
  split_ifs at h with h1 h2 h2
  · exfalso; linarith [h1.1, h1.2, h2.1, h2.2]
  · rw [abs_of_pos (by linarith [h1.1]), abs_of_pos (by linarith [h1.1, h1.2])]; linarith [h1.2]
  · rw [abs_of_nonpos (by linarith [h2.2]), abs_of_neg (by linarith [h2.1, h2.2])]
    linarith [h2.1]
  · exact absurd (by norm_num) h

lemma measurable_ibpK (a : ℝ) : Measurable (Function.uncurry (ibpK a)) := by
  unfold ibpK
  apply Measurable.sub
  · apply Measurable.indicator measurable_const
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  · apply Measurable.indicator measurable_const
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

lemma intervalIntegral_eq_ibpK {φ : ℝ → ℝ} (hφ : ∀ x y : ℝ, IntervalIntegrable φ volume x y)
    (a v : ℝ) : ∫ s in a..v, φ s = ∫ s, φ s * ibpK a v s := by
  have h1 := (hφ a v).1
  have h2 := (hφ a v).2
  rw [intervalIntegral, show (fun s => φ s * ibpK a v s) = fun s =>
    (Ioc a v).indicator φ s - (Ioc v a).indicator φ s by
      funext s; unfold ibpK Set.indicator; split_ifs <;> ring,
    integral_sub (h1.integrable_indicator measurableSet_Ioc)
      ((hφ v a).1.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]

/-- The inner integral of the integration by parts. -/
lemma integral_mul_ibpK {g : ℝ → ℝ} (hg : Integrable g) {a s : ℝ} (hs : s ≠ a) :
    ∫ v, g v * ibpK a v s = -(cdf g s - (∫ v, g v) * stepF a s) := by
  have hIio : ∫ v in Iio s, g v = cdf g s := by
    unfold cdf; exact (integral_Iic_eq_integral_Iio (μ := volume)).symm
  rcases lt_or_gt_of_ne hs with h | h
  · -- `s < a`: `ibpK = -1[v < s]`
    have e : (fun v => g v * ibpK a v s) = fun v => -(Iio s).indicator g v := by
      funext v; unfold ibpK; simp only [Set.indicator, mem_Ioc, mem_Iio]
      by_cases hv : v < s
      · rw [if_neg (by intro h'; linarith [h'.1]), if_pos ⟨hv, h.le⟩, if_pos hv]; ring
      · rw [if_neg (by intro h'; linarith [h'.1]), if_neg (by intro h'; exact hv h'.1),
          if_neg hv]; ring
    rw [e, integral_neg, integral_indicator measurableSet_Iio, hIio]
    unfold stepF; rw [if_neg (by linarith)]; ring
  · -- `s > a`: `ibpK = 1[s ≤ v]`
    have e : (fun v => g v * ibpK a v s) = fun v => g v - (Iio s).indicator g v := by
      funext v; unfold ibpK; simp only [Set.indicator, mem_Ioc, mem_Iio]
      by_cases hv : s ≤ v
      · rw [if_pos ⟨h, hv⟩, if_neg (by intro h'; linarith [h'.2]),
          if_neg (not_lt.mpr hv)]; ring
      · push_neg at hv
        rw [if_neg (by intro h'; linarith [h'.2]), if_neg (by intro h'; linarith [h'.2]),
          if_pos hv]; ring
    rw [e, integral_sub hg (hg.indicator measurableSet_Iio),
      integral_indicator measurableSet_Iio, hIio]
    unfold stepF; rw [if_pos h.le]; ring

/-- The distribution function of `g dt - c δ_a` vanishes outside `[a - R, a + R]`. -/
lemma cdf_sub_step_eq_zero {g : ℝ → ℝ} (hg : Integrable g) {a R : ℝ}
    (hsupp : ∀ v, R < |v - a| → g v = 0) {s : ℝ} (hs : R < |s - a|) :
    cdf g s - (∫ v, g v) * stepF a s = 0 := by
  rcases lt_or_ge s a with h | h
  · rw [abs_of_neg (by linarith)] at hs
    unfold cdf stepF
    rw [if_neg (by linarith), mul_zero, sub_zero]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    apply hsupp
    rw [abs_of_neg (by linarith [mem_Iic.mp hv])]; linarith [mem_Iic.mp hv]
  · rw [abs_of_nonneg (by linarith)] at hs
    unfold cdf stepF
    rw [if_pos h, mul_one, sub_eq_zero]
    rw [← integral_add_compl (s := Iic s) measurableSet_Iic hg, compl_Iic]
    rw [setIntegral_eq_zero_of_forall_eq_zero (t := Ioi s) fun v hv => ?_, add_zero]
    apply hsupp
    rw [abs_of_pos (by linarith [mem_Ioi.mp hv])]; linarith [mem_Ioi.mp hv]

/-- The distribution function of an integrable density is continuous. -/
lemma continuous_cdf {g : ℝ → ℝ} (hg : Integrable g) : Continuous (cdf g) := by
  have e : cdf g = fun t => (∫ v in Iic 0, g v) + ∫ v in (0 : ℝ)..t, g v := by
    funext t
    unfold cdf
    rw [← intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn]; ring
  rw [e]
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => hg.intervalIntegrable) 0)

/-- **The Kantorovich–Rubinstein duality** for `g dt - c δ_a`. -/
theorem kr_dual {g Φ : ℝ → ℝ} (hg : Integrable g) (hgm : Measurable g) {a R : ℝ}
    (hsupp : ∀ v, R < |v - a| → g v = 0) {L : ℝ≥0} (hΦ : LipschitzWith L Φ) :
    |∫ v, g v * (Φ v - Φ a)| ≤
      L * (∫⁻ t, ‖cdf g t - (∫ v, g v) * stepF a t‖ₑ).toReal := by
  set φ := deriv Φ
  have hφb : ∀ s, |φ s| ≤ L := fun s => by
    have := norm_deriv_le_of_lipschitz (x₀ := s) hΦ; rwa [Real.norm_eq_abs] at this
  have hφm : Measurable φ := measurable_deriv Φ
  have hφi : ∀ x y : ℝ, IntervalIntegrable φ volume x y := fun x y =>
    (intervalIntegrable_const (c := (L : ℝ))).mono_fun hφm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        show |φ s| ≤ |(L : ℝ)|
        exact (hφb s).trans (le_abs_self _))
  have hFTC : ∀ v, Φ v - Φ a = ∫ s, φ s * ibpK a v s := by
    intro v
    rw [← intervalIntegral_eq_ibpK hφi]
    exact ((hΦ.lipschitzOnWith (s := uIcc a v)).absolutelyContinuousOnInterval
      ).integral_deriv_eq_sub.symm
  set R' := max R 0
  have hsupp' : ∀ v, R' < |v - a| → g v = 0 := fun v hv => hsupp v (lt_of_le_of_lt
    (le_max_left _ _) hv)
  -- the product integrand
  set F2 : ℝ → ℝ → ℝ := fun v s => g v * (φ s * ibpK a v s)
  have hF2m : Measurable (Function.uncurry F2) :=
    (hgm.comp measurable_fst).mul ((hφm.comp measurable_snd).mul (measurable_ibpK a))
  have hbound : Integrable (fun z : ℝ × ℝ => (L * |g z.1|) *
      (Icc (a - R') (a + R')).indicator (fun _ => (1 : ℝ)) z.2) (volume.prod volume) :=
    Integrable.mul_prod (hg.abs.const_mul _)
      ((integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc)
  have hF2i : Integrable (Function.uncurry F2) (volume.prod volume) := by
    refine hbound.mono' hF2m.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    obtain ⟨v, s⟩ := z
    simp only [Function.uncurry, F2, Real.norm_eq_abs]
    by_cases hgv : g v = 0
    · simp only [hgv, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    by_cases hk : ibpK a v s = 0
    · simp only [hk, mul_zero, abs_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hva : |v - a| ≤ R' := by
      by_contra hc; push_neg at hc; exact hgv (hsupp' v hc)
    have hsa := (ibpK_ne_zero hk).trans hva
    rw [Set.indicator_of_mem (by rw [mem_Icc]; constructor <;>
      linarith [(abs_le.mp hsa).1, (abs_le.mp hsa).2]), mul_one, abs_mul, abs_mul]
    have h1 := hφb s
    have h2 := abs_ibpK_le a v s
    rw [mul_comm (L : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith [abs_nonneg (φ s), abs_nonneg (ibpK a v s)]
  -- the swap
  have hswap : ∫ v, g v * (Φ v - Φ a) = ∫ s, φ s * (∫ v, g v * ibpK a v s) := by
    have e1 : ∀ v, g v * (Φ v - Φ a) = ∫ s, F2 v s := by
      intro v; rw [hFTC v, ← integral_const_mul]
    simp_rw [e1]
    rw [integral_integral_swap hF2i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F2]
    rw [← integral_const_mul]
    congr 1; funext v; ring
  rw [hswap]
  set Fd : ℝ → ℝ := fun t => cdf g t - (∫ v, g v) * stepF a t
  have hin : (fun s => φ s * (∫ v, g v * ibpK a v s)) =ᵐ[volume] fun s => -(φ s * Fd s) := by
    have hne : ∀ᵐ s ∂volume, s ≠ a := by
      rw [ae_iff]; simp
    filter_upwards [hne] with s hs
    rw [integral_mul_ibpK hg hs]; ring
  rw [integral_congr_ae hin, integral_neg, abs_neg]
  -- `Fd` is bounded and compactly supported
  have hFdm : Measurable Fd :=
    (((continuous_cdf hg).measurable).sub (measurable_const.mul (measurable_stepF a)))
  have hFd0 : ∀ s, R' < |s - a| → Fd s = 0 := fun s hs => cdf_sub_step_eq_zero hg hsupp' hs
  have hFdb : ∀ s, |Fd s| ≤ 2 * ∫ v, |g v| := by
    intro s
    have h1 : |cdf g s| ≤ ∫ v, |g v| := by
      unfold cdf
      exact (abs_integral_le_integral_abs).trans
        (setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun v => abs_nonneg _))
    have h2 : |(∫ v, g v) * stepF a s| ≤ ∫ v, |g v| := by
      rw [abs_mul]
      have : |stepF a s| ≤ 1 := by unfold stepF; split_ifs <;> simp
      calc |∫ v, g v| * |stepF a s| ≤ |∫ v, g v| * 1 :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ ∫ v, |g v| := by rw [mul_one]; exact abs_integral_le_integral_abs
    calc |Fd s| ≤ |cdf g s| + |(∫ v, g v) * stepF a s| := abs_sub _ _
      _ ≤ _ := by linarith
  have hFdi : Integrable Fd := by
    have hc : Integrable ((Icc (a - R') (a + R')).indicator
        (fun _ => 2 * ∫ v, |g v|)) :=
      (integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
    refine hc.mono' hFdm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs]
    by_cases hs : |s - a| ≤ R'
    · rw [Set.indicator_of_mem (by rw [mem_Icc]; constructor <;>
        linarith [(abs_le.mp hs).1, (abs_le.mp hs).2])]
      exact hFdb s
    · push_neg at hs
      rw [hFd0 s hs, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hφFi : Integrable (fun s => φ s * Fd s) := by
    have hb : ∀ᵐ s ∂volume, ‖φ s‖ ≤ L := Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hφb s
    exact hFdi.bdd_mul (c := L) hφm.aestronglyMeasurable hb
  rw [← integral_norm_eq_lintegral_enorm hFdi.1, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans
    (integral_mono hφFi.abs (hFdi.norm.const_mul _) fun s => ?_)
  simp only [abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφb s) (abs_nonneg _)

end KR

end
