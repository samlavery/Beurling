module

public import RequestProject.Beurling.LocalPNT.Defs

/-!
# §5.7: the box-average kernels (Steps 9 and 10 of Theorem 5.24)

* General facts on iterated box averages `boxAvg δ` of a bounded measurable `f` with compact
  support: bounds, growth of the support, plateaus, continuity and the Laplace transform
  `∫ boxAvg δ f · e^{sx} = (sinh(sδ)/(sδ)) ∫ f · e^{sx}` (via `MeasureTheory.integral_convolution`).
-/

@[expose] public section

open Set Real MeasureTheory Complex

namespace LocalPNT

/-! ## One box average -/

section BoxAvg

variable {δ M α β c : ℝ} {f : ℝ → ℝ}

lemma intervalIntegrable_of_bdd (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := M)).mono_fun hf.aestronglyMeasurable.restrict ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (hb x).1, abs_of_nonneg ((hb x).1.trans (hb x).2)]
  exact (hb x).2

lemma continuous_boxAvg (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    Continuous (boxAvg δ f) := by
  have hI := intervalIntegrable_of_bdd hf hb
  have h : boxAvg δ f = fun x => (1 / (2 * δ)) *
      ((∫ t in (0 : ℝ)..(x + δ), f t) - ∫ t in (0 : ℝ)..(x - δ), f t) := by
    funext x
    rw [boxAvg, intervalIntegral.integral_interval_sub_left (hI _ _) (hI _ _)]
  rw [h]
  have hP := intervalIntegral.continuous_primitive hI 0
  exact continuous_const.mul ((hP.comp (continuous_add_right δ)).sub
    (hP.comp (continuous_sub_right δ)))

lemma boxAvg_bounds (hδ : 0 < δ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (x : ℝ) :
    0 ≤ boxAvg δ f x ∧ boxAvg δ f x ≤ M := by
  have hI := intervalIntegrable_of_bdd hf hb
  have hle : x - δ ≤ x + δ := by linarith
  have h0 : 0 ≤ ∫ t in (x - δ)..(x + δ), f t :=
    intervalIntegral.integral_nonneg hle fun t _ => (hb t).1
  have h1 : (∫ t in (x - δ)..(x + δ), f t) ≤ 2 * δ * M := by
    have := intervalIntegral.integral_mono_on hle (hI _ _) intervalIntegrable_const
      (fun t _ => (hb t).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hδ' : 0 < 1 / (2 * δ) := by positivity
  refine ⟨mul_nonneg hδ'.le h0, ?_⟩
  calc boxAvg δ f x ≤ 1 / (2 * δ) * (2 * δ * M) := mul_le_mul_of_nonneg_left h1 hδ'.le
    _ = M := by field_simp

lemma boxAvg_support (hδ : 0 < δ) (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (x : ℝ)
    (hx : boxAvg δ f x ≠ 0) : x ∈ Icc (α - δ) (β + δ) := by
  by_contra hx'
  apply hx
  have : ∀ t ∈ uIcc (x - δ) (x + δ), f t = 0 := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    by_contra h
    have := hs t h
    simp only [mem_Icc, not_and_or, not_le] at hx' this ht
    rcases hx' with h' | h' <;> linarith [this.1, this.2, ht.1, ht.2]
  rw [boxAvg, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) this]
  simp

lemma boxAvg_plateau (hδ : 0 < δ) (hc : ∀ x ∈ Icc (α - δ) (β + δ), f x = c) :
    ∀ x ∈ Icc α β, boxAvg δ f x = c := by
  intro x hx
  have : EqOn f (fun _ => c) (uIcc (x - δ) (x + δ)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact hc t ⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩
  rw [boxAvg, intervalIntegral.integral_congr this]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- The Laplace multiplier of one box average. -/
noncomputable def boxFactor (δ : ℝ) (s : ℂ) : ℂ :=
  (1 / (2 * δ) : ℂ) * ∫ u in (-δ)..δ, cexp (s * u)

lemma boxFactor_eq {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : s ≠ 0) :
    boxFactor δ s = Complex.sinh (s * δ) / (s * δ) := by
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [boxFactor, integral_exp_mul_complex hs, Complex.sinh]
  push_cast
  field_simp

lemma boxFactor_zero {δ : ℝ} (hδ : 0 < δ) : boxFactor δ 0 = 1 := by
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  simp [boxFactor]
  field_simp
  ring

lemma integrable_mul_cexp (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (s : ℂ) :
    Integrable (fun x => (f x : ℂ) * cexp (s * x)) := by
  have hαβ : IntegrableOn (fun x => (f x : ℂ) * cexp (s * x)) (Icc α β) := by
    rcases le_or_gt α β with h | h
    · have hI : IntegrableOn f (Icc α β) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le h).1 (intervalIntegrable_of_bdd hf hb α β)
      have hI' : IntegrableOn (fun x => (f x : ℂ)) (Icc α β) := hI.ofReal
      exact hI'.mul_continuousOn (by fun_prop) isCompact_Icc
    · simp [Icc_eq_empty_of_lt h]
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hαβ
  intro x hx
  exact hs x (by intro h; simp [h] at hx)

theorem laplace_boxAvg (hδ : 0 < δ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (s : ℂ) :
    ∫ x, (boxAvg δ f x : ℂ) * cexp (s * x) = boxFactor δ s * ∫ x, (f x : ℂ) * cexp (s * x) := by
  set F : ℝ → ℂ := fun x => (f x : ℂ) * cexp (s * x)
  set G : ℝ → ℂ := (Icc (-δ) δ).indicator fun u => (1 / (2 * δ) : ℂ) * cexp (s * u)
  have hF : Integrable F := integrable_mul_cexp hf hb hs s
  have hG : Integrable G := by
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  have hconv : ∀ x, convolution F G (ContinuousLinearMap.mul ℂ ℂ) volume x =
      (boxAvg δ f x : ℂ) * cexp (s * x) := by
    intro x
    rw [convolution_def]
    have hpt : ∀ t, (ContinuousLinearMap.mul ℂ ℂ) (F t) (G (x - t)) =
        ((Icc (x - δ) (x + δ)).indicator (fun t => (f t : ℂ)) t) *
          ((1 / (2 * δ) : ℂ) * cexp (s * x)) := by
      intro t
      simp only [ContinuousLinearMap.mul_apply', F, G]
      by_cases ht : t ∈ Icc (x - δ) (x + δ)
      · have ht' : x - t ∈ Icc (-δ) δ := by
          simp only [mem_Icc] at ht ⊢; constructor <;> linarith
        rw [indicator_of_mem ht, indicator_of_mem ht']
        have : cexp (s * x) = cexp (s * t) * cexp (s * ↑(x - t)) := by
          rw [← Complex.exp_add]; push_cast; ring_nf
        rw [this]; ring
      · have ht' : x - t ∉ Icc (-δ) δ := by
          simp only [mem_Icc, not_and_or, not_le] at ht ⊢
          rcases ht with h | h
          · right; linarith
          · left; linarith
        rw [indicator_of_notMem ht, indicator_of_notMem ht']
        simp
    simp_rw [hpt]
    rw [integral_mul_const, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_ofReal, boxAvg]
    push_cast
    ring
  have := integral_convolution (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ) hF hG
  simp_rw [hconv] at this
  rw [this, ContinuousLinearMap.mul_apply', mul_comm]
  congr 1
  rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), boxFactor]

end BoxAvg

/-! ## Iterated box averages -/

section Iterate

variable {δ M α β c : ℝ} {f : ℝ → ℝ}

lemma iterate_boxAvg_props (hδ : 0 < δ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (n : ℕ) :
    Measurable ((boxAvg δ)^[n] f) ∧ (∀ x, 0 ≤ (boxAvg δ)^[n] f x ∧ (boxAvg δ)^[n] f x ≤ M) ∧
      (∀ x, (boxAvg δ)^[n] f x ≠ 0 → x ∈ Icc (α - n * δ) (β + n * δ)) := by
  induction n with
  | zero => simpa using ⟨hf, hb, hs⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨(continuous_boxAvg h1 h2).measurable, boxAvg_bounds hδ h1 h2, fun x hx => ?_⟩
    have := boxAvg_support hδ h3 x hx
    push_cast
    simp only [mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]

lemma continuous_iterate_boxAvg (hδ : 0 < δ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) {n : ℕ} (hn : 1 ≤ n) :
    Continuous ((boxAvg δ)^[n] f) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h1, h2, -⟩ := iterate_boxAvg_props hδ hf hb hs m
  rw [Function.iterate_succ_apply']
  exact continuous_boxAvg h1 h2

lemma iterate_boxAvg_plateau (hδ : 0 < δ) (n : ℕ) :
    ∀ α' β' : ℝ, (∀ x ∈ Icc (α' - n * δ) (β' + n * δ), f x = c) →
      ∀ x ∈ Icc α' β', (boxAvg δ)^[n] f x = c := by
  induction n with
  | zero => intro α' β' h; simpa using h
  | succ n ih =>
    intro α' β' h
    rw [Function.iterate_succ_apply']
    refine boxAvg_plateau hδ (ih _ _ fun x hx => h x ?_)
    simp only [mem_Icc] at hx ⊢
    push_cast
    constructor <;> linarith [hx.1, hx.2]

theorem laplace_iterate_boxAvg (hδ : 0 < δ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (s : ℂ) (n : ℕ) :
    ∫ x, ((boxAvg δ)^[n] f x : ℂ) * cexp (s * x) =
      boxFactor δ s ^ n * ∫ x, (f x : ℂ) * cexp (s * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := iterate_boxAvg_props hδ hf hb hs n
    rw [Function.iterate_succ_apply', laplace_boxAvg hδ h1 h2 h3, ih]
    ring

/-- The real integral is preserved by box averages. -/
theorem integral_iterate_boxAvg (hδ : 0 < δ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hs : ∀ x, f x ≠ 0 → x ∈ Icc α β) (n : ℕ) :
    ∫ x, (boxAvg δ)^[n] f x = ∫ x, f x := by
  have := laplace_iterate_boxAvg hδ hf hb hs 0 n
  simp only [zero_mul, Complex.exp_zero, mul_one, boxFactor_zero hδ, one_pow, one_mul] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Iterate

/-! ## The window `ψ` of Step 10 -/

section Window

variable {a b ω : ℝ} {k : ℕ}

lemma indicator_one_props (a' b' : ℝ) :
    Measurable ((Icc a' b').indicator (1 : ℝ → ℝ)) ∧
      (∀ x, 0 ≤ (Icc a' b').indicator (1 : ℝ → ℝ) x ∧ (Icc a' b').indicator (1 : ℝ → ℝ) x ≤ 1) ∧
      (∀ x, (Icc a' b').indicator (1 : ℝ → ℝ) x ≠ 0 → x ∈ Icc a' b') := by
  refine ⟨measurable_one.indicator measurableSet_Icc, fun x => ?_, fun x hx => ?_⟩
  · by_cases h : x ∈ Icc a' b' <;> simp [h]
  · by_contra h; simp [h] at hx

theorem windowLog_props (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) :
    (∀ x, 0 ≤ windowLog a b ω k x ∧ windowLog a b ω k x ≤ 1) ∧
    (∀ x ∈ Icc a b, windowLog a b ω k x = 1) ∧
    (∀ x, windowLog a b ω k x ≠ 0 → x ∈ Icc (a - 2 * ω) (b + 2 * ω)) ∧
    Continuous (windowLog a b ω k) := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hδ : 0 < ω / k := by positivity
  have hkδ : (k : ℝ) * (ω / k) = ω := by field_simp
  obtain ⟨h1, h2, h3⟩ := indicator_one_props (a - ω) (b + ω)
  obtain ⟨-, i2, i3⟩ := iterate_boxAvg_props hδ h1 h2 h3 k
  refine ⟨i2, ?_, fun x hx => ?_, continuous_iterate_boxAvg hδ h1 h2 h3 hk⟩
  · refine iterate_boxAvg_plateau hδ k a b fun x hx => ?_
    rw [hkδ] at hx
    simp [hx]
  · have := i3 x hx
    rw [hkδ] at this
    simp only [mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]

lemma laplace_indicator_one {a' b' : ℝ} (hab : a' ≤ b') (s : ℂ) :
    ∫ x, Complex.ofReal ((Icc a' b').indicator (1 : ℝ → ℝ) x) * cexp (s * x) =
      ∫ x in a'..b', cexp (s * x) := by
  have : (fun x : ℝ => Complex.ofReal ((Icc a' b').indicator (1 : ℝ → ℝ) x) * cexp (s * x)) =
      (Icc a' b').indicator fun x => cexp (s * x) := by
    funext x
    by_cases h : x ∈ Icc a' b' <;> simp [h]
  rw [this, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

theorem windowLog_laplace (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 0) :
    ∫ x, (windowLog a b ω k x : ℂ) * cexp (s * x) =
      (∫ x in (a - ω)..(b + ω), cexp (s * x)) *
        (Complex.sinh (s * (ω / k)) / (s * (ω / k))) ^ k := by
  have hδ : 0 < ω / k := by positivity
  obtain ⟨h1, h2, h3⟩ := indicator_one_props (a - ω) (b + ω)
  rw [windowLog, laplace_iterate_boxAvg hδ h1 h2 h3, laplace_indicator_one (by linarith),
    boxFactor_eq hδ hs, mul_comm]
  push_cast
  rfl

end Window

end LocalPNT

end
