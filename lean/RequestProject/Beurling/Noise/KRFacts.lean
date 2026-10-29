module

public import Mathlib

/-!
# Lemma 5.13 (Kantorovich–Rubinstein facts), in distribution-function form

A finite signed measure `ν` on `ℝ` is represented by its distribution function
`F_ν(t) = ν((-∞, t])`. In this representation (§5.9.2):

* `δ_a` has distribution function `stepF a = 1[a ≤ ·]`;
* the convolution with the uniform probability `bx_h` on `[-h/2, h/2)` is
  `boxAvg h F (t) = h⁻¹ ∫_{t-h/2}^{t+h/2} F`;
* the push-forward `D_w` under `t ↦ t/w` (`w > 0`) is `t ↦ F(w t)`;
* the Kantorovich–Rubinstein norm of a measure of mass `0` is `‖ν‖_KR = ∫ |F_ν|` (`KRn`, as an
  extended real, so no integrability side conditions are needed);
* the total variation of `ν` is the variation of `F_ν` on `ℝ` (`eVariationOn F univ`).

Proved here (`F`, `G` bounded and measurable, `h, w > 0`):

* (K1) for `ρ = bx_h`: `KRn (boxAvg h F) ≤ KRn F` (`KRn_boxAvg_le`);
* (K2) `KRn (F(w ·)) = w⁻¹ KRn F` (`KRn_comp_mul`);
* (K3) `TV(bx_h * G) ≤ h⁻¹ ∫ |G(t + h/2) - G(t - h/2)|` (`eVariationOn_boxAvg_le`), which gives
  `TV(bx_h * ν) ≤ (2/h) KRn ν` after the triangle inequality and translation invariance
  (`lintegral_shift_sub_le`);
* (K4) for `ρ = bx_h`, `a`: `KRn (boxAvg h (stepF a) - stepF a) ≤ h/4` (`KRn_box_sub_step_le`,
  `‖bx_h - δ_0‖_KR = h/4`).
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ENNReal

namespace KR

/-- The distribution function of `δ_a`. -/
noncomputable def stepF (a : ℝ) (t : ℝ) : ℝ := if a ≤ t then 1 else 0

/-- The distribution function of `bx_h * ν` for `ν` of distribution function `F`. -/
noncomputable def boxAvg (h : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  h⁻¹ * ∫ s in (t - h / 2)..(t + h / 2), F s

/-- The Kantorovich–Rubinstein norm `∫ |F|` (for a distribution function of a measure of mass
`0`). -/
noncomputable def KRn (F : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ t, ‖F t‖ₑ

/-- Bounded and measurable. -/
def BM (F : ℝ → ℝ) : Prop := Measurable F ∧ ∃ M, ∀ t, |F t| ≤ M

lemma BM.intervalIntegrable {F : ℝ → ℝ} (hF : BM F) (a b : ℝ) :
    IntervalIntegrable F volume a b := by
  obtain ⟨hm, M, hM⟩ := hF
  refine (intervalIntegrable_const (c := M)).mono_fun hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  simp only [Real.norm_eq_abs]
  exact (hM t).trans (le_abs_self M)

lemma measurable_stepF (a : ℝ) : Measurable (stepF a) := by
  unfold stepF
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma BM_stepF (a : ℝ) : BM (stepF a) :=
  ⟨measurable_stepF a, 1, fun _ => by unfold stepF; split_ifs <;> simp⟩

lemma BM.comp_mul {F : ℝ → ℝ} (hF : BM F) (w : ℝ) : BM (fun t => F (w * t)) :=
  ⟨hF.1.comp (measurable_const_mul w), hF.2.choose, fun _ => hF.2.choose_spec _⟩

lemma BM.const_mul {F : ℝ → ℝ} (hF : BM F) (c : ℝ) : BM (fun t => c * F t) := by
  obtain ⟨hm, M, hM⟩ := hF
  refine ⟨measurable_const.mul hm, |c| * M, fun t => ?_⟩
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg c)

lemma BM.add {F G : ℝ → ℝ} (hF : BM F) (hG : BM G) : BM (fun t => F t + G t) := by
  obtain ⟨hm, M, hM⟩ := hF
  obtain ⟨hm', M', hM'⟩ := hG
  exact ⟨hm.add hm', M + M', fun t => (abs_add_le _ _).trans (add_le_add (hM t) (hM' t))⟩

lemma BM.sub {F G : ℝ → ℝ} (hF : BM F) (hG : BM G) : BM (fun t => F t - G t) := by
  obtain ⟨hm, M, hM⟩ := hF
  obtain ⟨hm', M', hM'⟩ := hG
  exact ⟨hm.sub hm', M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩

lemma BM.neg {F : ℝ → ℝ} (hF : BM F) : BM (fun t => -F t) := by
  obtain ⟨hm, M, hM⟩ := hF
  exact ⟨hm.neg, M, fun t => by rw [abs_neg]; exact hM t⟩

lemma BM_zero : BM (fun _ => 0) := ⟨measurable_const, 0, fun _ => by simp⟩

lemma BM.finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, BM (F i)) :
    BM (fun t => ∑ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM_zero
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1.add h2

lemma BM.comp_add {F : ℝ → ℝ} (hF : BM F) (c : ℝ) : BM (fun t => F (t + c)) :=
  ⟨hF.1.comp (measurable_add_const c), hF.2.choose, fun _ => hF.2.choose_spec _⟩

/-- `boxAvg h F b - boxAvg h F a = h⁻¹ ∫_a^b (F(s + h/2) - F(s - h/2)) ds`. -/
lemma boxAvg_sub {F : ℝ → ℝ} (hF : BM F) (h a b : ℝ) :
    boxAvg h F b - boxAvg h F a =
      h⁻¹ * ∫ s in a..b, (F (s + h / 2) - F (s - h / 2)) := by
  unfold boxAvg
  have hi := hF.intervalIntegrable
  have h1 := (hF.comp_add (h / 2)).intervalIntegrable a b
  have h2 := (hF.comp_add (-(h / 2))).intervalIntegrable a b
  simp only [← sub_eq_add_neg] at h2
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_comp_add_right F,
    intervalIntegral.integral_comp_sub_right F, ← mul_sub]
  congr 1
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi (a - h / 2) (b - h / 2))
    (hi (b - h / 2) (b + h / 2))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi (a - h / 2) (a + h / 2))
    (hi (a + h / 2) (b + h / 2))
  linarith

lemma continuous_boxAvg {F : ℝ → ℝ} (hF : BM F) (h : ℝ) : Continuous (boxAvg h F) := by
  unfold boxAvg
  apply Continuous.mul continuous_const
  have hi := hF.intervalIntegrable
  have hP : Continuous fun b => ∫ x in (0 : ℝ)..b, F x :=
    intervalIntegral.continuous_primitive hi 0
  have e : (fun t => ∫ s in (t - h / 2)..(t + h / 2), F s) =
      fun t => (∫ x in (0 : ℝ)..(t + h / 2), F x) - ∫ x in (0 : ℝ)..(t - h / 2), F x := by
    funext t
    rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  rw [e]
  exact (hP.comp (continuous_id.add continuous_const)).sub
    (hP.comp (continuous_id.sub continuous_const))

/-! ## (K2): dilation -/

/-- **(K2)** `‖D_w ν‖_KR = ‖ν‖_KR / w`: `∫ |F(w t)| dt = w⁻¹ ∫ |F|` for `w > 0`. -/
lemma KRn_comp_mul {F : ℝ → ℝ} (hF : Measurable F) {w : ℝ} (hw : 0 < w) :
    KRn (fun t => F (w * t)) = ENNReal.ofReal w⁻¹ * KRn F := by
  unfold KRn
  have hm : Measurable fun t => ‖F t‖ₑ := hF.enorm
  rw [← lintegral_map hm (measurable_const_mul w), Real.map_volume_mul_left hw.ne',
    lintegral_smul_measure, abs_of_pos (inv_pos.mpr hw)]
  rfl

/-! ## (K1) for the box -/

lemma enorm_boxAvg_le {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ‖boxAvg h F t‖ₑ ≤ ENNReal.ofReal h⁻¹ * ∫⁻ s in Ioc (t - h / 2) (t + h / 2), ‖F s‖ₑ := by
  unfold boxAvg
  rw [enorm_mul, intervalIntegral.integral_of_le (by linarith)]
  gcongr
  · rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hh)]
  · exact enorm_integral_le_lintegral_enorm _

/-- **(K1)** for `ρ = bx_h`: `‖bx_h * ν‖_KR ≤ ‖ν‖_KR`. -/
lemma KRn_boxAvg_le {F : ℝ → ℝ} (hF : Measurable F) {h : ℝ} (hh : 0 < h) :
    KRn (boxAvg h F) ≤ KRn F := by
  unfold KRn
  set S : Set (ℝ × ℝ) := {p | p.1 - h / 2 < p.2 ∧ p.2 ≤ p.1 + h / 2}
  have hS : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact measurableSet_lt (measurable_fst.sub_const _) measurable_snd
    · exact measurableSet_le measurable_snd (measurable_fst.add_const _)
  set g : ℝ → ℝ → ℝ≥0∞ := fun t s => S.indicator (fun p => ‖F p.2‖ₑ) (t, s)
  have hg : Measurable (Function.uncurry g) :=
    (hF.enorm.comp measurable_snd).indicator hS
  have h1 : ∀ t, ∫⁻ s in Ioc (t - h / 2) (t + h / 2), ‖F s‖ₑ = ∫⁻ s, g t s := by
    intro t
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1
  have h2 : ∀ s, ∫⁻ t, g t s = ‖F s‖ₑ * ENNReal.ofReal h := by
    intro s
    have : (fun t => g t s) = (Ico (s - h / 2) (s + h / 2)).indicator (fun _ => ‖F s‖ₑ) := by
      funext t
      simp only [g, S, Set.indicator, Set.mem_Ico, Set.mem_setOf_eq]
      congr 1
      apply propext
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [this, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
    congr 2; ring
  calc ∫⁻ t, ‖boxAvg h F t‖ₑ
      ≤ ∫⁻ t, ENNReal.ofReal h⁻¹ * ∫⁻ s in Ioc (t - h / 2) (t + h / 2), ‖F s‖ₑ :=
        lintegral_mono fun t => enorm_boxAvg_le hh t
    _ = ENNReal.ofReal h⁻¹ * ∫⁻ t, ∫⁻ s, g t s := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [h1]
    _ = ENNReal.ofReal h⁻¹ * ∫⁻ s, ∫⁻ t, g t s := by
        rw [lintegral_lintegral_swap hg.aemeasurable]
    _ = ENNReal.ofReal h⁻¹ * (ENNReal.ofReal h * ∫⁻ s, ‖F s‖ₑ) := by
        simp_rw [h2]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm (∫⁻ s, ‖F s‖ₑ)]
    _ = ∫⁻ s, ‖F s‖ₑ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hh).le, inv_mul_cancel₀ hh.ne',
          ENNReal.ofReal_one, one_mul]

/-! ## (K3): the total variation after a box -/

lemma lintegral_Ioc_telescope (f : ℝ → ℝ≥0∞) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ s in Ioc (u i) (u (i + 1)), f s = ∫⁻ s in Ioc (u 0) (u n), f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
      (Set.Ioc_disjoint_Ioc_of_le le_rfl),
      Set.Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]

/-- **(K3)**, distribution-function form: the variation of `bx_h * ν` is at most
`h⁻¹ ∫ |F_ν(t + h/2) - F_ν(t - h/2)| dt`. -/
lemma eVariationOn_boxAvg_le {G : ℝ → ℝ} (hG : BM G) {h : ℝ} (hh : 0 < h) :
    eVariationOn (boxAvg h G) univ ≤
      ENNReal.ofReal h⁻¹ * ∫⁻ t, ‖G (t + h / 2) - G (t - h / 2)‖ₑ := by
  set φ : ℝ → ℝ := fun s => G (s + h / 2) - G (s - h / 2)
  have key : ∀ a b, a ≤ b → edist (boxAvg h G b) (boxAvg h G a) ≤
      ENNReal.ofReal h⁻¹ * ∫⁻ s in Ioc a b, ‖φ s‖ₑ := by
    intro a b hab
    rw [edist_eq_enorm_sub, boxAvg_sub hG, enorm_mul, intervalIntegral.integral_of_le hab]
    gcongr
    · rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hh)]
    · exact enorm_integral_le_lintegral_enorm _
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, -⟩ := p
  calc ∑ i ∈ Finset.range n, edist (boxAvg h G (u (i + 1))) (boxAvg h G (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal h⁻¹ * ∫⁻ s in Ioc (u i) (u (i + 1)), ‖φ s‖ₑ :=
        Finset.sum_le_sum fun i _ => key _ _ (hu (Nat.le_succ i))
    _ = ENNReal.ofReal h⁻¹ * ∫⁻ s in Ioc (u 0) (u n), ‖φ s‖ₑ := by
        rw [← Finset.mul_sum, lintegral_Ioc_telescope _ u hu n]
    _ ≤ ENNReal.ofReal h⁻¹ * ∫⁻ t, ‖φ t‖ₑ :=
        mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- `∫ |F(t + c)| dt = ∫ |F|`. -/
lemma lintegral_shift (F : ℝ → ℝ) (c : ℝ) : ∫⁻ t, ‖F (t + c)‖ₑ = ∫⁻ t, ‖F t‖ₑ :=
  lintegral_add_right_eq_self (fun t => ‖F t‖ₑ) c

/-- `∫ |F(t + h/2) - F(t - h/2)| ≤ 2 ∫ |F|`. -/
lemma lintegral_shift_sub_le {F : ℝ → ℝ} (hF : Measurable F) (h : ℝ) :
    ∫⁻ t, ‖F (t + h / 2) - F (t - h / 2)‖ₑ ≤ 2 * KRn F := by
  unfold KRn
  calc ∫⁻ t, ‖F (t + h / 2) - F (t - h / 2)‖ₑ
      ≤ ∫⁻ t, (‖F (t + h / 2)‖ₑ + ‖F (t + -(h / 2))‖ₑ) := by
        refine lintegral_mono fun t => ?_
        rw [← sub_eq_add_neg]; exact enorm_sub_le
    _ = (∫⁻ t, ‖F (t + h / 2)‖ₑ) + ∫⁻ t, ‖F (t + -(h / 2))‖ₑ :=
        lintegral_add_left (f := fun t => ‖F (t + h / 2)‖ₑ)
          (by exact (hF.comp (measurable_add_const (h / 2))).enorm) _
    _ = 2 * ∫⁻ t, ‖F t‖ₑ := by
        have e1 : ∫⁻ t, ‖F (t + h / 2)‖ₑ = ∫⁻ t, ‖F t‖ₑ :=
          lintegral_add_right_eq_self (fun t => ‖F t‖ₑ) (h / 2)
        have e2 : ∫⁻ t, ‖F (t + -(h / 2))‖ₑ = ∫⁻ t, ‖F t‖ₑ :=
          lintegral_add_right_eq_self (fun t => ‖F t‖ₑ) (-(h / 2))
        rw [e1, e2, two_mul]

/-- `∫ |1[a ≤ t + h/2] - 1[a ≤ t - h/2]| dt = h`. -/
lemma lintegral_step_shift_sub (a : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ t, ‖stepF a (t + h / 2) - stepF a (t - h / 2)‖ₑ = ENNReal.ofReal h := by
  have : (fun t => ‖stepF a (t + h / 2) - stepF a (t - h / 2)‖ₑ) =
      (Ico (a - h / 2) (a + h / 2)).indicator (fun _ => 1) := by
    funext t
    unfold stepF
    simp only [Set.indicator, Set.mem_Ico]
    by_cases h1 : a ≤ t - h / 2
    · rw [if_pos (by linarith), if_pos h1, if_neg (by intro h'; linarith [h'.2])]; simp
    · by_cases h2 : a ≤ t + h / 2
      · rw [if_pos h2, if_neg h1, if_pos ⟨by linarith, by linarith⟩]; simp
      · rw [if_neg h2, if_neg h1, if_neg (by intro h'; linarith [h'.1])]; simp
  rw [this, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, one_mul]
  congr 1; ring

/-! ## (K4): `‖bx_h - δ_0‖_KR = h/4` -/

/-- A primitive of `stepF a`: `Φ(s) = (s - a)₊`, with right derivative `stepF a` everywhere. -/
lemma integral_stepF (a : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ∫ s in x..y, stepF a s = max 0 (y - a) - max 0 (x - a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy
  · exact (continuous_const.max (continuous_id.sub continuous_const)).continuousOn
  · intro s _
    unfold stepF
    by_cases hs : a ≤ s
    · rw [if_pos hs]
      have : HasDerivWithinAt (fun r => r - a) 1 (Ioi s) s :=
        ((hasDerivAt_id s).sub_const a).hasDerivWithinAt
      refine this.congr (fun r hr => ?_) ?_
      · rw [Set.mem_Ioi] at hr; exact max_eq_right (by linarith)
      · exact max_eq_right (by linarith)
    · rw [if_neg hs]
      push_neg at hs
      have : HasDerivAt (fun r : ℝ => max 0 (r - a)) 0 s := by
        apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hs] with r hr
        rw [Set.mem_Iio] at hr
        rw [max_eq_left (by linarith)]
      exact this.hasDerivWithinAt
  · exact (BM_stepF a).intervalIntegrable x y

lemma boxAvg_stepF {h : ℝ} (hh : 0 < h) (a t : ℝ) :
    boxAvg h (stepF a) t = h⁻¹ * (max 0 (t + h / 2 - a) - max 0 (t - h / 2 - a)) := by
  unfold boxAvg
  rw [integral_stepF a (by linarith)]

/-- The tent `(1/2 - |t - a|/h)₊`, of integral `h/4`. -/
lemma abs_boxAvg_step_sub_le {h : ℝ} (hh : 0 < h) (a t : ℝ) :
    |boxAvg h (stepF a) t - stepF a t| ≤
      (Icc (a - h / 2) (a + h / 2)).indicator (fun t => 1 / 2 - |t - a| / h) t := by
  rw [boxAvg_stepF hh]
  by_cases hI : t ∈ Icc (a - h / 2) (a + h / 2)
  · rw [Set.indicator_of_mem hI]
    obtain ⟨h1, h2⟩ := hI
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ t + h / 2 - a),
      max_eq_left (by linarith : t - h / 2 - a ≤ 0), sub_zero]
    unfold stepF
    by_cases h3 : a ≤ t
    · rw [if_pos h3, abs_of_nonneg (by linarith : 0 ≤ t - a)]
      have e : h⁻¹ * (t + h / 2 - a) - 1 = -(1 / 2 - (t - a) / h) := by field_simp; ring
      rw [e, abs_neg, abs_of_nonneg]
      rw [sub_nonneg, div_le_iff₀ hh]; linarith
    · push_neg at h3
      rw [if_neg (not_le.mpr h3), abs_of_neg (by linarith : t - a < 0)]
      have e : h⁻¹ * (t + h / 2 - a) - 0 = 1 / 2 - -(t - a) / h := by field_simp; ring
      rw [e, abs_of_nonneg]
      rw [sub_nonneg, div_le_iff₀ hh]; linarith
  · rw [Set.indicator_of_notMem hI]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hI
    unfold stepF
    rcases hI with h1 | h1
    · rw [max_eq_left (by linarith : t + h / 2 - a ≤ 0),
        max_eq_left (by linarith : t - h / 2 - a ≤ 0), if_neg (by linarith)]
      simp
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ t + h / 2 - a),
        max_eq_right (by linarith : (0 : ℝ) ≤ t - h / 2 - a), if_pos (by linarith)]
      have e : h⁻¹ * (t + h / 2 - a - (t - h / 2 - a)) - 1 = 0 := by field_simp; ring
      rw [e, abs_zero]

lemma integral_tent {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∫ t in Icc (a - h / 2) (a + h / 2), (1 / 2 - |t - a| / h) = h / 4 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hc : Continuous fun t : ℝ => 1 / 2 - |t - a| / h := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in (a - h / 2)..a, (1 / 2 - |t - a| / h) =
      ∫ t in (a - h / 2)..a, (1 / 2 + (t - a) / h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [abs_of_nonpos (by linarith [ht.2])]; ring
  have e2 : ∫ t in a..(a + h / 2), (1 / 2 - |t - a| / h) =
      ∫ t in a..(a + h / 2), (1 / 2 - (t - a) / h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [abs_of_nonneg (by linarith [ht.1])]
  rw [e1, e2]
  simp only [intervalIntegral.integral_comp_sub_right (fun x => 1 / 2 + x / h),
    intervalIntegral.integral_comp_sub_right (fun x => 1 / 2 - x / h)]
  have c1 : ∀ x y : ℝ, IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume x y :=
    fun x y => intervalIntegrable_const
  have c2 : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => t / h) volume x y :=
    fun x y => (continuous_id.div_const h).intervalIntegrable x y
  rw [intervalIntegral.integral_add (c1 _ _) (c2 _ _),
    intervalIntegral.integral_sub (c1 _ _) (c2 _ _)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id,
    smul_eq_mul]
  field_simp
  ring

/-- **(K4)** for the box: `‖bx_h(· - a) - δ_a‖_KR ≤ h/4`. -/
lemma KRn_box_sub_step_le {h : ℝ} (hh : 0 < h) (a : ℝ) :
    KRn (fun t => boxAvg h (stepF a) t - stepF a t) ≤ ENNReal.ofReal (h / 4) := by
  unfold KRn
  set T := (Icc (a - h / 2) (a + h / 2)).indicator (fun t => 1 / 2 - |t - a| / h)
  have hT0 : ∀ t, 0 ≤ T t := fun t => le_trans (abs_nonneg _) (abs_boxAvg_step_sub_le hh a t)
  calc ∫⁻ t, ‖boxAvg h (stepF a) t - stepF a t‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (T t) := by
        refine lintegral_mono fun t => ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_boxAvg_step_sub_le hh a t)
    _ = ENNReal.ofReal (∫ t, T t) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · have hc : Continuous fun t : ℝ => 1 / 2 - |t - a| / h := by fun_prop
          exact (hc.integrableOn_Icc).integrable_indicator measurableSet_Icc
        · exact Filter.Eventually.of_forall hT0
    _ = ENNReal.ofReal (h / 4) := by
        rw [integral_indicator measurableSet_Icc, integral_tent hh]

/-! ## Linearity and regularity of the box average -/

lemma BM.boxAvg {F : ℝ → ℝ} (hF : BM F) {h : ℝ} (hh : 0 < h) : BM (boxAvg h F) := by
  refine ⟨(continuous_boxAvg hF h).measurable, hF.2.choose, fun t => ?_⟩
  have hM := hF.2.choose_spec
  unfold KR.boxAvg
  rw [abs_mul, abs_of_pos (inv_pos.mpr hh)]
  have : |∫ s in (t - h / 2)..(t + h / 2), F s| ≤ hF.2.choose * |t + h / 2 - (t - h / 2)| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t - h / 2) (b := t + h / 2)
      (C := hF.2.choose) (f := F) (fun s _ => by rw [Real.norm_eq_abs]; exact hM s)
    simpa [Real.norm_eq_abs] using this
  have e : |t + h / 2 - (t - h / 2)| = h := by rw [abs_of_pos (by linarith)]; ring
  rw [e] at this
  calc h⁻¹ * |∫ s in (t - h / 2)..(t + h / 2), F s| ≤ h⁻¹ * (hF.2.choose * h) :=
        mul_le_mul_of_nonneg_left this (inv_pos.mpr hh).le
    _ = hF.2.choose := by field_simp

lemma boxAvg_add {F G : ℝ → ℝ} (hF : BM F) (hG : BM G) (h t : ℝ) :
    boxAvg h (fun s => F s + G s) t = boxAvg h F t + boxAvg h G t := by
  unfold boxAvg
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  ring

lemma boxAvg_const_mul (c : ℝ) (F : ℝ → ℝ) (h t : ℝ) :
    boxAvg h (fun s => c * F s) t = c * boxAvg h F t := by
  unfold boxAvg
  rw [intervalIntegral.integral_const_mul]
  ring

lemma boxAvg_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, BM (F i))
    (h t : ℝ) : boxAvg h (fun r => ∑ i ∈ s, F i r) t = ∑ i ∈ s, boxAvg h (F i) t := by
  unfold boxAvg
  rw [intervalIntegral.integral_finset_sum (fun i hi => (hF i hi).intervalIntegrable _ _),
    Finset.mul_sum]

lemma boxAvg_congr {F G : ℝ → ℝ} (hFG : ∀ s, F s = G s) (h t : ℝ) :
    boxAvg h F t = boxAvg h G t := by
  have : F = G := funext hFG
  rw [this]

lemma stepF_mul {w : ℝ} (hw : 0 < w) (a s : ℝ) : stepF (w * a) (w * s) = stepF a s := by
  unfold stepF
  by_cases h : a ≤ s
  · rw [if_pos h, if_pos (mul_le_mul_of_nonneg_left h hw.le)]
  · rw [if_neg h, if_neg (fun h' => h (le_of_mul_le_mul_left h' hw))]

/-- `∫ |∑ F_i| ≤ ∑ ∫ |F_i|`. -/
lemma KRn_sum_le {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, Measurable (F i)) :
    KRn (fun t => ∑ i ∈ s, F i t) ≤ ∑ i ∈ s, KRn (F i) := by
  unfold KRn
  calc ∫⁻ t, ‖∑ i ∈ s, F i t‖ₑ ≤ ∫⁻ t, ∑ i ∈ s, ‖F i t‖ₑ :=
        lintegral_mono fun t => enorm_sum_le _ _
    _ = ∑ i ∈ s, ∫⁻ t, ‖F i t‖ₑ := lintegral_finset_sum _ fun i hi => (hF i hi).enorm

lemma KRn_add_le {F G : ℝ → ℝ} (hF : Measurable F) :
    KRn (fun t => F t + G t) ≤ KRn F + KRn G := by
  unfold KRn
  calc ∫⁻ t, ‖F t + G t‖ₑ ≤ ∫⁻ t, (‖F t‖ₑ + ‖G t‖ₑ) := lintegral_mono fun t => enorm_add_le _ _
    _ = (∫⁻ t, ‖F t‖ₑ) + ∫⁻ t, ‖G t‖ₑ := lintegral_add_left hF.enorm _

lemma KRn_const_mul (c : ℝ) (F : ℝ → ℝ) :
    KRn (fun t => c * F t) = ENNReal.ofReal |c| * KRn F := by
  unfold KRn
  simp_rw [enorm_mul, Real.enorm_eq_ofReal_abs c]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma KRn_neg (F : ℝ → ℝ) : KRn (fun t => -F t) = KRn F := by
  unfold KRn; simp_rw [enorm_neg]
