module

public import Mathlib

/-!
# Lemma 5.3: Abel summation against `S = log + E` with a unimodal weight

For finitely many points `σ_i ∈ [0, L]` with weights `a_i`, put `A(x) = ∑_{σ_i ≤ x} a_i` and
`E(x) = A(x) - x`. If `F ≥ 0` is continuous on `[0, L]`, differentiable off one point `c`,
non-decreasing on `[0, c]` and non-increasing on `[c, L]` (`F' ≥ 0`, resp. `≤ 0`), and
`|E| ≤ K` on `[0, L]`, then (`abel_unimodal`)

  `∑ a_i F(σ_i) = ∫_0^L F + F(L) E(L) - ∫_0^L F' E ≤ ∫_0^L F + 2K F(c)`.

This is the partial summation "main terms" step of the proof of Lemma 5.3, with `F` unimodal so
that `TV(F) ≤ 2 max F`.
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral Set

namespace BSaias

lemma intervalIntegrable_indicator_Ici {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable ((Ici c).indicator f) volume a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.indicator measurableSet_Ici

/-- `∫_0^L 1[x ≥ c] f(x) dx = ∫_c^L f` for `0 ≤ c ≤ L`. -/
lemma integral_indicator_Ici {f : ℝ → ℝ} {L c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ L)
    (hf : IntervalIntegrable f volume 0 L) :
    ∫ x in (0 : ℝ)..L, (Ici c).indicator f x = ∫ x in c..L, f x := by
  have h0c : IntervalIntegrable f volume 0 c := hf.mono_set (by
    rw [uIcc_of_le hc0, uIcc_of_le (hc0.trans hcL)]; exact Icc_subset_Icc le_rfl hcL)
  have hcL' : IntervalIntegrable f volume c L := hf.mono_set (by
    rw [uIcc_of_le hcL, uIcc_of_le (hc0.trans hcL)]; exact Icc_subset_Icc hc0 le_rfl)
  rw [← integral_add_adjacent_intervals (b := c) (intervalIntegrable_indicator_Ici h0c)
    (intervalIntegrable_indicator_Ici hcL')]
  have h1 : ∫ x in (0 : ℝ)..c, (Ici c).indicator f x = 0 := by
    rw [integral_of_le hc0, setIntegral_indicator measurableSet_Ici]
    apply setIntegral_measure_zero
    apply measure_mono_null (t := {c})
    · intro t ht; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici] at ht
      exact le_antisymm ht.1.2 ht.2
    · exact Real.volume_singleton
  have h2 : ∫ x in c..L, (Ici c).indicator f x = ∫ x in c..L, f x := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hcL] at ht
    simp [indicator_of_mem (show t ∈ Ici c from ht.1)]
  rw [h1, h2, zero_add]

/-- FTC on `[a, b]` with one exceptional point. -/
lemma ftc_off_point {F F' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hFc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ≠ c → HasDerivAt F (F' x) x)
    (hi : IntervalIntegrable F' volume a b) : ∫ x in a..b, F' x = F b - F a :=
  integral_eq_of_hasDerivAt_off_countable_of_le F F' hab (countable_singleton c) hFc
    (fun x hx => hd x hx.1 hx.2) hi

/-- **Abel summation with a unimodal weight** (proof of Lemma 5.3, main terms). -/
theorem abel_unimodal {ι : Type*} (s : Finset ι) (a σ : ι → ℝ) {L K c : ℝ} {F F' : ℝ → ℝ}
    (hσ : ∀ i ∈ s, 0 ≤ σ i ∧ σ i ≤ L) (hK : 0 ≤ K)
    (hE : ∀ x ∈ Icc 0 L, |∑ i ∈ s.filter (fun i => σ i ≤ x), a i - x| ≤ K)
    (hc : c ∈ Icc 0 L) (hFc : ContinuousOn F (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, x ≠ c → HasDerivAt F (F' x) x)
    (hi : IntervalIntegrable F' volume 0 L)
    (hup : ∀ x ∈ Ioo 0 c, 0 ≤ F' x) (hdown : ∀ x ∈ Ioo c L, F' x ≤ 0)
    (hF0 : 0 ≤ F 0) (hFL : 0 ≤ F L) :
    ∑ i ∈ s, a i * F (σ i) ≤ (∫ x in (0 : ℝ)..L, F x) + 2 * K * F c := by
  have hL : 0 ≤ L := hc.1.trans hc.2
  set A : ℝ → ℝ := fun x => ∑ i ∈ s.filter (fun i => σ i ≤ x), a i with hA
  -- `F(σ_i) = F(L) - ∫_{σ_i}^L F'`
  have hsub : ∀ {p q : ℝ}, 0 ≤ p → p ≤ q → q ≤ L → ContinuousOn F (Icc p q) ∧
      IntervalIntegrable F' volume p q := by
    intro p q hp hpq hq
    refine ⟨hFc.mono (Icc_subset_Icc hp hq), hi.mono_set ?_⟩
    rw [uIcc_of_le hpq, uIcc_of_le hL]; exact Icc_subset_Icc hp hq
  have hFi : ∀ i ∈ s, F (σ i) = F L - ∫ x in (0 : ℝ)..L, (Ici (σ i)).indicator F' x := by
    intro i hi'
    obtain ⟨h0, h1⟩ := hσ i hi'
    rw [integral_indicator_Ici h0 h1 hi]
    obtain ⟨hc1, hi1⟩ := hsub h0 h1 le_rfl
    rw [ftc_off_point h1 hc1 (fun x hx hxc => hd x ⟨lt_of_le_of_lt h0 hx.1, hx.2⟩ hxc) hi1]
    ring
  have hAF : ∀ x, A x * F' x = ∑ i ∈ s, a i * (Ici (σ i)).indicator F' x := by
    intro x
    simp only [hA, Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : σ i ≤ x
    · simp [h, indicator_of_mem (show x ∈ Ici (σ i) from h)]
    · simp [h, indicator_of_notMem (show x ∉ Ici (σ i) from h)]
  have hAFi : IntervalIntegrable (fun x => A x * F' x) volume 0 L := by
    simp only [hAF]
    have := IntervalIntegrable.sum s fun i _ =>
      (intervalIntegrable_indicator_Ici (c := σ i) hi).const_mul (a i)
    refine this.congr ?_
    intro x _; simp
  have hsum : ∑ i ∈ s, a i * F (σ i) = A L * F L - ∫ x in (0 : ℝ)..L, A x * F' x := by
    rw [Finset.sum_congr rfl (fun i hi' => by rw [hFi i hi']), integral_congr (g := fun x =>
      ∑ i ∈ s, a i * (Ici (σ i)).indicator F' x) (fun x _ => hAF x),
      integral_finset_sum (fun i _ => (intervalIntegrable_indicator_Ici hi).const_mul _)]
    have : A L = ∑ i ∈ s, a i := by
      simp only [hA]; congr 1; ext i; simp only [mem_filter, and_iff_left_iff_imp]
      intro hi'; exact (hσ i hi').2
    rw [this, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]; ring
  -- `∫_0^L x F' = L F(L) - ∫_0^L F`
  have hxF : ∫ x in (0 : ℝ)..L, x * F' x = L * F L - ∫ x in (0 : ℝ)..L, F x := by
    have hFi' : IntervalIntegrable F volume 0 L := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hL]; exact hFc
    have hxFi : IntervalIntegrable (fun x => x * F' x) volume 0 L :=
      hi.continuousOn_mul continuousOn_id
    have := ftc_off_point (F := fun x => x * F x) (F' := fun x => F x + x * F' x) (c := c) hL
      (continuousOn_id.mul hFc) (fun x hx hxc => by
        have := (hasDerivAt_id' x).mul (hd x hx hxc)
        simpa [Pi.mul_def] using this) (hFi'.add hxFi)
    rw [integral_add hFi' hxFi] at this
    simp only [zero_mul, sub_zero] at this
    linarith
  -- the error integral
  set E : ℝ → ℝ := fun x => A x - x with hEdef
  have hxFi : IntervalIntegrable (fun x => x * F' x) volume 0 L :=
    hi.continuousOn_mul continuousOn_id
  have hEFi : IntervalIntegrable (fun x => E x * F' x) volume 0 L := by
    have := hAFi.sub hxFi
    refine this.congr ?_
    intro x _
    simp [E]; ring
  have hmain : ∑ i ∈ s, a i * F (σ i) =
      (∫ x in (0 : ℝ)..L, F x) + E L * F L - ∫ x in (0 : ℝ)..L, E x * F' x := by
    rw [hsum]
    have : ∫ x in (0 : ℝ)..L, E x * F' x =
        (∫ x in (0 : ℝ)..L, A x * F' x) - ∫ x in (0 : ℝ)..L, x * F' x := by
      rw [← integral_sub hAFi hxFi]; congr 1; funext x; simp [E]; ring
    rw [this, hxF]; simp only [E]; ring
  -- bound the error integral on `[0, c]` and `[c, L]`
  have hc0 := hc.1
  have hcL := hc.2
  have hEF0c : IntervalIntegrable (fun x => E x * F' x) volume 0 c := hEFi.mono_set (by
    rw [uIcc_of_le hc0, uIcc_of_le hL]; exact Icc_subset_Icc le_rfl hcL)
  have hEFcL : IntervalIntegrable (fun x => E x * F' x) volume c L := hEFi.mono_set (by
    rw [uIcc_of_le hcL, uIcc_of_le hL]; exact Icc_subset_Icc hc0 le_rfl)
  obtain ⟨hFc1, hi1⟩ := hsub le_rfl hc0 hcL
  obtain ⟨hFc2, hi2⟩ := hsub hc0 hcL le_rfl
  have b1 : -∫ x in (0 : ℝ)..c, E x * F' x ≤ K * (F c - F 0) := by
    rw [← ftc_off_point hc0 hFc1 (fun x hx hxc => hd x ⟨hx.1, lt_of_lt_of_le hx.2 hcL⟩ hxc) hi1,
      ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on_of_le_Ioo hc0 hEF0c.neg (hi1.const_mul K)
    intro x hx
    have h1 := hE x ⟨hx.1.le, (hx.2.trans_le hcL).le⟩
    have h2 := hup x hx
    have : -(E x) ≤ K := by have := neg_abs_le (E x); simp only [E, A] at *; linarith
    show -(E x * F' x) ≤ K * F' x
    nlinarith
  have b2 : -∫ x in c..L, E x * F' x ≤ K * (F c - F L) := by
    have hf := ftc_off_point hcL hFc2 (fun x hx hxc => hd x ⟨lt_of_le_of_lt hc0 hx.1, hx.2⟩ hxc)
      hi2
    have : K * (F c - F L) = ∫ x in c..L, K * (-F' x) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hf]; ring
    rw [this, ← intervalIntegral.integral_neg]
    apply integral_mono_on_of_le_Ioo hcL hEFcL.neg (hi2.neg.const_mul K)
    intro x hx
    have h1 := hE x ⟨(hc0.trans_lt hx.1).le, hx.2.le⟩
    have h2 := hdown x hx
    have : E x ≤ K := by have := le_abs_self (E x); simp only [E, A] at *; linarith
    show -(E x * F' x) ≤ K * -F' x
    nlinarith
  have hsplit : ∫ x in (0 : ℝ)..L, E x * F' x =
      (∫ x in (0 : ℝ)..c, E x * F' x) + ∫ x in c..L, E x * F' x :=
    (integral_add_adjacent_intervals hEF0c hEFcL).symm
  have hEL : E L ≤ K := by
    have := hE L ⟨hL, le_rfl⟩; have := le_abs_self (E L); simp only [E, A] at *; linarith
  rw [hmain, hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hEL hFL, mul_nonneg hK hF0]

end BSaias

end
