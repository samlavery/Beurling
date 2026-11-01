module

public import RequestProject.Beurling.Construction.Greedy

/-!
# Lemma 6.10: the first failure and the summation of the probability budget

* `compl_goodAll_subset_firstFailure`: if some event fails, the failing event of least time `E`
  fails on `Good(< t(E))`; so `Gᶜ ⊆ ⋃_E (Eᶜ ∩ Good(< t(E)))` (first failure).
* `goodAll_prob_ge_firstFailure`: hence `P(G) ≥ 1 - ∑_E P(Eᶜ ∩ Good(< t(E)))`.
* `budget_sum_le`: the summation of Lemma 6.10. If at the dyadic scale `u = 2^m X₀` the failures
  of the events of Table 1 have total probability (on the good events) at most
  `1.0001 (Λ + m log 2)^{-2} + 3.2 (2^m X₀)^{-2}` (`E1`: `1.0001 L_u^{-2}`; `E2`, `E3 + E3'`, `E4`:
  `u^{-2}`, `1.2 u^{-2}`, `u^{-2}`), then the total is at most
  `1.0001 (Λ^{-2} + (Λ log 2)^{-1}) + 4.3 X₀^{-2} ≤ 1.5/Λ`, `Λ = log X₀ ≥ 10⁸`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Construction

section FirstFailure

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- **First failure**: `Gᶜ ⊆ ⋃_E (Eᶜ ∩ Good(< t(E)))`. -/
theorem compl_goodAll_subset_firstFailure (E : ι → Set Ω) (time : ι → ℕ) :
    (goodAll E)ᶜ ⊆ ⋃ i, (E i)ᶜ ∩ goodBefore E time (time i) := by
  classical
  intro ω hω
  simp only [goodAll, mem_compl_iff, mem_iInter, not_forall] at hω
  -- the least time of a failing event
  have hex : ∃ t, ∃ i, time i = t ∧ ω ∉ E i := by
    obtain ⟨i, hi⟩ := hω; exact ⟨time i, i, rfl, hi⟩
  obtain ⟨i, hi, hfail⟩ := Nat.find_spec hex
  refine mem_iUnion.mpr ⟨i, hfail, ?_⟩
  simp only [goodBefore, mem_iInter]
  intro j hj
  by_contra hjE
  have := Nat.find_min hex (show time j < Nat.find hex by rw [← hi]; exact hj)
  exact this ⟨j, rfl, hjE⟩

/-- **The probability budget by first failure (Lemma 6.10)**: if
`∑_E P(Eᶜ ∩ Good(< t(E))) ≤ c`, then `P(G) ≥ 1 - c`. -/
theorem goodAll_prob_ge_firstFailure [Countable ι] (F : Filtration ℕ mΩ) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : ι → Set Ω} {time : ι → ℕ} (hE : FailureAdapted F E time)
    {c : ℝ} (hc : 0 ≤ c)
    (hsum : ∑' i, μ ((E i)ᶜ ∩ goodBefore E time (time i)) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (1 - c) ≤ μ (goodAll E) := by
  have hm : ∀ i, MeasurableSet (E i) := fun i => F.le (time i) _ (hE i)
  refine GoodEvent.ofReal_one_sub_le (MeasurableSet.iInter hm) hc ?_
  exact (measure_mono (compl_goodAll_subset_firstFailure E time)).trans
    ((measure_iUnion_le _).trans hsum)

/-- Grouping the failure probabilities by dyadic scale. -/
theorem tsum_le_of_scale {f : ι → ENNReal} (scale : ι → ℕ) (b : ℕ → ENNReal)
    (h : ∀ m, ∑' i : {i // scale i = m}, f i ≤ b m) : ∑' i, f i ≤ ∑' m, b m := by
  rw [← (Equiv.sigmaFiberEquiv scale).tsum_eq, ENNReal.tsum_sigma']
  exact ENNReal.tsum_le_tsum fun m => h m

end FirstFailure

/-- `∑_{m < N} (Λ + m a)^{-2} ≤ Λ^{-2} + (aΛ)^{-1}` (telescoping). -/
lemma sum_inv_sq_le {Λ a : ℝ} (hΛ : 0 < Λ) (ha : 0 < a) (N : ℕ) :
    ∑ m ∈ Finset.range N, 1 / (Λ + m * a) ^ 2 ≤ 1 / Λ ^ 2 + 1 / (a * Λ) := by
  -- `∑_{m < N} (Λ + m a)^{-2} ≤ Λ^{-2} + (1/a)(1/Λ - 1/(Λ + (N-1) a))`
  have key : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), 1 / (Λ + m * a) ^ 2 ≤
      1 / Λ ^ 2 + (1 / a) * (1 / Λ - 1 / (Λ + N * a)) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn0 : 0 < Λ + n * a := by positivity
      have hn1 : 0 < Λ + (n + 1 : ℕ) * a := by positivity
      have hstep : 1 / (Λ + (n + 1 : ℕ) * a) ^ 2 ≤
          (1 / a) * (1 / (Λ + n * a) - 1 / (Λ + (n + 1 : ℕ) * a)) := by
        have e : 1 / (Λ + n * a) - 1 / (Λ + (n + 1 : ℕ) * a) =
            a / ((Λ + n * a) * (Λ + (n + 1 : ℕ) * a)) := by
          push_cast; field_simp; ring
        rw [e, show (1 / a) * (a / ((Λ + n * a) * (Λ + (n + 1 : ℕ) * a))) =
          1 / ((Λ + n * a) * (Λ + (n + 1 : ℕ) * a)) by field_simp]
        apply one_div_le_one_div_of_le (by positivity)
        rw [sq]
        apply mul_le_mul_of_nonneg_right _ hn1.le
        push_cast; linarith
      have : (1 / a) * (1 / Λ - 1 / (Λ + n * a)) +
          (1 / a) * (1 / (Λ + n * a) - 1 / (Λ + (n + 1 : ℕ) * a)) =
          (1 / a) * (1 / Λ - 1 / (Λ + (n + 1 : ℕ) * a)) := by ring
      linarith
  rcases N with _ | N
  · simp; positivity
  · refine (key N).trans ?_
    have : 0 ≤ (1 / a) * (1 / (Λ + N * a)) := by positivity
    have e : 1 / (a * Λ) = (1 / a) * (1 / Λ) := by field_simp
    rw [e]; nlinarith

/-- `∑_{m < N} 4^{-m} ≤ 4/3`. -/
lemma sum_inv_four_pow_le (N : ℕ) : ∑ m ∈ Finset.range N, (1 / 4 : ℝ) ^ m ≤ 4 / 3 := by
  have := geom_sum_eq (show (1 / 4 : ℝ) ≠ 1 by norm_num) N
  rw [this]
  have : (0 : ℝ) ≤ (1 / 4) ^ N := by positivity
  have e : ((1 / 4 : ℝ) ^ N - 1) / (1 / 4 - 1) = 4 / 3 * (1 - (1 / 4) ^ N) := by ring
  rw [e]; nlinarith

/-- **The summation of Lemma 6.10**: for `Λ = log X₀ ≥ 10⁸`,
`∑_m (1.0001 (Λ + m log 2)^{-2} + 3.2 (2^m X₀)^{-2}) ≤ 1.5/Λ`. -/
theorem budget_sum_le {X₀ : ℝ} (hX0 : 0 < X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    ∑' m : ℕ, ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 +
      3.2 / (2 ^ m * X₀) ^ 2) ≤ ENNReal.ofReal (1.5 / Real.log X₀) := by
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  -- `X₀ ≥ 100 Λ`
  have hXΛ : 100 * Λ ≤ X₀ := by
    have h := Real.pow_div_factorial_le_exp Λ hΛ0.le 2
    rw [hΛ, Real.exp_log hX0] at h
    simp [Nat.factorial] at h
    nlinarith
  have hX1 : 1 ≤ X₀ := by nlinarith
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_add_distrib]
  have h1 : ∑ m ∈ Finset.range N, 1.0001 / (Λ + m * Real.log 2) ^ 2 ≤
      1.0001 * (1 / Λ ^ 2 + 1 / (Real.log 2 * Λ)) := by
    rw [show ∑ m ∈ Finset.range N, 1.0001 / (Λ + m * Real.log 2) ^ 2 =
      1.0001 * ∑ m ∈ Finset.range N, 1 / (Λ + m * Real.log 2) ^ 2 by
        rw [Finset.mul_sum]; congr 1; ext m; ring]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_le hΛ0 hl2p N) (by norm_num)
  have h2 : ∑ m ∈ Finset.range N, 3.2 / (2 ^ m * X₀) ^ 2 ≤ 3.2 / X₀ ^ 2 * (4 / 3) := by
    rw [show ∑ m ∈ Finset.range N, 3.2 / (2 ^ m * X₀) ^ 2 =
      3.2 / X₀ ^ 2 * ∑ m ∈ Finset.range N, (1 / 4 : ℝ) ^ m by
        rw [Finset.mul_sum]; congr 1; ext m
        have e1 : ((2 : ℝ) ^ m * X₀) ^ 2 = 4 ^ m * X₀ ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num
        rw [e1, one_div_pow]; field_simp]
    exact mul_le_mul_of_nonneg_left (sum_inv_four_pow_le N) (by positivity)
  -- the constants
  have h3 : 1.0001 * (1 / Λ ^ 2 + 1 / (Real.log 2 * Λ)) ≤ 1.4429 / Λ := by
    have e : 1.0001 * (1 / Λ ^ 2 + 1 / (Real.log 2 * Λ)) =
        (1.0001 / Λ + 1.0001 / Real.log 2) / Λ := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hΛ0.le
    have : 1.0001 / Λ ≤ 0.00001 := by
      rw [div_le_iff₀ hΛ0]; linarith
    have : 1.0001 / Real.log 2 ≤ 1.44285 := by
      rw [div_le_iff₀ hl2p]; linarith
    linarith
  have h4 : 3.2 / X₀ ^ 2 * (4 / 3) ≤ 0.05 / Λ := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hΛ0]
    have : X₀ ≤ X₀ ^ 2 := by nlinarith
    nlinarith
  have : 1.4429 / Λ + 0.05 / Λ ≤ 1.5 / Λ := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hΛ0.le
  linarith

/-- The per-scale budget of Table 1: at the dyadic scale `2^m X₀`, the events fail on their good
events with total probability at most `1.0001 (log X₀ + m log 2)^{-2} + 3.2 (2^m X₀)^{-2}`. -/
def TableBudget {Ω ι : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (X₀ : ℝ) (E : ι → Set Ω)
    (time : ι → ℕ) (scale : ι → ℕ) : Prop :=
  ∀ m, ∑' i : {i // scale i = m}, μ ((E i)ᶜ ∩ goodBefore E time (time i)) ≤
    ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 + 3.2 / (2 ^ m * X₀) ^ 2)

/-- **Lemma 6.10 (probability budget)** from the per-scale bounds of Table 1:
`P(G) ≥ 1 - 1.5/log X₀`. -/
theorem goodAll_prob_ge_table {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Countable ι]
    (F : Filtration ℕ mΩ) {μ : Measure Ω} [IsProbabilityMeasure μ] {E : ι → Set Ω}
    {time : ι → ℕ} (hE : FailureAdapted F E time) {X₀ : ℝ} (hX0 : 0 < X₀)
    (hX : 10 ^ 8 ≤ Real.log X₀) {scale : ι → ℕ} (htab : TableBudget μ X₀ E time scale) :
    ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ (goodAll E) := by
  have hΛ0 : 0 < Real.log X₀ := by linarith
  refine goodAll_prob_ge_firstFailure F hE (by positivity) ?_
  exact (tsum_le_of_scale (f := fun i => μ ((E i)ᶜ ∩ goodBefore E time (time i))) scale _
    htab).trans (budget_sum_le hX0 hX)

end Construction

end
