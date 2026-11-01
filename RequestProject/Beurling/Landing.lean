module

public import RequestProject.Beurling.Freedman

/-!
# The landing count (Lemma 6.1) from Freedman's inequality

Lemma 6.1 of the paper: take indicators `X_k ∈ {0, 1}` in slot order (`X_k` is
`ℱ_{k+1}`-measurable), with conditional means `p_k = E[X_k | ℱ_k]` whose sum is at most `μ̄`
surely. Then, for `λ > 0`,

  `P(∃ n, |∑_{k<n} (X_k - p_k)| ≥ √(2 μ̄ λ) + 2λ/3) ≤ 2 e^{-λ}`,

which is the first part of the event `Land(J)` in (72) (with `λ = λ_P`). The proof applies
Freedman's inequality (73) with `v = μ̄` and `b = 1` to both tails: the predictable quadratic
variation is `∑ (p_k - p_k²) ≤ ∑ p_k ≤ μ̄`. The second form of (72),
`∑_{k<n} X_k ≤ 2 μ̄ + 7λ/6`, is `landing_count_upper`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

namespace Freedman

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- The conditional mean clipped to `[0, 1]` (a version of `E[X_k | ℱ_k]` for indicators). -/
noncomputable def clipMean (ℱ : Filtration ℕ m0) (μ : Measure Ω) (X : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  max 0 (min 1 ((μ[X k | ℱ k]) ω))

/-- The numerical step: with `a = √(2vλ) + 2λ/3`, `λ ≤ a² / (2v + 2a/3)`. -/
lemma lam_le {v l : ℝ} (hv : 0 < v) (hl : 0 < l) :
    l ≤ (Real.sqrt (2 * v * l) + 2 * l / 3) ^ 2 /
      (2 * v + 2 * (Real.sqrt (2 * v * l) + 2 * l / 3) * 1 / 3) := by
  set s := Real.sqrt (2 * v * l)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * v * l := Real.sq_sqrt (by positivity)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hl.le hs0]

lemma X_bounds {X : ℕ → Ω → ℝ} (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1) (k : ℕ) (ω : Ω) :
    0 ≤ X k ω ∧ X k ω ≤ 1 := by
  rcases hX01 k ω with h | h <;> rw [h] <;> norm_num

lemma integrable_X {X : ℕ → Ω → ℝ} (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) (k : ℕ) : Integrable (X k) μ :=
  Integrable.of_bound ((hmeas k).mono (ℱ.le (k + 1))).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [X_bounds hX01 k ω])

omit [IsProbabilityMeasure μ] in
lemma clipMean_bounds (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ clipMean ℱ μ X k ω ∧ clipMean ℱ μ X k ω ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

omit [IsProbabilityMeasure μ] in
lemma stronglyMeasurable_clipMean (X : ℕ → Ω → ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ k] (clipMean ℱ μ X k) := by
  unfold clipMean
  exact (measurable_const.max (measurable_const.min
    (stronglyMeasurable_condExp (m := ℱ k)).measurable)).stronglyMeasurable

lemma integrable_clipMean (X : ℕ → Ω → ℝ) (k : ℕ) : Integrable (clipMean ℱ μ X k) μ :=
  Integrable.of_bound ((stronglyMeasurable_clipMean X k).mono (ℱ.le k)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω])

lemma clipMean_ae_eq {X : ℕ → Ω → ℝ} (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) (k : ℕ) :
    clipMean ℱ μ X k =ᵐ[μ] μ[X k | ℱ k] := by
  have h0 : 0 ≤ᵐ[μ] μ[X k | ℱ k] :=
    condExp_nonneg (Eventually.of_forall fun ω => (X_bounds hX01 k ω).1)
  have h1 : μ[X k | ℱ k] ≤ᵐ[μ] μ[fun _ => (1 : ℝ) | ℱ k] :=
    condExp_mono (integrable_X hX01 hmeas k) (integrable_const 1)
      (Eventually.of_forall fun ω => (X_bounds hX01 k ω).2)
  rw [condExp_const (ℱ.le k)] at h1
  filter_upwards [h0, h1] with ω e0 e1
  simp only [clipMean, Pi.zero_apply] at e0 e1 ⊢
  rw [min_eq_right e1, max_eq_right e0]

lemma martDiff_landing (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) :
    MartDiff ℱ μ (fun k ω => X k ω - clipMean ℱ μ X k ω) 1 1 where
  meas k := (hmeas k).sub ((stronglyMeasurable_clipMean X k).mono (ℱ.mono (Nat.le_succ k)))
  le_b k ω := by linarith [X_bounds hX01 k ω, clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω]
  bdd k ω := by
    rw [abs_le]
    constructor <;> linarith [X_bounds hX01 k ω, clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω]
  mean_zero k := by
    have e1 := condExp_sub (m := ℱ k) (integrable_X (μ := μ) hX01 hmeas k)
      (integrable_clipMean (ℱ := ℱ) (μ := μ) X k)
    rw [condExp_of_stronglyMeasurable (ℱ.le k) (stronglyMeasurable_clipMean X k)
      (integrable_clipMean X k)] at e1
    filter_upwards [e1, clipMean_ae_eq (μ := μ) hX01 hmeas k] with ω h1 h2
    change (μ[X k - clipMean ℱ μ X k | ℱ k]) ω = 0
    rw [h1, Pi.sub_apply, h2, sub_self]

lemma martDiff_landing_neg (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) :
    MartDiff ℱ μ (fun k ω => -(X k ω - clipMean ℱ μ X k ω)) 1 1 := by
  have h := martDiff_landing (μ := μ) X hX01 hmeas
  refine ⟨fun k => (h.meas k).neg, fun k ω => ?_, fun k ω => by rw [abs_neg]; exact h.bdd k ω,
    fun k => ?_⟩
  · linarith [X_bounds hX01 k ω, clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω]
  · have e := condExp_neg (μ := μ) (fun ω => X k ω - clipMean ℱ μ X k ω) (ℱ k)
    filter_upwards [e, h.mean_zero k] with ω h1 h2
    change (μ[-(fun ω => X k ω - clipMean ℱ μ X k ω) | ℱ k]) ω = 0
    rw [h1, Pi.neg_apply, h2]; simp

lemma condVar_landing_le (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) (k : ℕ) :
    μ[fun ω => (X k ω - clipMean ℱ μ X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] clipMean ℱ μ X k := by
  set c := clipMean ℱ μ X k
  set g : Ω → ℝ := fun ω => 1 - 2 * c ω
  set q : Ω → ℝ := fun ω => c ω ^ 2
  have hc : StronglyMeasurable[ℱ k] c := stronglyMeasurable_clipMean X k
  have hg : StronglyMeasurable[ℱ k] g := (stronglyMeasurable_const.sub (hc.const_mul 2))
  have hq : StronglyMeasurable[ℱ k] q := hc.pow 2
  have hXi := integrable_X (μ := μ) hX01 hmeas k
  have hgX : Integrable (g * X k) μ :=
    Integrable.of_bound (((hg.mono (ℱ.le k)).mul
      ((hmeas k).mono (ℱ.le (k + 1)))).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => by
        have := X_bounds hX01 k ω
        have := clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω
        simp only [Pi.mul_apply, g, Real.norm_eq_abs, abs_mul]
        have h1 : |1 - 2 * c ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have h2 : |X k ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        nlinarith [abs_nonneg (1 - 2 * c ω), abs_nonneg (X k ω)])
  have hqi : Integrable q μ :=
    Integrable.of_bound (hq.mono (ℱ.le k)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        have := clipMean_bounds (ℱ := ℱ) (μ := μ) X k ω
        simp only [q, Real.norm_eq_abs, abs_pow]
        rw [abs_of_nonneg this.1]; nlinarith)
  have heq : (fun ω => (X k ω - c ω) ^ 2) = g * X k + q := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, g, q]
    rcases hX01 k ω with h | h <;> rw [h] <;> ring
  rw [heq]
  have e1 := condExp_add (m := ℱ k) hgX hqi
  have e2 := condExp_mul_of_stronglyMeasurable_left (m := ℱ k) hg hgX hXi
  rw [condExp_of_stronglyMeasurable (ℱ.le k) hq hqi] at e1
  filter_upwards [e1, e2, clipMean_ae_eq (μ := μ) hX01 hmeas k] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, Pi.mul_apply, ← h3]
  simp only [g, q]
  nlinarith [sq_nonneg (c ω)]

lemma V_landing_le (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) {μbar : ℝ}
    (hsum : ∀ᵐ ω ∂μ, ∀ n, ∑ k ∈ range n, (μ[X k | ℱ k]) ω ≤ μbar) :
    ∀ᵐ ω ∂μ, ∀ n, V ℱ μ (fun k ω => X k ω - clipMean ℱ μ X k ω) n ω ≤ μbar := by
  have h1 := ae_all_iff.mpr fun k => condVar_landing_le (μ := μ) X hX01 hmeas k
  have h2 := ae_all_iff.mpr fun k => clipMean_ae_eq (μ := μ) hX01 hmeas k
  filter_upwards [h1, h2, hsum] with ω e1 e2 e3 n
  refine le_trans ?_ (e3 n)
  unfold V
  refine sum_le_sum fun k _ => ?_
  rw [← e2 k]
  exact e1 k

/-- **Lemma 6.1 (landing count), first part of (72)**: for indicators `X_k` (`ℱ_{k+1}`-measurable)
whose conditional means `p_k = E[X_k | ℱ_k]` sum to at most `μ̄` surely, and `λ > 0`,
`P(∃ n, |∑_{k<n} (X_k - p_k)| ≥ √(2 μ̄ λ) + 2λ/3) ≤ 2 e^{-λ}`. -/
theorem landing_count (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) {μbar l : ℝ} (hμ : 0 < μbar)
    (hl : 0 < l) (hsum : ∀ᵐ ω ∂μ, ∀ n, ∑ k ∈ range n, (μ[X k | ℱ k]) ω ≤ μbar) :
    μ.real {ω | ∃ n, Real.sqrt (2 * μbar * l) + 2 * l / 3 ≤
      |∑ k ∈ range n, (X k ω - (μ[X k | ℱ k]) ω)|} ≤ 2 * Real.exp (-l) := by
  set a := Real.sqrt (2 * μbar * l) + 2 * l / 3 with ha_def
  have ha : 0 < a := by positivity
  set ξ : ℕ → Ω → ℝ := fun k ω => X k ω - clipMean ℱ μ X k ω
  set ξ' : ℕ → Ω → ℝ := fun k ω => -(X k ω - clipMean ℱ μ X k ω)
  have hV' : ∀ n ω, V ℱ μ ξ' n ω = V ℱ μ ξ n ω := by
    intro n ω; simp only [V, ξ, ξ', neg_sq]
  have hS' : ∀ n ω, S ξ' n ω = - S ξ n ω := by
    intro n ω; simp only [S, ξ, ξ', sum_neg_distrib]
  set E1 := {ω | ∃ n, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ μbar}
  set E2 := {ω | ∃ n, a ≤ S ξ' n ω ∧ V ℱ μ ξ' n ω ≤ μbar}
  have hsub : ({ω | ∃ n, a ≤ |∑ k ∈ range n, (X k ω - (μ[X k | ℱ k]) ω)|} : Set Ω) ≤ᵐ[μ]
      (E1 ∪ E2 : Set Ω) := by
    have h2 := ae_all_iff.mpr fun k => clipMean_ae_eq (μ := μ) hX01 hmeas k
    filter_upwards [V_landing_le (μ := μ) X hX01 hmeas hsum, h2] with ω hV hc
    intro hω
    obtain ⟨n, hn⟩ := hω
    change ω ∈ E1 ∪ E2
    have hS : ∑ k ∈ range n, (X k ω - (μ[X k | ℱ k]) ω) = S ξ n ω := by
      simp only [S, ξ]; exact sum_congr rfl fun k _ => by rw [hc k]
    rw [hS] at hn
    rcases le_abs'.mp hn with h | h
    · right; exact ⟨n, by rw [hS']; linarith, by rw [hV']; exact hV n⟩
    · left; exact ⟨n, h, hV n⟩
  have hb1 : μ.real E1 ≤ Real.exp (-l) :=
    (freedman_iUnion (martDiff_landing X hX01 hmeas) zero_le_one ha hμ).trans
      (Real.exp_le_exp.mpr (neg_le_neg (lam_le hμ hl)))
  have hb2 : μ.real E2 ≤ Real.exp (-l) :=
    (freedman_iUnion (martDiff_landing_neg X hX01 hmeas) zero_le_one ha hμ).trans
      (Real.exp_le_exp.mpr (neg_le_neg (lam_le hμ hl)))
  calc _ ≤ μ.real (E1 ∪ E2) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ μ.real E1 + μ.real E2 := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-l) := by linarith

/-- **Lemma 6.1, second part of (72)**: under the same hypotheses,
`P(∃ n, ∑_{k<n} X_k > 2 μ̄ + 7λ/6) ≤ 2 e^{-λ}` (from `√(2 μ̄ λ) ≤ μ̄ + λ/2`). -/
theorem landing_count_upper (X : ℕ → Ω → ℝ) (hX01 : ∀ k ω, X k ω = 0 ∨ X k ω = 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) {μbar l : ℝ} (hμ : 0 < μbar)
    (hl : 0 < l) (hsum : ∀ᵐ ω ∂μ, ∀ n, ∑ k ∈ range n, (μ[X k | ℱ k]) ω ≤ μbar) :
    μ.real {ω | ∃ n, 2 * μbar + 7 * l / 6 < ∑ k ∈ range n, X k ω} ≤ 2 * Real.exp (-l) := by
  refine le_trans ?_ (landing_count X hX01 hmeas hμ hl hsum)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [hsum] with ω hω
  intro h
  obtain ⟨n, hn⟩ := h
  change ∃ n, _
  refine ⟨n, ?_⟩
  have hsq : Real.sqrt (2 * μbar * l) ≤ μbar + l / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (μbar - l / 2)]
  have := hω n
  rw [sum_sub_distrib]
  refine le_trans ?_ (le_abs_self _)
  linarith

end Freedman

end
