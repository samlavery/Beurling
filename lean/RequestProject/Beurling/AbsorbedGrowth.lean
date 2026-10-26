module

public import RequestProject.Beurling.AbsorbedPart

/-!
# The `1/16` requirement on the absorbed set from a growth condition

The inputs of Theorem 4.10 ask that the explicit bound of Lemma 4.4(a) be at most `1/16`:
`absorbedBound ς δ Y ≤ 1/16`. Here (`absorbedBound_le_of_growth`) this is derived from the growth
condition

  `δ ℓ + 2 log(2 + ℓ) + 5 ≤ ς(ℓ)` for `0 ≤ ℓ ≤ log Y`

on the exponent `ς` of the counting bound `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}`. (In the paper,
`ς = ς_*` of Lemma 6.26 and `δ = δ_k`; the paper checks the needed smallness by splitting the range
at `v_0` and `V = e^{ℓ_std}`.) The two terms of `absorbedBound` are bounded by `e^{-5}/4` and
`e^{-5} ∫_1^Y dv/(v (2 + log v)²) ≤ e^{-5}/2`.
-/

@[expose] public section

open Set MeasureTheory

namespace Absorbed

lemma hasDerivAt_inv_two_add_log {v : ℝ} (hv : 1 ≤ v) :
    HasDerivAt (fun v : ℝ => -(2 + Real.log v)⁻¹) (v⁻¹ * ((2 + Real.log v) ^ 2)⁻¹) v := by
  have hv0 : v ≠ 0 := by positivity
  have hl : 0 ≤ Real.log v := Real.log_nonneg hv
  have h1 : HasDerivAt (fun v : ℝ => 2 + Real.log v) v⁻¹ v :=
    (Real.hasDerivAt_log hv0).const_add 2
  have h2 := (h1.inv (by positivity)).neg
  convert h2 using 1
  field_simp

/-- **The `1/16` requirement from a growth condition on `ς`.** -/
theorem absorbedBound_le_of_growth {ς : ℝ → ℝ} (hς : Monotone ς) {δ Y : ℝ} (hδ : 0 ≤ δ)
    (hY : 1 ≤ Y)
    (hg : ∀ ℓ ∈ Icc 0 (Real.log Y), δ * ℓ + 2 * Real.log (2 + ℓ) + 5 ≤ ς ℓ) :
    absorbedBound ς δ Y ≤ 1 / 16 := by
  have hY0 : 0 < Y := by linarith
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hpt : ∀ ℓ ∈ Icc 0 (Real.log Y),
      Real.exp (δ * ℓ - ς ℓ) ≤ Real.exp (-5) * ((2 + ℓ) ^ 2)⁻¹ := by
    intro ℓ hℓ
    have h := hg ℓ hℓ
    have h2 : 0 < 2 + ℓ := by linarith [hℓ.1]
    calc Real.exp (δ * ℓ - ς ℓ) ≤ Real.exp (-5 - 2 * Real.log (2 + ℓ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-5) * ((2 + ℓ) ^ 2)⁻¹ := by
          have e2 : Real.exp (-(2 * Real.log (2 + ℓ))) = ((2 + ℓ) ^ 2)⁻¹ := by
            rw [Real.exp_neg, show 2 * Real.log (2 + ℓ) = Real.log ((2 + ℓ) ^ 2) by
              rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
          rw [sub_eq_add_neg, Real.exp_add, e2]
  -- the boundary term
  have hT1 : Y ^ δ * Real.exp (-ς (Real.log Y)) ≤ Real.exp (-5) / 4 := by
    have e : Y ^ δ * Real.exp (-ς (Real.log Y)) = Real.exp (δ * Real.log Y - ς (Real.log Y)) := by
      rw [Real.rpow_def_of_pos hY0, ← Real.exp_add]; ring_nf
    rw [e]
    refine (hpt _ ⟨hlY, le_rfl⟩).trans ?_
    have : ((2 + Real.log Y) ^ 2)⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have := Real.exp_pos (-5)
    nlinarith
  -- the integral
  have hI : ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤ Real.exp (-5) / 2 := by
    have hmono : ∀ v ∈ Icc (1 : ℝ) Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤
        Real.exp (-5) * (v⁻¹ * ((2 + Real.log v) ^ 2)⁻¹) := by
      intro v hv
      have hv0 : 0 < v := by linarith [hv.1]
      have hl : Real.log v ∈ Icc 0 (Real.log Y) :=
        ⟨Real.log_nonneg hv.1, Real.log_le_log hv0 hv.2⟩
      have e : v ^ (δ - 1) * Real.exp (-ς (Real.log v)) =
          v⁻¹ * Real.exp (δ * Real.log v - ς (Real.log v)) := by
        rw [Real.rpow_def_of_pos hv0, ← Real.exp_log hv0]
        rw [Real.log_exp, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [e]
      have := hpt _ hl
      have hvi : 0 ≤ v⁻¹ := by positivity
      calc v⁻¹ * Real.exp (δ * Real.log v - ς (Real.log v)) ≤
          v⁻¹ * (Real.exp (-5) * ((2 + Real.log v) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left this hvi
        _ = _ := by ring
    have hderiv : ∀ x ∈ uIcc (1 : ℝ) Y, HasDerivAt (fun v : ℝ => -(2 + Real.log v)⁻¹)
        (x⁻¹ * ((2 + Real.log x) ^ 2)⁻¹) x := by
      intro x hx
      rw [uIcc_of_le hY] at hx
      exact hasDerivAt_inv_two_add_log hx.1
    have hcont : ContinuousOn (fun x : ℝ => x⁻¹ * ((2 + Real.log x) ^ 2)⁻¹) (uIcc 1 Y) := by
      rw [uIcc_of_le hY]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx.1
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul (continuousAt_inv₀ hx0)
      apply ContinuousAt.inv₀ _ (by positivity)
      exact (continuousAt_const.add (Real.continuousAt_log hx0)).pow 2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable)
    have hlhs : IntervalIntegrable (fun v : ℝ => v ^ (δ - 1) * Real.exp (-ς (Real.log v)))
        volume 1 Y := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
      refine integrableOn_Ioc_of_bdd (C := Y ^ δ * Real.exp (-ς 0))
        (measurable_rpow_mul_exp hς) fun v hv => ?_
      have hv1 : 1 ≤ v := hv.1.le
      rw [abs_of_nonneg (by positivity)]
      have h1 : v ^ (δ - 1) ≤ Y ^ δ :=
        (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)).trans
          (Real.rpow_le_rpow (by linarith) hv.2 hδ)
      have : Real.exp (-ς (Real.log v)) ≤ Real.exp (-ς 0) := by
        rw [Real.exp_le_exp]; have := hς (Real.log_nonneg hv1); linarith
      have : 0 ≤ Real.exp (-ς (Real.log v)) := by positivity
      have : 0 ≤ v ^ (δ - 1) := by positivity
      nlinarith
    calc ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v))
        ≤ ∫ v in (1 : ℝ)..Y, Real.exp (-5) * (v⁻¹ * ((2 + Real.log v) ^ 2)⁻¹) :=
          intervalIntegral.integral_mono_on hY hlhs
            (hcont.intervalIntegrable.const_mul _) hmono
      _ = Real.exp (-5) * (-(2 + Real.log Y)⁻¹ - -(2 + Real.log 1)⁻¹) := by
          rw [intervalIntegral.integral_const_mul, hFTC]
      _ ≤ Real.exp (-5) / 2 := by
          rw [Real.log_one]
          have : 0 < (2 + Real.log Y)⁻¹ := by positivity
          have := Real.exp_pos (-5)
          nlinarith
  have he : Real.exp (-5) ≤ 1 / 100 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    norm_num at this ⊢; linarith
  have hT0 : 0 ≤ Y ^ δ * Real.exp (-ς (Real.log Y)) := by positivity
  unfold absorbedBound
  nlinarith

end Absorbed

end
