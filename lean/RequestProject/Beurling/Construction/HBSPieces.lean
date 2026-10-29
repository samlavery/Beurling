module

public import RequestProject.Beurling.Construction.RigidFine

/-!
# Local versions of the absorbed-part bound and of Lemma 6.26, and other pieces for (HBS)

* `Absorbed.absorbed_target_error_loc`, `Absorbed.absorbed_target_error_cap_loc`: Lemma 3.4
  (absorbed part) at a height `x`, using the density bound only on `[X₀, x]`.
-/

@[expose] public section

open MeasureTheory Set Real Finset

namespace Absorbed

open scoped Classical

variable {b X₀ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}

theorem absorbed_target_error_loc (h : AbsorbedWindowHyp b X₀ A u) {ε : ℝ}
    {x : ℝ} (hx : X₀ ≤ x)
    (hρ : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensity b A u v ≤ ε) :
    |countA A x - ∫ v in X₀..x, absorbedDensity b A u v| ≤ ε * x ^ b := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hx0 : 0 < x := by linarith
  set S := below h.fin (2 * x)
  have hε : 0 ≤ ε := by
    refine le_trans ?_ (hρ X₀ le_rfl hx)
    rw [absorbedDensity_eq_sum h le_rfl hx]
    exact Finset.sum_nonneg fun a _ => absorbedBump_nonneg hX0 le_rfl
  have hint := fun a => intervalIntegrable_absorbedBump h a hx
  have hU : uIcc X₀ x = Icc X₀ x := uIcc_of_le hx
  -- the integral of the density is the sum of the integrals of the bumps
  have hρsum : ∫ v in X₀..x, absorbedDensity b A u v =
      ∑ a ∈ S, ∫ v in X₀..x, absorbedBump b A u a v := by
    rw [← intervalIntegral.integral_finset_sum fun a _ => hint a]
    apply intervalIntegral.integral_congr
    intro v hv; rw [hU] at hv
    exact absorbedDensity_eq_sum h hv.1 hv.2
  have hdiff : countA A x - ∫ v in X₀..x, absorbedDensity b A u v =
      ∑ a ∈ S, ((if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) -
        ∫ v in X₀..x, absorbedBump b A u a v) := by
    rw [hρsum, countA_eq_sum h hx, Finset.sum_sub_distrib]
  have hcont : ContinuousOn (fun v : ℝ => v ^ (b - 1)) (uIcc X₀ x) := by
    intro v hv; rw [hU] at hv
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  -- upper bound
  have hup : countA A x - ∫ v in X₀..x, absorbedDensity b A u v ≤ ε * x ^ b := by
    rw [hdiff]
    refine le_trans (Finset.sum_le_sum fun a _ => bump_upper h a hx) ?_
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum fun a _ =>
      (hint a).mul_continuousOn hcont]
    have hle : ∫ v in X₀..x, ∑ a ∈ S, absorbedBump b A u a v * v ^ (b - 1) ≤
        ∫ v in X₀..x, ε * v ^ (b - 1) := by
      apply intervalIntegral.integral_mono_on hx
      · have := IntervalIntegrable.sum S fun a _ => (hint a).mul_continuousOn hcont
        convert this using 1; ext v; simp [Finset.sum_apply]
      · exact (hcont.intervalIntegrable).const_mul ε
      · intro v hv
        rw [← Finset.sum_mul, ← absorbedDensity_eq_sum h hv.1 hv.2]
        exact mul_le_mul_of_nonneg_right (hρ v hv.1 hv.2)
          (Real.rpow_nonneg (by linarith [hv.1]) _)
    have hcalc : ∫ v in X₀..x, ε * v ^ (b - 1) = ε * ((x ^ b - X₀ ^ b) / b) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith [h.b_pos]))]
      simp
    have hb := h.b_pos
    calc b * ∫ v in X₀..x, ∑ a ∈ S, absorbedBump b A u a v * v ^ (b - 1)
        ≤ b * (ε * ((x ^ b - X₀ ^ b) / b)) := by
          rw [← hcalc]; exact mul_le_mul_of_nonneg_left hle hb.le
      _ = ε * (x ^ b - X₀ ^ b) := by field_simp
      _ ≤ ε * x ^ b := by
          have := Real.rpow_nonneg hX0.le b
          nlinarith
  -- lower bound
  have hlo : -(ε * x ^ b) ≤ countA A x - ∫ v in X₀..x, absorbedDensity b A u v := by
    rw [hdiff]
    refine le_trans ?_ (Finset.sum_le_sum fun a _ => bump_lower h a hx)
    rw [Finset.sum_neg_distrib, neg_le_neg_iff,
      ← intervalIntegral.integral_finset_sum fun a _ => ?_]
    · have hcongr : ∫ v in X₀..x, ∑ a ∈ S, (Ioi (x - x ^ b)).indicator (absorbedBump b A u a) v =
          ∫ v in X₀..x, (Ioi (x - x ^ b)).indicator (absorbedDensity b A u) v := by
        apply intervalIntegral.integral_congr
        intro v hv; rw [hU] at hv
        simp only [Set.indicator_apply]
        split_ifs
        · exact (absorbedDensity_eq_sum h hv.1 hv.2).symm
        · simp
      rw [hcongr]
      apply integral_window_le hx (Real.rpow_nonneg hx0.le _) hε
      · refine (IntervalIntegrable.sum S fun a _ => hint a).congr ?_
        intro v hv
        rw [uIoc_of_le hx] at hv
        simp only [Finset.sum_apply]
        exact (absorbedDensity_eq_sum h hv.1.le hv.2).symm
      · intro v hv; exact hρ v hv.1 hv.2
    · have ha := hint a
      rw [intervalIntegrable_iff] at ha ⊢
      exact ha.indicator measurableSet_Ioi
  exact abs_le.mpr ⟨hlo, hup⟩


/-- **Lemma 3.4, absorbed part, capped density, local version**: with `ρ_A(v) ≤ (log v)^{-4}` on
`[X₀, x]` and `log X₀ ≥ 3`, `|#(A ∩ [1, x]) - ∫_{X₀}^x ρ̄_A| ≤ 2 x^b`. -/
theorem absorbed_target_error_cap_loc (h : AbsorbedWindowHyp b X₀ A u)
    (hlog : 3 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x)
    (hρ : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensity b A u v ≤ (Real.log v) ^ (-4 : ℤ)) :
    |countA A x - ∫ v in X₀..x, absorbedDensityCap b A u v| ≤ 2 * x ^ b := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hlogv : ∀ v ≥ X₀, Real.log X₀ ≤ Real.log v := fun v hv => Real.log_le_log hX0 hv
  have hcap : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensityCap b A u v = absorbedDensity b A u v := by
    intro v hv hvx
    have hl : 3 ≤ Real.log v := hlog.trans (hlogv v hv)
    apply min_eq_left
    refine (hρ v hv hvx).trans ?_
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    have hl0 : 0 < Real.log v := by linarith
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : 0.1 / Real.log v * Real.log v ^ 4 = 0.1 * Real.log v ^ 3 := by
      field_simp
    rw [this]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hl 3]
  have hint : ∫ v in X₀..x, absorbedDensityCap b A u v =
      ∫ v in X₀..x, absorbedDensity b A u v := by
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le hx] at hv
    exact hcap v hv.1 hv.2
  rw [hint]
  have hL0 : 0 < Real.log X₀ := by linarith
  have hε : (Real.log X₀) ^ (-4 : ℤ) ≤ 2 := by
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    have : 1 ≤ Real.log X₀ ^ 4 := one_le_pow₀ (by linarith)
    calc (Real.log X₀ ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      _ ≤ 2 := by norm_num
  refine le_trans (absorbed_target_error_loc h (ε := (Real.log X₀) ^ (-4 : ℤ)) hx ?_) ?_
  · intro v hv hvx
    refine (hρ v hv hvx).trans ?_
    rw [zpow_neg, zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hL0.le (hlogv v hv) 4)
  · exact mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg (by linarith) _)

end Absorbed

end
