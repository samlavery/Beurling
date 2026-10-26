module

public import RequestProject.Beurling.Decomp.Mellin
public import RequestProject.Beurling.OscBounds

/-!
# The transform of the oscillation

For switch-on points with `x⁺_{k+1} ≥ exp(x⁺_k)` and bounded amplitudes, the oscillation
`R = ∑_k R_k` of (1) has transform `s ∫_1^∞ R(x) x^{-s-1} dx = ∑_k R̂_k(s)` for `σ > θ ≥ 0`
(`mellin_osc`): the series may be integrated term by term, since `|R_k(x)| ≤ |α_k| x^θ` vanishes
below `x⁺_k ≥ 2^k`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Remark12 Oscillation DesignedZero

namespace Decomp

lemma Spacing.two_pow_le {xp : ℕ → ℝ} (h : Spacing xp) (k : ℕ) : (2 : ℝ) ^ k ≤ xp k := by
  induction k with
  | zero => simpa using h.one_le
  | succ k ih =>
    have h0 : 0 ≤ xp k := le_trans (by positivity) ih
    have h1 : 2 * xp k ≤ Real.exp (xp k) := by
      have := Real.quadratic_le_exp_of_nonneg h0
      nlinarith [sq_nonneg (xp k - 1)]
    rw [pow_succ]
    linarith [h.exp_le k]

lemma measurable_oscTerm (θ α γ xp : ℝ) : Measurable (oscTerm θ α γ xp) := by
  unfold oscTerm
  have hs : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  refine Measurable.mul (Measurable.mul (Measurable.mul measurable_const
    (measurable_id.pow_const θ)) (Real.measurable_cos.comp
      (measurable_const.mul Real.measurable_log))) ?_
  exact hs.measurable.comp (Real.measurable_log.comp (measurable_id.div_const xp))

lemma abs_oscTerm_le {θ α γ xp x : ℝ} (hx : 0 < x) :
    |oscTerm θ α γ xp x| ≤ if xp ≤ x then |α| * x ^ θ else 0 := by
  split_ifs with h
  · unfold oscTerm
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le θ)]
    have h1 : |Real.cos (γ * Real.log x)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.smoothTransition (Real.log (x / xp))| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have h3 : 0 ≤ |α| * x ^ θ := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.le θ)
    calc |α| * x ^ θ * |Real.cos (γ * Real.log x)| * |Real.smoothTransition (Real.log (x / xp))|
        ≤ |α| * x ^ θ * 1 * 1 := by gcongr
      _ = |α| * x ^ θ := by ring
  · push_neg at h
    rw [oscTerm_eq_zero_of_le hx h.le, abs_zero]

/-- **The transform of the oscillation**: for `θ < σ`, `|α_k| ≤ C` and switch-on points with
`x⁺_{k+1} ≥ exp(x⁺_k)`, `s ∫_1^∞ R(x) x^{-s-1} dx = ∑_k R̂_k(s)` (with the integrand integrable). -/
theorem mellin_osc {θ : ℝ} {α γ xp : ℕ → ℝ} (hsp : Spacing xp) {C : ℝ}
    (hα : ∀ k, |α k| ≤ C) {s : ℂ} (hs : θ < s.re) :
    IntegrableOn (fun x : ℝ => (osc θ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (osc θ α γ xp) s = ∑' k, oscHat θ (α k) (γ k) (xp k) s := by
  set σ := s.re
  set δ := σ - θ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hα 0)
  set f : ℕ → ℝ → ℂ := fun k x =>
    (oscTerm θ (α k) (γ k) (xp k) x : ℂ) * (x : ℂ) ^ (-s - 1) with hf
  have hfm : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (Ioi 1)) := fun k =>
    ((Complex.measurable_ofReal.comp (measurable_oscTerm _ _ _ _)).mul
      ((Complex.measurable_ofReal).pow_const _)).aestronglyMeasurable
  -- pointwise bound
  have hfb : ∀ k, ∀ x ∈ Ioi (1 : ℝ),
      ‖f k x‖ ≤ C * (if xp k ≤ x then x ^ (-δ - 1) else 0) := by
    intro k x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -σ - 1 := by simp [σ]
    rw [hre]
    have hb := abs_oscTerm_le (θ := θ) (α := α k) (γ := γ k) (xp := xp k) hx0
    have hxs : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    split_ifs at hb ⊢ with h
    · calc |oscTerm θ (α k) (γ k) (xp k) x| * x ^ (-σ - 1) ≤ |α k| * x ^ θ * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right hb hxs
        _ ≤ C * x ^ θ * x ^ (-σ - 1) := by gcongr; exact hα k
        _ = C * x ^ (-δ - 1) := by
            rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; rw [hδ]; ring
    · have : |oscTerm θ (α k) (γ k) (xp k) x| = 0 := le_antisymm hb (abs_nonneg _)
      rw [this]; simp
  -- summable bound for the integrals of the norms
  have hlin : ∀ k, ∫⁻ x in Ioi (1 : ℝ), ‖f k x‖ₑ ≤
      ENNReal.ofReal (C * (xp k ^ (-δ) / δ)) := by
    intro k
    have hT : 1 ≤ xp k := hsp.one_le_all k
    calc ∫⁻ x in Ioi (1 : ℝ), ‖f k x‖ₑ
        ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (C * (if xp k ≤ x then x ^ (-δ - 1) else 0)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hfb k x hx)
      _ = ENNReal.ofReal (C * (xp k ^ (-δ) / δ)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · rw [integral_const_mul, AbelMellin.integral_ite_rpow hT hδ0]
          · refine Integrable.const_mul ?_ C
            refine Integrable.mono' (g := fun x => x ^ (-δ - 1))
              (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
              ((Measurable.ite measurableSet_Ici (by fun_prop)
                measurable_const).aestronglyMeasurable) ?_
            refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
            have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
            have := Real.rpow_nonneg hx0.le (-δ - 1)
            split_ifs <;> simp [abs_of_nonneg this, this]
          · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
            have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
            have := Real.rpow_nonneg hx0.le (-δ - 1)
            simp only [Pi.zero_apply]
            split_ifs <;> positivity
  have hsumm : Summable fun k => C * (xp k ^ (-δ) / δ) := by
    have hg : Summable fun k : ℕ => ((2 : ℝ) ^ (-δ)) ^ k :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) ((hg.div_const δ).mul_left C)
    · have := hsp.one_le_all k
      exact mul_nonneg hC (div_nonneg (Real.rpow_nonneg (by linarith) _) hδ0.le)
    · have h1 : xp k ^ (-δ) ≤ ((2 : ℝ) ^ (-δ)) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (Spacing.two_pow_le hsp k)
          (by linarith)
      gcongr
  have hfin : ∑' k, ∫⁻ x in Ioi (1 : ℝ), ‖f k x‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlin)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) hsumm]
    · exact ENNReal.ofReal_ne_top
    · have := hsp.one_le_all k
      exact mul_nonneg hC (div_nonneg (Real.rpow_nonneg (by linarith) _) hδ0.le)
  have heq : (fun x : ℝ => (osc θ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ∑' k, f k x := by
    funext x
    simp only [hf, osc]
    rw [Complex.ofReal_tsum, tsum_mul_right]
  refine ⟨heq ▸ integrable_tsum_of_lintegral f hfm hfin, ?_⟩
  unfold tailMellin
  rw [heq, integral_tsum hfm hfin, ← tsum_mul_left]
  rfl

end Decomp

end
