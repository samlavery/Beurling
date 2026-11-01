module

public import Mathlib

/-!
# The smooth step `ϕ` (Section 3.2, (2)) and its transform `Φ` (Section 4.2)

The paper's `ϕ(t) = ψ(t)/(ψ(t) + ψ(1-t))` with `ψ(t) = e^{-1/t}` (`t > 0`), `ψ = 0` otherwise, is
Mathlib's `Real.smoothTransition`. We prove the properties (2) used in the paper:

* `smoothTransition_one_sub` : `ϕ(1 - t) = 1 - ϕ(t)`;
* `hasDerivAt_smoothTransition` : on `(0,1)`, `ϕ' = e^g (1/t² + 1/(1-t)²)/(1 + e^g)²` where
  `g = 1/t - 1/(1-t)` (equivalently `ϕ' = ϕ(1-ϕ)(1/t² + 1/(1-t)²)`);
* `deriv_smoothTransition_nonneg`, `deriv_smoothTransition_le_two` : `0 ≤ ϕ' ≤ 2`;
* `integral_deriv_smoothTransition` : `∫₀¹ ϕ' = 1`;

and, for `Φ(w) := ∫₀¹ e^{-wv} ϕ'(v) dv` (Section 4.2):

* `phiTransform_zero` : `Φ(0) = 1`;
* `norm_phiTransform_le` : `|Φ(w)| ≤ 1` for `Re w ≥ 0`;
* `re_phiTransform_ge` : `Re Φ(w) ≥ e^{-1} cos 1` for `0 ≤ Re w ≤ 1`, `|Im w| ≤ 1`.
-/

@[expose] public section

open Real Set Filter Topology intervalIntegral

namespace SmoothStep

/-- `ϕ(1 - t) = 1 - ϕ(t)`. -/
lemma smoothTransition_one_sub (t : ℝ) :
    smoothTransition (1 - t) = 1 - smoothTransition t := by
  have h := smoothTransition.pos_denom t
  simp only [smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - t))]
  field_simp
  ring

/-- The exponent `g(t) = 1/t - 1/(1-t)`, so that `ϕ = 1/(1 + e^g)` on `(0,1)`. -/
noncomputable def gExp (t : ℝ) : ℝ := 1 / t - 1 / (1 - t)

/-- The derivative of `ϕ` on `(0,1)`. -/
noncomputable def phiDeriv (t : ℝ) : ℝ :=
  Real.exp (gExp t) * (1 / t ^ 2 + 1 / (1 - t) ^ 2) / (1 + Real.exp (gExp t)) ^ 2

lemma smoothTransition_eq_of_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    smoothTransition t = 1 / (1 + Real.exp (gExp t)) := by
  obtain ⟨h0, h1⟩ := ht
  have e1 : expNegInvGlue t = Real.exp (-t⁻¹) := by
    simp [expNegInvGlue, not_le.mpr h0]
  have e2 : expNegInvGlue (1 - t) = Real.exp (-(1 - t)⁻¹) := by
    simp [expNegInvGlue, not_le.mpr (sub_pos.mpr h1)]
  simp only [smoothTransition, e1, e2, gExp]
  have : Real.exp (1 / t - 1 / (1 - t)) = Real.exp (-(1 - t)⁻¹) / Real.exp (-t⁻¹) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [this]
  have := Real.exp_pos (-t⁻¹)
  field_simp

lemma hasDerivAt_smoothTransition {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt smoothTransition (phiDeriv t) t := by
  obtain ⟨h0, h1⟩ := ht
  have h1' : (1 - t) ≠ 0 := by linarith
  have hg : HasDerivAt gExp (-(1 / t ^ 2 + 1 / (1 - t) ^ 2)) t := by
    have ha : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / t ^ 2)) t := by
      have := hasDerivAt_inv h0.ne'
      simpa [one_div] using this
    have hb : HasDerivAt (fun x : ℝ => 1 / (1 - x)) (1 / (1 - t) ^ 2) t := by
      have := ((hasDerivAt_id t).const_sub 1).inv h1'
      convert! this using 1
      · ext x; simp [one_div]
      · simp
    have := ha.sub hb
    convert! this using 1
    ring
  have hE := hg.exp
  have hden : HasDerivAt (fun x => 1 + Real.exp (gExp x))
      (Real.exp (gExp t) * -(1 / t ^ 2 + 1 / (1 - t) ^ 2)) t := hE.const_add 1
  have hpos : 1 + Real.exp (gExp t) ≠ 0 := by positivity
  have hf := hden.inv hpos
  have hf' : HasDerivAt (fun x => 1 / (1 + Real.exp (gExp x))) (phiDeriv t) t := by
    convert! hf using 1
    · ext x; simp [one_div]
    · unfold phiDeriv; ring
  refine hf'.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h0 h1] with x hx
  exact smoothTransition_eq_of_mem hx

/-- `e^y + e^{-y} ≥ 2 + y²`. -/
lemma two_add_sq_le_exp_add_exp_neg (y : ℝ) : 2 + y ^ 2 ≤ Real.exp y + Real.exp (-y) := by
  have e : Real.exp y + Real.exp (-y) = 2 + (2 * Real.sinh (y / 2)) ^ 2 := by
    rw [Real.sinh_eq]
    have h1 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [h1, h2]; nlinarith [h3]
  rw [e]
  have : (2 * (y / 2)) ^ 2 ≤ (2 * Real.sinh (y / 2)) ^ 2 := by
    rcases le_total 0 y with hy | hy
    · have := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ y / 2)
      nlinarith
    · have := Real.sinh_le_self_iff.mpr (by linarith : y / 2 ≤ 0)
      nlinarith
  nlinarith

lemma phiDeriv_le_two {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : phiDeriv t ≤ 2 := by
  obtain ⟨h0, h1⟩ := ht
  have h1' : 0 < 1 - t := by linarith
  set g := gExp t with hgdef
  set E := Real.exp g with hEdef
  have hEpos : 0 < E := Real.exp_pos g
  have hQ : 1 / t ^ 2 + 1 / (1 - t) ^ 2 ≤ 2 * (4 + g ^ 2) := by
    rw [hgdef, gExp]
    rw [div_add_div _ _ (by positivity) (by positivity), div_sub_div _ _ h0.ne' h1'.ne',
      div_pow, div_le_iff₀ (by positivity)]
    have hs : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hs0 : 0 < t * (1 - t) := by positivity
    field_simp
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 4 * (t * (1 - t)))
      (by linarith : (0:ℝ) ≤ 1 - 2 * (t * (1 - t))), sq_nonneg (t * (1 - t))]
  have hEg : 2 + g ^ 2 ≤ E + E⁻¹ := by
    have := two_add_sq_le_exp_add_exp_neg g
    rwa [Real.exp_neg] at this
  have hkey : E * (4 + g ^ 2) ≤ (1 + E) ^ 2 := by
    have : E * E⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
    nlinarith
  unfold phiDeriv
  rw [← hgdef, ← hEdef, div_le_iff₀ (by positivity)]
  have : 0 ≤ 1 / t ^ 2 + 1 / (1 - t) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hQ hEpos.le]

lemma deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv smoothTransition t :=
  smoothTransition.monotone.deriv_nonneg

lemma continuous_deriv_smoothTransition : Continuous (deriv smoothTransition) :=
  (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

/-- `ϕ' ≤ 2` everywhere (the bound `‖ϕ'‖_∞ ≤ 2` of (2)). -/
theorem deriv_smoothTransition_le_two (t : ℝ) : deriv smoothTransition t ≤ 2 := by
  have hclosed : IsClosed {t : ℝ | deriv smoothTransition t ≤ 2} :=
    isClosed_le continuous_deriv_smoothTransition continuous_const
  have hsub : ({0, 1} : Set ℝ)ᶜ ⊆ {t : ℝ | deriv smoothTransition t ≤ 2} := by
    intro t ht
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at ht
    simp only [mem_setOf_eq]
    rcases lt_or_gt_of_ne ht.1 with h0 | h0
    · have : smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h0] with x hx
        exact smoothTransition.zero_of_nonpos (le_of_lt hx)
      rw [this.deriv_eq]; simp
    · rcases lt_or_gt_of_ne ht.2 with h1 | h1
      · rw [(hasDerivAt_smoothTransition ⟨h0, h1⟩).deriv]
        exact phiDeriv_le_two ⟨h0, h1⟩
      · have : smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds h1] with x hx
          exact smoothTransition.one_of_one_le (le_of_lt hx)
        rw [this.deriv_eq]; simp
  have hdense : Dense ({0, 1} : Set ℝ)ᶜ := (Set.toFinite _).countable.dense_compl ℝ
  have := closure_minimal hsub hclosed
  rw [hdense.closure_eq] at this
  exact this (mem_univ t)

/-- `∫₀¹ ϕ' = 1`. -/
theorem integral_deriv_smoothTransition : ∫ v in (0 : ℝ)..1, deriv smoothTransition v = 1 := by
  rw [integral_deriv_eq_sub (fun x _ => (smoothTransition.contDiff (n := 1)).differentiable
      one_ne_zero x) (continuous_deriv_smoothTransition.intervalIntegrable _ _)]
  simp

/-- `Φ(w) := ∫₀¹ e^{-wv} ϕ'(v) dv` (Section 4.2). -/
noncomputable def phiTransform (w : ℂ) : ℂ :=
  ∫ v in (0 : ℝ)..1, Complex.exp (-w * v) * ((deriv smoothTransition v : ℝ) : ℂ)

lemma continuous_phiIntegrand (w : ℂ) :
    Continuous fun v : ℝ => Complex.exp (-w * v) * ((deriv smoothTransition v : ℝ) : ℂ) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp continuous_deriv_smoothTransition)

theorem phiTransform_zero : phiTransform 0 = 1 := by
  simp only [phiTransform, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal, integral_deriv_smoothTransition]
  simp

theorem norm_phiTransform_le {w : ℂ} (hw : 0 ≤ w.re) : ‖phiTransform w‖ ≤ 1 := by
  unfold phiTransform
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine le_trans ?_ integral_deriv_smoothTransition.le
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((continuous_phiIntegrand w).norm).intervalIntegrable _ _
  · exact continuous_deriv_smoothTransition.intervalIntegrable _ _
  · intro v hv
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (deriv_smoothTransition_nonneg v)]
    have : (-w * (v : ℂ)).re = -(w.re * v) := by simp
    rw [this]
    have h1 : Real.exp (-(w.re * v)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hv.1]
    exact mul_le_of_le_one_left (deriv_smoothTransition_nonneg v) h1

theorem re_phiTransform_ge {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) (him : |w.im| ≤ 1) :
    Real.exp (-1) * Real.cos 1 ≤ (phiTransform w).re := by
  unfold phiTransform
  rw [← Complex.reCLM_apply,
    ← Complex.reCLM.intervalIntegral_comp_comm ((continuous_phiIntegrand w).intervalIntegrable _ _)]
  simp only [Complex.reCLM_apply]
  have hc : Real.exp (-1) * Real.cos 1 =
      ∫ v in (0 : ℝ)..1, Real.exp (-1) * Real.cos 1 * deriv smoothTransition v := by
    rw [intervalIntegral.integral_const_mul, integral_deriv_smoothTransition, mul_one]
  rw [hc]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (continuous_const.mul continuous_deriv_smoothTransition).intervalIntegrable _ _
  · exact (Complex.continuous_re.comp (continuous_phiIntegrand w)).intervalIntegrable _ _
  · intro v hv
    have hre : (Complex.exp (-w * v) * ((deriv smoothTransition v : ℝ) : ℂ)).re =
        Real.exp (-(w.re * v)) * Real.cos (w.im * v) * deriv smoothTransition v := by
      rw [Complex.re_mul_ofReal, Complex.exp_re]
      simp
    rw [hre]
    apply mul_le_mul_of_nonneg_right _ (deriv_smoothTransition_nonneg v)
    have h1 : Real.exp (-1) ≤ Real.exp (-(w.re * v)) := by
      rw [Real.exp_le_exp]; nlinarith [hv.1, hv.2]
    have hcos1 : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three],
      by linarith [Real.pi_gt_three]⟩
    have h2 : Real.cos 1 ≤ Real.cos (w.im * v) := by
      rw [← Real.cos_abs (w.im * v)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
      rw [abs_mul, abs_of_nonneg hv.1]
      nlinarith [abs_nonneg w.im, hv.1, hv.2]
    have := Real.exp_pos (-1)
    nlinarith

end SmoothStep

end
