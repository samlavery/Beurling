module

public import RequestProject.Beurling.Oscillation
public import RequestProject.Beurling.SmoothStep

/-!
# The Mellin transform of an oscillation (Section 4.2, (17))

For `Re w > 0` and `x⁺ > 0`,

  `∫_{x⁺}^∞ x^{-w-1} ϕ(log(x/x⁺)) dx = (x⁺)^{-w} Φ(w) / w`,

where `Φ(w) = ∫₀¹ e^{-wv} ϕ'(v) dv`. Consequently, for `Re s > θ` and `x⁺ ≥ 1`, the oscillation
`R_k(x) = α x^θ cos(γ log x) ϕ(log(x/x⁺))` has

  `s ∫_1^∞ R_k(x) x^{-s-1} dx = (α s / 2) [ (x⁺)^{-w} Φ(w)/w + (x⁺)^{-w'} Φ(w')/w' ]`,
  `w = s - θ - iγ`, `w' = s - θ + iγ`,

which is (17) (the left side is `∫ x^{-s} dR_k` after partial summation).

Further estimates of Sections 3–4:

* `norm_mellin_oscTerm_le` : `|R̂_k(s)| ≤ (|α| |s|/2) (x⁺)^{θ-σ} (1/|w| + 1/|w'|)` (Section 4.2);
* `norm_tail_mellin_le` : the late-noise estimate of Lemma 4.7,
  `|s ∫_a^∞ D(x) x^{-s-1} dx| ≤ |s| a^{η-σ}/(σ - η)` when `|D(x)| ≤ x^η`;
* `hasDerivAt_oscTerm`, `abs_deriv_oscTerm_le` : the slope bound
  `|R_k'(x)| ≤ |α| x^{θ-1} (|θ| + |γ| + 2)` from the proof of Lemma 3.3.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory intervalIntegral SmoothStep

namespace Oscillation

/-- Integration by parts: `∫₀¹ e^{-wv} ϕ(v) dv = (Φ(w) - e^{-w}) / w`. -/
lemma integral_exp_mul_smooth {w : ℂ} (hw : w ≠ 0) :
    ∫ v in (0 : ℝ)..1, cexp (-w * v) * ((Real.smoothTransition v : ℝ) : ℂ) =
      (phiTransform w - cexp (-w)) / w := by
  have hdiff : ∀ x : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    fun x => ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => ((Real.smoothTransition x : ℝ) : ℂ))
      ((deriv Real.smoothTransition x : ℝ) : ℂ) x := fun x _ => (hdiff x).ofReal_comp
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => -cexp (-w * x) / w)
      (cexp (-w * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -w * (x : ℂ)) (-w) x := by
      simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp.const_mul (-w)
    have := (h1.cexp.neg).div_const w
    convert this using 1
    field_simp
  have hcu : Continuous fun x : ℝ => ((deriv Real.smoothTransition x : ℝ) : ℂ) :=
    continuous_ofReal.comp continuous_deriv_smoothTransition
  have hcv : Continuous fun x : ℝ => cexp (-w * x) :=
    continuous_exp.comp (continuous_const.mul continuous_ofReal)
  have key := integral_mul_deriv_eq_deriv_mul hu hv (hcu.intervalIntegrable _ _)
    (hcv.intervalIntegrable _ _)
  rw [show (fun x : ℝ => cexp (-w * x) * ((Real.smoothTransition x : ℝ) : ℂ)) =
      fun x : ℝ => ((Real.smoothTransition x : ℝ) : ℂ) * cexp (-w * x) from by ext; ring, key]
  have hint : ∫ x in (0 : ℝ)..1, ((deriv Real.smoothTransition x : ℝ) : ℂ) * (-cexp (-w * x) / w) =
      -phiTransform w / w := by
    unfold phiTransform
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_div]
    congr 1; ext x; ring
  rw [hint]
  simp [Real.smoothTransition.one, Real.smoothTransition.zero]
  ring

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = cexp ((Real.log x : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]

lemma continuousOn_cpow_smooth (w : ℂ) {xk : ℝ} (hxk : 0 < xk) :
    ContinuousOn (fun x : ℝ =>
      (x : ℂ) ^ (-w - 1) * ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ)) (Ioi 0) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · exact continuousAt_ofReal_cpow_const x _ (Or.inr (ne_of_gt hx))
  · refine continuous_ofReal.continuousAt.comp ?_
    refine Real.smoothTransition.continuous.continuousAt.comp ?_
    exact (continuousAt_id.div_const xk).log (div_ne_zero (ne_of_gt hx) hxk.ne')

/-- The substitution `x = x⁺ e^v`. -/
lemma integral_cpow_smooth_Icc {w : ℂ} {xk : ℝ} (hxk : 0 < xk) :
    ∫ x in xk..(xk * Real.exp 1),
        (x : ℂ) ^ (-w - 1) * ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ) =
      (xk : ℂ) ^ (-w) * ∫ v in (0 : ℝ)..1, cexp (-w * v) * ((Real.smoothTransition v : ℝ) : ℂ) := by
  have hf : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v => xk * Real.exp v) (xk * Real.exp v) v :=
    fun v _ => (Real.hasDerivAt_exp v).const_mul xk
  have hf' : ContinuousOn (fun v => xk * Real.exp v) (uIcc (0 : ℝ) 1) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  have hg := (continuousOn_cpow_smooth w hxk).mono (show (fun v => xk * Real.exp v) '' uIcc 0 1 ⊆
    Ioi 0 by rintro _ ⟨v, -, rfl⟩; exact mul_pos hxk (Real.exp_pos v))
  have key := integral_comp_smul_deriv' hf hf' hg
  simp only [Real.exp_zero, mul_one] at key
  rw [← key, ← intervalIntegral.integral_const_mul]
  congr 1
  ext v
  have hpos : 0 < xk * Real.exp v := mul_pos hxk (Real.exp_pos v)
  simp only [Function.comp, real_smul]
  rw [show xk * Real.exp v / xk = Real.exp v by field_simp, Real.log_exp,
    ofReal_cpow_eq_exp hpos, ofReal_cpow_eq_exp hxk, Real.log_mul hxk.ne' (Real.exp_pos v).ne',
    Real.log_exp]
  have : ((xk * Real.exp v : ℝ) : ℂ) = cexp ((Real.log xk : ℂ) + v) := by
    rw [Complex.exp_add, ← ofReal_exp, ← ofReal_exp, Real.exp_log hxk, ofReal_mul]
  rw [this]
  push_cast
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma integrableOn_cpow_smooth {w : ℂ} (hw : 0 < w.re) {xk : ℝ} (hxk : 0 < xk) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-w - 1) * ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ)) (Ioi xk) := by
  have hre : (-w - 1).re < -1 := by simp; linarith
  refine Integrable.mono' (integrableOn_Ioi_cpow_of_lt hre hxk).norm ?_ ?_
  · exact ((continuousOn_cpow_smooth w hxk).mono (Ioi_subset_Ioi hxk.le)).aestronglyMeasurable
      measurableSet_Ioi
  · refine Eventually.of_forall fun x => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.smoothTransition.le_one _)

/-- `∫_{x⁺}^∞ x^{-w-1} ϕ(log(x/x⁺)) dx = (x⁺)^{-w} Φ(w)/w` for `Re w > 0`. -/
theorem integral_Ioi_cpow_smooth {w : ℂ} (hw : 0 < w.re) {xk : ℝ} (hxk : 0 < xk) :
    ∫ x in Ioi xk, (x : ℂ) ^ (-w - 1) * ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ) =
      (xk : ℂ) ^ (-w) * phiTransform w / w := by
  set F := fun x : ℝ =>
    (x : ℂ) ^ (-w - 1) * ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ) with hFdef
  set b := xk * Real.exp 1 with hb
  have hxb : xk ≤ b := le_mul_of_one_le_right hxk.le (Real.one_le_exp zero_le_one)
  have hbpos : 0 < b := lt_of_lt_of_le hxk hxb
  have hre : (-w - 1).re < -1 := by simp; linarith
  have hint : IntegrableOn F (Ioi xk) := integrableOn_cpow_smooth hw hxk
  rw [← Ioc_union_Ioi_eq_Ioi hxb, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hxb)),
    ← intervalIntegral.integral_of_le hxb, hFdef, integral_cpow_smooth_Icc hxk,
    integral_exp_mul_smooth (by intro h; rw [h] at hw; simp at hw)]
  have h2 : ∫ x in Ioi b, F x = ∫ x in Ioi b, (x : ℂ) ^ (-w - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : b < x := hx
    have : 1 ≤ Real.log (x / xk) := by
      rw [Real.le_log_iff_exp_le (div_pos (by linarith) hxk), le_div_iff₀ hxk]
      linarith
    simp [hFdef, Real.smoothTransition.one_of_one_le this]
  rw [hFdef] at h2
  rw [h2, integral_Ioi_cpow_of_lt hre hbpos]
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hbw : (b : ℂ) ^ (-w - 1 + 1) = (xk : ℂ) ^ (-w) * cexp (-w) := by
    rw [show -w - 1 + 1 = -w by ring, ofReal_cpow_eq_exp hbpos, ofReal_cpow_eq_exp hxk, hb,
      Real.log_mul hxk.ne' (Real.exp_pos 1).ne', Real.log_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hbw, show -w - 1 + 1 = -w by ring]
  field_simp
  ring

/-- **The Mellin transform (17) of an oscillation**: for `Re s > θ` and `x⁺ ≥ 1`,
`s ∫_1^∞ R_k(x) x^{-s-1} dx = (α s/2) [(x⁺)^{-w} Φ(w)/w + (x⁺)^{-w'} Φ(w')/w']`
with `w = s - θ - iγ`, `w' = s - θ + iγ`. -/
theorem mellin_oscTerm {θ α γ xk : ℝ} (hxk : 1 ≤ xk) {s : ℂ} (hs : θ < s.re) :
    s * ∫ x in Ioi (1 : ℝ), (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1) =
      α * s / 2 * ((xk : ℂ) ^ (-(s - θ - γ * I)) * phiTransform (s - θ - γ * I) / (s - θ - γ * I) +
        (xk : ℂ) ^ (-(s - θ + γ * I)) * phiTransform (s - θ + γ * I) / (s - θ + γ * I)) := by
  have hxk0 : 0 < xk := by linarith
  set w := s - θ - γ * I with hw
  set w' := s - θ + γ * I with hw'
  have hwre : 0 < w.re := by simp [hw]; linarith
  have hw're : 0 < w'.re := by simp [hw']; linarith
  set ϕx := fun x : ℝ => ((Real.smoothTransition (Real.log (x / xk)) : ℝ) : ℂ) with hϕx
  have hpt : ∀ x : ℝ, 0 < x → (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (α / 2 : ℂ) * ((x : ℂ) ^ (-w - 1) * ϕx x + (x : ℂ) ^ (-w' - 1) * ϕx x) := by
    intro x hx
    simp only [oscTerm, hϕx]
    push_cast
    rw [ofReal_cpow hx.le, ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hx,
      ofReal_cpow_eq_exp hx, Complex.cos]
    have e1 : cexp (↑(Real.log x) * (-w - 1)) =
        cexp (↑(Real.log x) * θ) * cexp (↑γ * ↑(Real.log x) * I) *
          cexp (↑(Real.log x) * (-s - 1)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hw]; ring
    have e2 : cexp (↑(Real.log x) * (-w' - 1)) =
        cexp (↑(Real.log x) * θ) * cexp (-(↑γ * ↑(Real.log x)) * I) *
          cexp (↑(Real.log x) * (-s - 1)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hw']; ring
    rw [e1, e2]
    ring
  have hzero : ∫ x in Ioi (1 : ℝ), (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∫ x in Ioi xk, (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1) := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi hxk) fun x hx => ?_
    have hx1 : 1 < x := hx.1
    have hxk' : x ≤ xk := not_lt.mp hx.2
    rw [oscTerm_eq_zero_of_le (by linarith) hxk']
    simp
  have hcongr : ∫ x in Ioi xk, (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∫ x in Ioi xk, (α / 2 : ℂ) * ((x : ℂ) ^ (-w - 1) * ϕx x + (x : ℂ) ^ (-w' - 1) * ϕx x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => hpt x (lt_trans hxk0 hx)
  rw [hzero, hcongr, MeasureTheory.integral_const_mul, integral_add (integrableOn_cpow_smooth hwre hxk0)
    (integrableOn_cpow_smooth hw're hxk0), integral_Ioi_cpow_smooth hwre hxk0,
    integral_Ioi_cpow_smooth hw're hxk0]
  ring

/-- **The size of `R̂_k`** (Section 4.2): with `|Φ| ≤ 1` on `Re w ≥ 0`, for `Re s > θ`, `x⁺ ≥ 1`,
`|s ∫_1^∞ R_k(x) x^{-s-1} dx| ≤ (|α| |s|/2) (x⁺)^{θ-σ} (1/|w| + 1/|w'|)`. -/
theorem norm_mellin_oscTerm_le {θ α γ xk : ℝ} (hxk : 1 ≤ xk) {s : ℂ} (hs : θ < s.re) :
    ‖s * ∫ x in Ioi (1 : ℝ), (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤
      |α| * ‖s‖ / 2 * (xk ^ (θ - s.re) / ‖s - θ - γ * I‖ + xk ^ (θ - s.re) / ‖s - θ + γ * I‖) := by
  rw [mellin_oscTerm hxk hs]
  have hxk0 : 0 < xk := by linarith
  have hterm : ∀ w : ℂ, w.re = s.re - θ →
      ‖(xk : ℂ) ^ (-w) * phiTransform w / w‖ ≤ xk ^ (θ - s.re) / ‖w‖ := by
    intro w hw
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxk0, neg_re, hw, neg_sub]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_of_le_one_right (Real.rpow_nonneg hxk0.le _)
      (norm_phiTransform_le (by rw [hw]; linarith))
  have h1 := hterm (s - θ - γ * I) (by simp)
  have h2 := hterm (s - θ + γ * I) (by simp)
  rw [norm_mul]
  have hn : ‖(α : ℂ) * s / 2‖ = |α| * ‖s‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]; simp
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- **Late noise** (the estimate in Lemma 4.7): if `|D(x)| ≤ x^η` on `(a, ∞)`, `a > 0`, and
`Re s > η`, then `|s ∫_a^∞ D(x) x^{-s-1} dx| ≤ |s| a^{η-σ}/(σ - η)`. -/
theorem norm_tail_mellin_le {D : ℝ → ℝ} {η a : ℝ} (ha : 0 < a)
    (hD : ∀ x > a, |D x| ≤ x ^ η) {s : ℂ} (hs : η < s.re) :
    ‖s * ∫ x in Ioi a, (D x : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (η - s.re) / (s.re - η) := by
  have hlt : η - s.re - 1 < -1 := by linarith
  have hint : IntegrableOn (fun x : ℝ => x ^ (η - s.re - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt hlt ha
  have hbound : ‖∫ x in Ioi a, (D x : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ a ^ (η - s.re) / (s.re - η) := by
    have hval : ∫ x in Ioi a, x ^ (η - s.re - 1) = a ^ (η - s.re) / (s.re - η) := by
      rw [integral_Ioi_rpow_of_lt hlt ha, show η - s.re - 1 + 1 = η - s.re by ring]
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [← hval]
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x (hx : a < x) => ?_)
    have hx0 : 0 < x := lt_trans ha hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have : (-s - 1).re = -s.re - 1 := by simp
    rw [this]
    calc |D x| * x ^ (-s.re - 1) ≤ x ^ η * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hD x hx) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (η - s.re - 1) := by rw [← Real.rpow_add hx0]; ring_nf
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

/-- The derivative of an oscillation `R_k` (for the positivity margin, Lemma 3.3). -/
theorem hasDerivAt_oscTerm {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : 0 < xk) :
    HasDerivAt (oscTerm θ α γ xk)
      (α * x ^ (θ - 1) * (θ * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
        - γ * Real.sin (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
        + Real.cos (γ * Real.log x) * deriv Real.smoothTransition (Real.log (x / xk)))) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ θ) (θ * x ^ (θ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h2 : HasDerivAt (fun y : ℝ => Real.cos (γ * Real.log y))
      (-Real.sin (γ * Real.log x) * (γ * x⁻¹)) x := (hlog.const_mul γ).cos
  have hlog2 : HasDerivAt (fun y : ℝ => Real.log (y / xk)) x⁻¹ x := by
    have := ((hasDerivAt_id x).div_const xk).log (div_ne_zero hx.ne' hxk.ne')
    convert this using 1
    simp only [id]
    field_simp
  have hϕ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (Real.log (x / xk))) (Real.log (x / xk)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h3 := hϕ.comp x hlog2
  have := ((h1.const_mul α).mul h2).mul h3
  unfold oscTerm
  convert this using 1
  have hxθ : x ^ θ = x ^ (θ - 1) * x := by
    rw [← Real.rpow_add_one hx.ne']; ring_nf
  simp only [Function.comp, Pi.mul_apply]
  rw [hxθ]
  field_simp
  ring

/-- **The oscillation slope bound** (proof of Lemma 3.3):
`|R_k'(x)| ≤ |α| x^{θ-1} (|θ| + |γ| + ‖ϕ'‖_∞)` with `‖ϕ'‖_∞ ≤ 2`. -/
theorem abs_deriv_oscTerm_le {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : 0 < xk) :
    |deriv (oscTerm θ α γ xk) x| ≤ |α| * x ^ (θ - 1) * (|θ| + |γ| + 2) := by
  rw [(hasDerivAt_oscTerm hx hxk).deriv, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set c := Real.cos (γ * Real.log x)
  set sn := Real.sin (γ * Real.log x)
  set p := Real.smoothTransition (Real.log (x / xk))
  set d := deriv Real.smoothTransition (Real.log (x / xk))
  have hc : |c| ≤ 1 := Real.abs_cos_le_one _
  have hs : |sn| ≤ 1 := Real.abs_sin_le_one _
  have hp0 : 0 ≤ p := Real.smoothTransition.nonneg _
  have hp1 : p ≤ 1 := Real.smoothTransition.le_one _
  have hd0 : 0 ≤ d := deriv_smoothTransition_nonneg _
  have hd2 : d ≤ 2 := deriv_smoothTransition_le_two _
  have e1 : |θ * c * p| ≤ |θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    calc |θ| * |c| * p ≤ |θ| * 1 * 1 := by gcongr
      _ = |θ| := by ring
  have e2 : |γ * sn * p| ≤ |γ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    calc |γ| * |sn| * p ≤ |γ| * 1 * 1 := by gcongr
      _ = |γ| := by ring
  have e3 : |c * d| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg hd0]
    calc |c| * d ≤ 1 * 2 := by gcongr
      _ = 2 := by ring
  calc |θ * c * p - γ * sn * p + c * d| ≤ |θ * c * p - γ * sn * p| + |c * d| := abs_add_le _ _
    _ ≤ |θ * c * p| + |γ * sn * p| + |c * d| := by gcongr; exact abs_sub _ _
    _ ≤ |θ| + |γ| + 2 := by linarith

end Oscillation

end
