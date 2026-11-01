module

public import RequestProject.Beurling.LocalPNT.Defs
public import RequestProject.Beurling.LocalPNT.InversionAux

/-!
# §5.7: Laplace/Perron inversion and the Mellin transform of `Π₀`

Analytic tools for Steps 9–10 of the proof of Theorem 5.24 (paper, `04e-lp.tex`).

* `laplace_inversion`: Laplace inversion on a vertical line `Re s = c`, from Fourier inversion.
* `perron_smoothed`: Perron's formula with a smooth weight: for `h` continuous with compact
  support and `ĥ(s) = ∫ h(τ) e^{sτ} dτ`,
  `(1/2π) ∫ ĥ(c + it) x^{c+it}/(c + it) dt = ∫_{τ ≥ -log x} h(τ) dτ`.
* `integral_cpow_pi0Dens`: the Frullani-type Mellin transform
  `∫_1^∞ u^{-s} π₀(u) du = log (s/(s - 1))` for `Re s > 1`.
* The contour shifts `integral_vertical_eq_zero` and `integral_rect_shift_left` live in
  `InversionAux`.
-/

@[expose] public section

open Set Real MeasureTheory Complex Filter Topology
open scoped FourierTransform

namespace LocalPNT

/-! ## Laplace inversion on a vertical line -/

section Laplace

/-- **Laplace inversion.** If `f` is continuous, `f(x) e^{-cx}` is integrable and the Laplace
transform `F(s) = ∫ f(ξ) e^{-sξ} dξ` is integrable on `Re s = c`, then
`f(x) = (1/2π) ∫ F(c + it) e^{(c + it) x} dt`. -/
theorem laplace_inversion {f : ℝ → ℂ} {c : ℝ} (hf : Continuous f)
    (hint : Integrable (fun x : ℝ => f x * Real.exp (-c * x)))
    (hF : Integrable (fun t : ℝ => ∫ x : ℝ, f x * cexp (-((c : ℂ) + t * I) * x))) (x : ℝ) :
    f x = (1 / (2 * Real.pi)) *
      ∫ t : ℝ, (∫ ξ : ℝ, f ξ * cexp (-((c : ℂ) + t * I) * ξ)) * cexp (((c : ℂ) + t * I) * x) := by
  set L : ℝ → ℂ := fun t => ∫ ξ : ℝ, f ξ * cexp (-((c : ℂ) + t * I) * ξ) with hL
  set g : ℝ → ℂ := fun x => f x * (Real.exp (-c * x) : ℂ) with hg
  have h2π : 2 * π ≠ 0 := by positivity
  have hFg : 𝓕 g = fun w => L (2 * π * w) := by
    ext w
    rw [fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hg, smul_eq_mul, ofReal_exp]
    rw [mul_left_comm, ← Complex.exp_add]
    push_cast
    ring_nf
  have hgi : Integrable (𝓕 g) := by
    rw [hFg]
    exact hF.comp_mul_left' h2π
  have hgc : Continuous g := hf.mul (by fun_prop)
  have hinv : g x = ∫ w : ℝ, cexp (↑(2 * π * w * x) * I) * L (2 * π * w) := by
    rw [← congrFun (hgc.fourierInv_fourier_eq hint hgi) x, fourierInv_eq', hFg]
    simp [mul_comm x, mul_assoc]
  have hscale : ∫ w : ℝ, cexp (↑(2 * π * w * x) * I) * L (2 * π * w) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ, cexp (↑(t * x) * I) * L t := by
    have := Measure.integral_comp_mul_left (fun t : ℝ => cexp (↑(t * x) * I) * L t) (2 * π)
    rw [this, abs_of_pos (by positivity), Complex.real_smul]
    push_cast
    rfl
  calc f x = cexp (c * x) * g x := by
        simp only [hg, ofReal_exp]
        rw [mul_left_comm, ← Complex.exp_add]
        push_cast
        ring_nf
        simp
    _ = _ := by
        rw [hinv, hscale, ← mul_assoc, mul_comm (cexp _), mul_assoc, ← integral_const_mul]
        congr 1
        · push_cast; ring
        · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [hL]
          rw [show ((c : ℂ) + t * I) * x = c * x + ↑(t * x) * I by push_cast; ring,
            Complex.exp_add]
          ring

end Laplace

/-! ## The density `π₀` and its Mellin transform -/

section Pi0

theorem pi0Dens_nonneg {u : ℝ} (hu : 1 < u) : 0 ≤ pi0Dens u := by
  have : 1 / u ≤ 1 := (div_le_one (by linarith)).mpr hu.le
  exact div_nonneg (by linarith) (Real.log_pos hu).le

theorem pi0Dens_le_inv_log {u : ℝ} (hu : 1 < u) : pi0Dens u ≤ 1 / Real.log u := by
  have : 0 ≤ 1 / u := by positivity
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hu).le

theorem pi0Dens_le_one {u : ℝ} (hu : 1 < u) : pi0Dens u ≤ 1 := by
  rw [pi0Dens, div_le_one (Real.log_pos hu), one_div]
  exact Real.one_sub_inv_le_log_of_pos (by linarith)

theorem continuousOn_pi0Dens : ContinuousOn pi0Dens (Ioi 1) := by
  intro u hu
  have hu : 1 < u := hu
  exact ((continuousAt_const.sub (continuousAt_const.div continuousAt_id (by simp only [id_eq]; linarith))).div
    (Real.continuousAt_log (by linarith)) (Real.log_pos hu).ne').continuousWithinAt

theorem integrableOn_rpow_mul_pi0Dens {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => u ^ (-σ) * pi0Dens u) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) one_pos).mono' ?_ ?_
  · exact ((continuousOn_id.rpow_const fun u hu => Or.inl (by
      have : (1 : ℝ) < u := hu; simp only [id_eq]; linarith)).mul continuousOn_pi0Dens).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu : 1 < u := hu
    have h0 : 0 ≤ u ^ (-σ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (pi0Dens_nonneg hu))]
    exact mul_le_of_le_one_right h0 (pi0Dens_le_one hu)

theorem integrableOn_cpow_mul_pi0Dens {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s) * (pi0Dens u : ℂ)) (Ioi 1) := by
  refine (integrableOn_rpow_mul_pi0Dens hs).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu : 1 < u := hu
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact continuousAt_ofReal_cpow_const u _ (Or.inr (by linarith))
    · exact continuous_ofReal.continuousAt.comp
        ((continuousOn_pi0Dens u hu).continuousAt (Ioi_mem_nhds hu))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu : 1 < u := hu
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
      Real.norm_of_nonneg (pi0Dens_nonneg hu), neg_re]

/-- `u^{-s} π₀(u) = ∫_0^1 u^{-s-θ} dθ`. -/
theorem cpow_mul_pi0Dens_eq_integral {u : ℝ} (hu : 1 < u) (s : ℂ) :
    (u : ℂ) ^ (-s) * (pi0Dens u : ℂ) = ∫ θ in (0 : ℝ)..1, (u : ℂ) ^ (-s - θ) := by
  have h0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hL : (Real.log u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have key : ∀ θ : ℝ, (u : ℂ) ^ (-s - θ) =
      (u : ℂ) ^ (-s) * cexp (-(Real.log u : ℂ) * θ) := by
    intro θ
    rw [cpow_def_of_ne_zero h0, cpow_def_of_ne_zero h0, ← Complex.exp_add, ofReal_log (by linarith)]
    ring_nf
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hL)]
  have he : cexp (-(Real.log u : ℂ)) = (u : ℂ)⁻¹ := by
    rw [← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log (by linarith), ofReal_inv]
  simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, he, pi0Dens]
  push_cast
  field_simp
  ring

/-- **Frullani-type Mellin transform of `Π₀`**: `∫_1^∞ u^{-s} π₀(u) du = log (s/(s - 1))` for
`Re s > 1`. -/
theorem integral_cpow_pi0Dens {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s) * (pi0Dens u : ℂ) = Complex.log (s / (s - 1)) := by
  -- Fubini on `(1, ∞) × (0, 1]`
  have hprod : Integrable (Function.uncurry fun (u θ : ℝ) => (u : ℂ) ^ (-s - θ))
      ((volume.restrict (Ioi 1)).prod (volume.restrict (Ioc 0 1))) := by
    have hb : Integrable (fun p : ℝ × ℝ => p.1 ^ (-s.re) * (1 : ℝ))
        ((volume.restrict (Ioi 1)).prod (volume.restrict (Ioc 0 1))) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) one_pos).mul_prod
        (integrableOn_const (by simp))
    refine hb.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact (continuous_ofReal.measurable.comp measurable_fst).pow
        (measurable_const.sub (continuous_ofReal.measurable.comp measurable_snd))
    · rw [Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).mpr
        (Eventually.of_forall fun p hp => ?_)
      obtain ⟨hp1, hp2⟩ := hp
      have hp1 : 1 < p.1 := hp1
      simp only [Function.uncurry, mul_one]
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
      refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
      simp only [sub_re, neg_re, ofReal_re]
      linarith [hp2.1]
  have hslit : ∀ θ : ℝ, 0 ≤ θ → s - 1 + θ ∈ slitPlane := fun θ hθ =>
    Or.inl (by simp only [add_re, sub_re, one_re, ofReal_re]; linarith)
  calc ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s) * (pi0Dens u : ℂ)
      = ∫ u in Ioi (1 : ℝ), ∫ θ in Ioc (0 : ℝ) 1, (u : ℂ) ^ (-s - θ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        rw [cpow_mul_pi0Dens_eq_integral hu, intervalIntegral.integral_of_le zero_le_one]
    _ = ∫ θ in Ioc (0 : ℝ) 1, ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s - θ) :=
        integral_integral_swap hprod
    _ = ∫ θ in Ioc (0 : ℝ) 1, 1 / (s - 1 + θ) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [integral_Ioi_cpow_of_lt (by simp only [sub_re, neg_re, ofReal_re]; linarith [hθ.1])
          one_pos, ofReal_one, one_cpow]
        have : -s - θ + 1 = -(s - 1 + θ) := by ring
        rw [this, neg_div_neg_eq]
    _ = ∫ θ in (0 : ℝ)..1, 1 / (s - 1 + θ) := (intervalIntegral.integral_of_le zero_le_one).symm
    _ = Complex.log s - Complex.log (s - 1) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun θ : ℝ => Complex.log (s - 1 + θ))]
        · simp
        · intro θ hθ
          rw [uIcc_of_le zero_le_one] at hθ
          simpa using ((hasDerivAt_id (θ : ℂ)).comp_ofReal.const_add (s - 1)).clog_real
            (hslit θ hθ.1)
        · refine ContinuousOn.intervalIntegrable fun θ hθ => ?_
          rw [uIcc_of_le zero_le_one] at hθ
          exact (continuousAt_const.div (continuousAt_const.add continuous_ofReal.continuousAt)
            (slitPlane_ne_zero (hslit θ hθ.1))).continuousWithinAt
    _ = Complex.log (s / (s - 1)) := by
        have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
        have hs1 : s - 1 ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        have ha : |arg s| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
        have ha1 : |arg (s - 1)| < π / 2 :=
          abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp; linarith))
        have hpi : arg (s - 1) ≠ π := fun h => by
          rw [h, abs_of_pos Real.pi_pos] at ha1; linarith [Real.pi_pos]
        rw [div_eq_mul_inv, (log_mul_eq_add_log_iff hs0 (inv_ne_zero hs1)).mpr,
          log_inv _ hpi, sub_eq_add_neg]
        rw [arg_inv, if_neg hpi]
        constructor <;> linarith [abs_lt.mp ha, abs_lt.mp ha1]

end Pi0

end LocalPNT

end
