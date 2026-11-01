module

public import RequestProject.BSCert.Transc

/-!
# The exponential integral `Ei` and `Ein`

The paper (proof of Lemma 6.22(c)) uses `Ein(x) := ∫₀ˣ (eʷ - 1)/w dw` and the exponential
integral `Ei`.  Mathlib has neither, so we define them here:
* `Ein x := ∫ w in 0..x, (exp w - 1)/w` (the paper's definition);
* `Ei x := γ + log x + Ein x`, which for `x > 0` is the classical identity for the
  principal-value integral `Ei(x) = PV ∫_{-∞}^x eᵗ/t dt` (`γ` is Euler's constant).

We prove polynomial enclosures of `Ein` (from the Taylor series of `exp`) and the derivative
`Ei'(x) = eˣ/x` for `x > 0`.
-/

@[expose] public section

namespace BSCert.EiFn

open Real Finset intervalIntegral MeasureTheory

/-- `Ein(x) = ∫₀ˣ (eʷ - 1)/w dw`. -/
noncomputable def Ein (x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, (Real.exp w - 1) / w

/-- The exponential integral, `Ei(x) = γ + log x + Ein(x)` (meaningful for `x > 0`). -/
noncomputable def Ei (x : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log x + Ein x

/-! ## Pointwise bounds for the integrand -/

lemma integrand_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ (Real.exp w - 1) / w := by
  have := Real.add_one_le_exp w
  apply div_nonneg _ hw.le
  linarith

lemma integrand_le_exp {w : ℝ} (hw : 0 < w) : (Real.exp w - 1) / w ≤ Real.exp w := by
  rw [div_le_iff₀ hw]
  have h := Real.add_one_le_exp (-w)
  have he : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos w
  nlinarith

/-- The lower polynomial: `∑_{k<K} wᵏ/(k+1)!`. -/
noncomputable def lowPoly (K : ℕ) (w : ℝ) : ℝ := ∑ k ∈ range K, w ^ k / ((k + 1).factorial : ℝ)

lemma lowPoly_le {w : ℝ} (hw : 0 < w) (K : ℕ) : lowPoly K w ≤ (Real.exp w - 1) / w := by
  have h := Real.sum_le_exp_of_nonneg hw.le (K + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  rw [le_div_iff₀ hw]
  unfold lowPoly
  rw [Finset.sum_mul]
  have : ∀ k ∈ range K, w ^ k / ((k + 1).factorial : ℝ) * w = w ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    intro k _; ring
  rw [Finset.sum_congr rfl this]
  linarith

/-- Real form of `Complex.exp_bound'`. -/
lemma real_exp_bound' {x : ℝ} {n : ℕ} (hx : |x| / n.succ ≤ 1 / 2) :
    |Real.exp x - ∑ m ∈ range n, x ^ m / m.factorial| ≤ |x| ^ n / n.factorial * 2 := by
  have h := Complex.exp_bound' (x := (x : ℂ)) (n := n) (by simpa [Complex.norm_real] using hx)
  have e : Complex.exp (x : ℂ) - ∑ m ∈ range n, (x : ℂ) ^ m / (m.factorial : ℂ)
      = ((Real.exp x - ∑ m ∈ range n, x ^ m / m.factorial : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [Complex.norm_real] using h

lemma le_highPoly {w : ℝ} (hw : 0 < w) {K : ℕ} (hK : w / (K + 2) ≤ 1 / 2) :
    (Real.exp w - 1) / w ≤ lowPoly K w + 2 * w ^ K / ((K + 1).factorial : ℝ) := by
  have h := real_exp_bound' (x := w) (n := K + 1) (by
    rw [abs_of_pos hw]; push_cast; convert! hK using 2; ring)
  have h2 := (abs_le.mp h).2
  rw [Finset.sum_range_succ'] at h2
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h2
  rw [abs_of_pos hw] at h2
  rw [div_le_iff₀ hw]
  unfold lowPoly
  rw [add_mul, Finset.sum_mul]
  have : ∀ k ∈ range K, w ^ k / ((k + 1).factorial : ℝ) * w = w ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    intro k _; ring
  rw [Finset.sum_congr rfl this]
  have e : 2 * w ^ K / ((K + 1).factorial : ℝ) * w = w ^ (K + 1) / ((K + 1).factorial : ℝ) * 2 := by
    ring
  rw [e]
  linarith

/-! ## Integrability and the polynomial enclosures of `Ein` -/

lemma integrand_intervalIntegrable {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun w => (Real.exp w - 1) / w) volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine Measure.integrableOn_of_bounded (M := Real.exp x) (by simp) ?_ ?_
  · exact (by fun_prop : Measurable fun w : ℝ => (Real.exp w - 1) / w).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hw.1)]
    exact le_trans (integrand_le_exp hw.1) (Real.exp_le_exp.mpr hw.2)

lemma integral_lowPoly (K : ℕ) (x : ℝ) :
    ∫ w in (0 : ℝ)..x, lowPoly K w
      = ∑ k ∈ range K, x ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) := by
  unfold lowPoly
  rw [intervalIntegral.integral_finset_sum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_div, integral_pow]
  push_cast
  field_simp
  ring

/-- Lower polynomial bound for `Ein`. -/
noncomputable def EinLo (K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range K, x ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))

/-- Upper polynomial bound for `Ein` (valid for `x ≤ (K+2)/2`). -/
noncomputable def EinHi (K : ℕ) (x : ℝ) : ℝ :=
  EinLo K x + 2 * x ^ (K + 1) / (((K + 1 : ℕ) : ℝ) * ((K + 1).factorial : ℝ))

lemma EinLo_le_Ein {x : ℝ} (hx : 0 ≤ x) (K : ℕ) : EinLo K x ≤ Ein x := by
  unfold EinLo Ein
  rw [← integral_lowPoly]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hx
  · apply Continuous.intervalIntegrable; unfold lowPoly; fun_prop
  · exact integrand_intervalIntegrable hx
  · intro w hw; exact lowPoly_le hw.1 K

lemma Ein_le_EinHi {x : ℝ} (hx : 0 ≤ x) {K : ℕ} (hK : x / (K + 2) ≤ 1 / 2) :
    Ein x ≤ EinHi K x := by
  have hint : ∫ w in (0 : ℝ)..x, (lowPoly K w + 2 * w ^ K / ((K + 1).factorial : ℝ))
      = EinHi K x := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; unfold lowPoly; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [integral_lowPoly, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_pow]
    unfold EinHi EinLo
    push_cast
    field_simp
    ring
  unfold Ein
  rw [← hint]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hx
  · exact integrand_intervalIntegrable hx
  · apply Continuous.intervalIntegrable; unfold lowPoly; fun_prop
  · intro w hw
    apply le_highPoly hw.1
    have hK0 : (0 : ℝ) < K + 2 := by positivity
    calc w / (K + 2) ≤ x / (K + 2) := by gcongr; exact hw.2.le
      _ ≤ 1 / 2 := hK

lemma EinLo_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (K : ℕ) : EinLo K x ≤ EinLo K y := by
  unfold EinLo
  gcongr

/-! ## The derivative of `Ei` -/

lemma hasDerivAt_Ein {x : ℝ} (hx : 0 < x) : HasDerivAt Ein ((Real.exp x - 1) / x) x := by
  have hcont : ContinuousOn (fun w : ℝ => (Real.exp w - 1) / w) (Set.Ioi 0) := by
    apply ContinuousOn.div (by fun_prop) continuousOn_id
    intro w hw; exact ne_of_gt hw
  apply intervalIntegral.integral_hasDerivAt_right (integrand_intervalIntegrable hx.le)
  · exact hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact hcont.continuousAt (Ioi_mem_nhds hx)

lemma hasDerivAt_Ei {x : ℝ} (hx : 0 < x) : HasDerivAt Ei (Real.exp x / x) x := by
  have h := ((hasDerivAt_const x Real.eulerMascheroniConstant).add
    (Real.hasDerivAt_log hx.ne')).add (hasDerivAt_Ein hx)
  convert! h using 1
  · field_simp
    ring

end BSCert.EiFn
