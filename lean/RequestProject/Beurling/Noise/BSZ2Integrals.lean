module

public import RequestProject.Beurling.Noise.BSZ2Tail

/-!
# Elementary integrals for the region-Z2 bound (Theorem 5.6, Step 7(iii))

* the masses of `π` from (R1): `∫_{u-1}^u ρ(w-1)/w = ρ(u-1) - ρ(u)`,
  `∫_{u-1}^u ρ(w-1)(u-w)/w = ρ(u-1) - uρ(u)`, `∫_u^U ρ(w-1)/w = ρ(u) - ρ(U)`,
  `∫_{u-1}^u ρ(w-1) = (u-1)ρ(u-1)`;
* the exponential integrals `∫_c^d e^{-k(w-u)} dw = (e^{-k(c-u)} - e^{-k(d-u)})/k`;
* the linear interpolation `e^{-αt} ≤ 1 - (1 - e^{-α}) t` on `[0, 1]` (convexity of `exp`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace BSaias

lemma intervalIntegrable_P {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w => Dickman.rho (w - 1) / w) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro w hw
  exact ((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt.div
    continuousAt_id (by simp only [id]; linarith [hw.1])).continuousWithinAt

lemma intervalIntegrable_P2 {a b u : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w => Dickman.rho (w - 1) * (u - w) / w) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro w hw
  exact (((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).mul
    (continuous_const.sub continuous_id)).continuousAt.div
    continuousAt_id (by simp only [id]; linarith [hw.1])).continuousWithinAt

lemma intervalIntegrable_rho_shift (a b : ℝ) :
    IntervalIntegrable (fun w => Dickman.rho (w - 1)) volume a b :=
  (Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).intervalIntegrable a b

lemma intervalIntegrable_expl (k u a b : ℝ) :
    IntervalIntegrable (fun w => Real.exp (-(k * (w - u)))) volume a b := by
  apply Continuous.intervalIntegrable; fun_prop

lemma mass_I {u : ℝ} (hu : 2 ≤ u) :
    ∫ w in (u - 1)..u, Dickman.rho (w - 1) / w = Dickman.rho (u - 1) - Dickman.rho u :=
  Dickman.integral_shift_div (by linarith) (by linarith)

lemma mass_tail {u U : ℝ} (hu : 2 ≤ u) (hU : u ≤ U) :
    ∫ w in u..U, Dickman.rho (w - 1) / w = Dickman.rho u - Dickman.rho U :=
  Dickman.integral_shift_div (by linarith) (by linarith)

lemma mass_lin {u : ℝ} (hu : 2 ≤ u) :
    ∫ w in (u - 1)..u, Dickman.rho (w - 1) * (u - w) / w =
      Dickman.rho (u - 1) - u * Dickman.rho u :=
  Dickman.integral_shift_mul_div hu

lemma mass_flat {u : ℝ} (hu : 2 ≤ u) :
    ∫ w in (u - 1)..u, Dickman.rho (w - 1) = (u - 1) * Dickman.rho (u - 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => Dickman.rho t) 1,
    Dickman.mul_rho_eq_integral (by linarith)]

/-- `∫_c^d e^{-k(w-u)} dw = (e^{-k(c-u)} - e^{-k(d-u)})/k`. -/
lemma integral_expl {k u c d : ℝ} (hk : k ≠ 0) :
    ∫ w in c..d, Real.exp (-(k * (w - u))) =
      (Real.exp (-(k * (c - u))) - Real.exp (-(k * (d - u)))) / k := by
  have hF : ∀ w ∈ uIcc c d, HasDerivAt (fun w => -Real.exp (-(k * (w - u))) / k)
      (Real.exp (-(k * (w - u)))) w := by
    intro w _
    have h1 : HasDerivAt (fun w => -(k * (w - u))) (-(k * 1)) w :=
      (((hasDerivAt_id w).sub_const u).const_mul k).neg
    have := (h1.exp.neg).div_const k
    convert! this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (intervalIntegrable_expl k u c d)]
  ring

/-- `∫_c^d e^{-k(w-u)} dw ≤ e^{-k(c-u)}/k` for `k > 0`. -/
lemma integral_expl_le {k u c d : ℝ} (hk : 0 < k) :
    ∫ w in c..d, Real.exp (-(k * (w - u))) ≤ Real.exp (-(k * (c - u))) / k := by
  rw [integral_expl hk.ne']
  apply div_le_div_of_nonneg_right _ hk.le
  have := Real.exp_pos (-(k * (d - u))); linarith

/-- `e^{-αt} ≤ 1 - (1 - e^{-α}) t` for `t ∈ [0, 1]`. -/
lemma exp_neg_mul_le (α t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-(α * t)) ≤ 1 - (1 - Real.exp (-α)) * t := by
  have := convexOn_exp.2 (mem_univ (-α)) (mem_univ 0) ht0 (by linarith : 0 ≤ 1 - t)
    (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at this
  calc Real.exp (-(α * t)) = Real.exp (t * -α) := by ring_nf
    _ ≤ t * Real.exp (-α) + (1 - t) := this
    _ = 1 - (1 - Real.exp (-α)) * t := by ring

end BSaias

end
