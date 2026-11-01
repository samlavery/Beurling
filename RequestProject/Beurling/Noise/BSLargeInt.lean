module

public import RequestProject.Beurling.Noise.BSLargeDefs

/-!
# Integrals against `π` (Theorem 5.6, Step 7(ii))

For `u ≥ 2`, integrals of `φ(w) ρ(w-1)/w` over `(u-1, ∞)`:

* `rho_tail`: (R3) the density of `π` at `w ≥ u` is at most `e^{-r(u-1)(w-u)}/u` (times `ρ(u-1)`);
* `integral_Ioi_shift_div`: (R1) `∫_a^∞ ρ(w-1) dw/w = ρ(a)` for `a ≥ 1` (with integrability);
* `integrableOn_mul_rho`: `φ(w) ρ(w-1)/w` is integrable on `(u-1, ∞)` when `φ` is continuous and
  `|φ(w)| ≤ C (1+w)⁵`;
* `integral_Ioi_exp`, `integral_Ioi_moment`: `∫_u^∞ e^{-r(w-u)} = 1/r` and
  `∫_u^∞ s(1+s)³ e^{-rs} = 1/r² + 6/r³ + 18/r⁴ + 24/r⁵` (`s = w - u`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace BSaias.Large

lemma ratio_ge_one {v : ℝ} (hv : 1 ≤ v) : 1 ≤ Dickman.ratio v :=
  BSCert.dickmanRatioFacts.one_le hv

/-- (R3): for `u ≥ 2` and `w ≥ u`, `ρ(w-1)/w ≤ ρ(u-1) e^{-r(u-1)(w-u)}/u`. -/
lemma rho_tail {u w : ℝ} (hu : 2 ≤ u) (hw : u ≤ w) :
    Dickman.rho (w - 1) / w ≤
      Dickman.rho (u - 1) * Real.exp (-(Dickman.ratio (u - 1) * (w - u))) / u := by
  have h := Dickman.rho_le_exp (w := u - 1) (t := w - 1) (by linarith) (by linarith)
  have e : w - 1 - (u - 1) = w - u := by ring
  rw [e] at h
  have hu0 : 0 < u := by linarith
  calc Dickman.rho (w - 1) / w ≤ Dickman.rho (w - 1) / u :=
        div_le_div_of_nonneg_left (Dickman.rho_pos _).le hu0 hw
    _ ≤ _ := div_le_div_of_nonneg_right h hu0.le

/-- (R1): `∫_a^∞ ρ(w-1) dw/w = ρ(a)` for `a ≥ 1`, and the integrand is integrable. -/
lemma integral_Ioi_shift_div {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun w => Dickman.rho (w - 1) / w) (Ioi a) ∧
      ∫ w in Ioi a, Dickman.rho (w - 1) / w = Dickman.rho a := by
  have hcont : ContinuousWithinAt (fun w => -Dickman.rho w) (Ici a) a :=
    (Dickman.continuous_rho.neg).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt (fun w => -Dickman.rho w)
      (Dickman.rho (x - 1) / x) x := by
    intro x hx
    have := (Dickman.hasDerivAt_rho (lt_of_le_of_lt ha hx)).neg
    simpa [Pi.neg_def] using this
  have hpos : ∀ x ∈ Ioi a, 0 ≤ Dickman.rho (x - 1) / x := fun x hx =>
    div_nonneg (Dickman.rho_pos _).le (by linarith [mem_Ioi.mp hx])
  have hlim : Tendsto (fun w => -Dickman.rho w) atTop (𝓝 (-0)) :=
    Dickman.tendsto_rho_atTop.neg
  rw [neg_zero] at hlim
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  ring

lemma pow_five_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 5 ≤ 3840 * Real.exp (x / 2) := by
  have h := Real.pow_div_factorial_le_exp (x := x / 2) (by linarith) 5
  have e : (x / 2) ^ 5 / (Nat.factorial 5 : ℝ) = x ^ 5 / 3840 := by
    norm_num [Nat.factorial]; ring
  rw [e] at h
  linarith

/-- Integrability against `π`: if `φ` is continuous on `[u-1, ∞)` with `|φ(w)| ≤ C(1+w)⁵`,
then `φ(w) ρ(w-1)/w` is integrable on `(u-1, ∞)` (`u ≥ 2`). -/
lemma integrableOn_mul_rho {u C : ℝ} (hu : 2 ≤ u) {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Ici (u - 1))) (hb : ∀ w, u - 1 ≤ w → |φ w| ≤ C * (1 + w) ^ 5) :
    IntegrableOn (fun w => φ w * Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
  have hF : ContinuousOn (fun w => φ w * Dickman.rho (w - 1) / w) (Ici (u - 1)) := by
    apply ContinuousOn.div (hc.mul (Dickman.continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn) continuousOn_id
    intro x hx; simp only [id]; linarith [mem_Ici.mp hx]
  have hC : 0 ≤ C := by
    have h1 := hb (u - 1) le_rfl
    have h2 : 0 < (1 + (u - 1)) ^ 5 := pow_pos (by linarith) 5
    by_contra hneg; push_neg at hneg
    have : C * (1 + (u - 1)) ^ 5 < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg (φ (u - 1))]
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : u - 1 ≤ u)]
  refine IntegrableOn.union ?_ ?_
  · exact ((hF.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · set K := C * Dickman.rho (u - 1) / u * 3840 * Real.exp (1 / 2 + u)
    have hg : IntegrableOn (fun w => K * Real.exp (-(1 / 2) * w)) (Ioi u) :=
      (exp_neg_integrableOn_Ioi u (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K
    refine hg.mono' ((hF.mono (fun x hx =>
      mem_Ici.mpr (by linarith [mem_Ioi.mp hx]))).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_
    have hw' : u < w := hw
    have hw0 : 0 < w := by linarith
    have hr0 := ratio_ge_one (v := u - 1) (by linarith)
    have htail := rho_tail hu hw'.le
    have hphi := hb w (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Dickman.rho_pos _), abs_of_pos hw0,
      mul_div_assoc]
    have hexp : Real.exp (-(Dickman.ratio (u - 1) * (w - u))) ≤ Real.exp (-(w - u)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h5 := pow_five_le_exp (x := 1 + w) (by linarith)
    have hρu := Dickman.rho_pos (u - 1)
    have hu0 : 0 < u := by linarith
    calc |φ w| * (Dickman.rho (w - 1) / w)
        ≤ (C * (1 + w) ^ 5) * (Dickman.rho (u - 1) * Real.exp (-(w - u)) / u) := by
          apply mul_le_mul hphi (htail.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hρu.le) hu0.le))
            (div_nonneg (Dickman.rho_pos _).le hw0.le) (mul_nonneg hC (pow_nonneg (by linarith) 5))
      _ ≤ (C * (3840 * Real.exp ((1 + w) / 2))) *
            (Dickman.rho (u - 1) * Real.exp (-(w - u)) / u) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hC) (by positivity)
      _ = C * 3840 * Dickman.rho (u - 1) / u *
            (Real.exp ((1 + w) / 2) * Real.exp (-(w - u))) := by ring
      _ = K * Real.exp (-(1 / 2) * w) := by
          have : Real.exp ((1 + w) / 2) * Real.exp (-(w - u)) =
              Real.exp (1 / 2 + u) * Real.exp (-(1 / 2) * w) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [this]; simp only [K]; ring

lemma tendsto_pow_mul_exp_shift (k : ℕ) {r u : ℝ} (hr : 0 < r) :
    Tendsto (fun w => (w - u) ^ k * Real.exp (-(r * (w - u)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun w : ℝ => r * (w - u)) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-u) tendsto_id).const_mul_atTop hr |>.congr
      (fun w => by simp [sub_eq_add_neg])
  have h2 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp h1
  have h3 := h2.const_mul ((r ^ k)⁻¹)
  rw [mul_zero] at h3
  refine h3.congr fun w => ?_
  simp only [Function.comp_apply]
  rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- `∫_u^∞ e^{-r(w-u)} dw = 1/r`. -/
lemma integral_Ioi_exp {r u : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w => Real.exp (-(r * (w - u)))) (Ioi u) ∧
      ∫ w in Ioi u, Real.exp (-(r * (w - u))) = 1 / r := by
  have hderiv : ∀ x ∈ Ici u, HasDerivAt (fun w => -Real.exp (-(r * (w - u))) / r)
      (Real.exp (-(r * (x - u)))) x := by
    intro x _
    have h := ((((hasDerivAt_id x).sub_const u).const_mul r).neg.exp).neg.div_const r
    convert! h using 1
    field_simp
    simp
  have hpos : ∀ x ∈ Ioi u, 0 ≤ Real.exp (-(r * (x - u))) := fun _ _ => (Real.exp_pos _).le
  have hlim : Tendsto (fun w => -Real.exp (-(r * (w - u))) / r) atTop (𝓝 0) := by
    have := ((tendsto_pow_mul_exp_shift 0 hr (u := u)).neg).div_const r
    simpa using this
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- `∫_u^∞ s(1+s)³ e^{-rs} dw = 1/r² + 6/r³ + 18/r⁴ + 24/r⁵`, `s = w - u`. -/
lemma integral_Ioi_moment {r u : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w => (w - u) * (1 + (w - u)) ^ 3 * Real.exp (-(r * (w - u)))) (Ioi u) ∧
      ∫ w in Ioi u, (w - u) * (1 + (w - u)) ^ 3 * Real.exp (-(r * (w - u))) =
        1 / r ^ 2 + 6 / r ^ 3 + 18 / r ^ 4 + 24 / r ^ 5 := by
  -- `P(s) = q/r + q'/r² + q''/r³ + q'''/r⁴ + q''''/r⁵`, `q = s + 3s² + 3s³ + s⁴`, expanded
  set a0 : ℝ := 1 / r ^ 2 + 6 / r ^ 3 + 18 / r ^ 4 + 24 / r ^ 5 with ha0
  set a1 : ℝ := 1 / r + 6 / r ^ 2 + 18 / r ^ 3 + 24 / r ^ 4 with ha1
  set a2 : ℝ := 3 / r + 9 / r ^ 2 + 12 / r ^ 3 with ha2
  set a3 : ℝ := 3 / r + 4 / r ^ 2 with ha3
  set a4 : ℝ := 1 / r with ha4
  set P : ℝ → ℝ := fun s => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4 with hP
  have hPd : ∀ s, HasDerivAt P (a1 + a2 * (2 * s) + a3 * (3 * s ^ 2) + a4 * (4 * s ^ 3)) s := by
    intro s
    have hs := hasDerivAt_id s
    have := (((((hasDerivAt_const s a0).add (hs.const_mul a1)).add
      ((hs.pow 2).const_mul a2)).add ((hs.pow 3).const_mul a3)).add ((hs.pow 4).const_mul a4))
    convert! this using 1
    simp only [id]; push_cast; ring
  have hderiv : ∀ x ∈ Ici u, HasDerivAt (fun w => -(Real.exp (-(r * (w - u))) * P (w - u)))
      ((x - u) * (1 + (x - u)) ^ 3 * Real.exp (-(r * (x - u)))) x := by
    intro x _
    have he := (((hasDerivAt_id x).sub_const u).const_mul r).neg.exp
    have hp := (hPd (x - u)).comp x ((hasDerivAt_id x).sub_const u)
    have h := (he.mul hp).neg
    convert! h using 1
    simp only [hP, id, Function.comp_apply, Pi.neg_apply, Pi.mul_apply, ha0, ha1, ha2, ha3, ha4]
    field_simp
    ring
  have hpos : ∀ x ∈ Ioi u, 0 ≤ (x - u) * (1 + (x - u)) ^ 3 * Real.exp (-(r * (x - u))) := by
    intro x hx
    have : 0 ≤ x - u := by linarith [mem_Ioi.mp hx]
    positivity
  have hlim : Tendsto (fun w => -(Real.exp (-(r * (w - u))) * P (w - u))) atTop (𝓝 0) := by
    have t := fun k => tendsto_pow_mul_exp_shift k hr (u := u)
    have hsum := (((((t 0).const_mul a0).add ((t 1).const_mul a1)).add ((t 2).const_mul a2)).add
      ((t 3).const_mul a3)).add ((t 4).const_mul a4) |>.neg
    simp only [mul_zero, add_zero, neg_zero] at hsum
    refine hsum.congr fun w => ?_
    simp only [hP]
    ring
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [hP, sub_self, mul_zero, neg_zero, Real.exp_zero]
  simp only [ha0]
  ring

end BSaias.Large

end
