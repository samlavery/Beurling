module

public import RequestProject.Beurling.LocalPNT.Kernel
public import RequestProject.Beurling.LocalPNT.Perron

/-!
# §5.7: the smoothed Perron integral of Step 9 (Theorem 5.24)

With `h₀ = perronKernel` (supported on `[-2, -1]`, of mass one) and `T > 0`, `v > 1`:

* `Hs T z = ∫_{τ ≥ -z} T h₀(Tτ) dτ` is a continuous monotone step from `0` (for `z < 1/T`)
  to `1` (for `z ≥ 2/T`).
* `f9 v T x = e^{-x} Hs(log v - x)` has Laplace transform
  `F9 v T s = v^{s-1} ĥ₀((s-1)/T)/(s-1)` on `Re s > 1`.
* Bounds for `ĥ₀ = hhat0`, differentiability of `hhat0` and `F9`, and the decay
  `‖F9(σ + it)‖ ≪ e^{σ(log v - 1/T)}/(1 + t²)` on `Re s ≥ c > 1`.
-/

@[expose] public section

open Set Real MeasureTheory Complex Filter Topology

namespace LocalPNT

section Kernel9

/-- `ĥ₀(w) = ∫ h₀(x) e^{wx} dx`. -/
noncomputable def hhat0 (w : ℂ) : ℂ := ∫ x, (perronKernel x : ℂ) * cexp (w * x)

/-- `Hs T z = ∫_{τ ≥ -z} T h₀(Tτ) dτ` (the smoothed step). -/
noncomputable def Hs (T z : ℝ) : ℝ := ∫ τ in Ici (-z), T * perronKernel (T * τ)

/-- `f(x) = e^{-x} Hs(log v - x)` (Step 9's test function in the variable x = log u). -/
noncomputable def f9 (v T x : ℝ) : ℝ := Real.exp (-x) * Hs T (Real.log v - x)

/-- Its transform `F(s) = v^{s-1} ĥ₀((s-1)/T)/(s-1)`. -/
noncomputable def F9 (v T : ℝ) (s : ℂ) : ℂ := (v : ℂ) ^ (s - 1) * hhat0 ((s - 1) / T) / (s - 1)

variable {v T : ℝ}

/-! ## The smoothed step `Hs` -/

theorem hasCompactSupport_perronKernel : HasCompactSupport perronKernel :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by_contra fun h => hx (perronKernel_support h)

theorem integrable_perronKernel : Integrable perronKernel :=
  continuous_perronKernel.integrable_of_hasCompactSupport hasCompactSupport_perronKernel

lemma perronKernel_eq_zero {x : ℝ} (hx : x ∉ Icc (-2 : ℝ) (-1)) : perronKernel x = 0 :=
  by_contra fun h => hx (perronKernel_support h)

lemma integral_Ici_perronKernel (a : ℝ) :
    ∫ u in Ici a, perronKernel u = ∫ u in a..0, perronKernel u := by
  have h0 : ∫ u in Ioi 0, perronKernel u = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
      perronKernel_eq_zero fun h => by linarith [h.2, (mem_Ioi.1 hu)]
  rw [integral_Ici_eq_integral_Ioi, ← intervalIntegral.integral_interval_add_Ioi
    integrable_perronKernel.integrableOn integrable_perronKernel.integrableOn, h0, add_zero]

/-- `Hs T z = ∫_{u ≥ -Tz} h₀(u) du`. -/
theorem Hs_eq (hT : 0 < T) (z : ℝ) : Hs T z = ∫ u in Ici (-(T * z)), perronKernel u := by
  rw [Hs, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_comp_mul_left_Ioi _ _ hT, smul_eq_mul, mul_neg, mul_inv_cancel_left₀ hT.ne']

theorem Hs_nonneg (hT : 0 < T) (z : ℝ) : 0 ≤ Hs T z := by
  rw [Hs_eq hT]
  exact setIntegral_nonneg measurableSet_Ici fun u _ => perronKernel_nonneg u

theorem Hs_le_one (hT : 0 < T) (z : ℝ) : Hs T z ≤ 1 := by
  rw [Hs_eq hT, ← integral_perronKernel]
  exact setIntegral_le_integral integrable_perronKernel
    (Eventually.of_forall fun u => perronKernel_nonneg u)

theorem Hs_eq_zero (hT : 0 < T) {z : ℝ} (hz : z < 1 / T) : Hs T z = 0 := by
  have hz' : T * z < 1 := by rw [lt_div_iff₀ hT] at hz; linarith
  rw [Hs_eq hT]
  exact setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
    perronKernel_eq_zero fun h => by linarith [h.2, mem_Ici.1 hu]

theorem Hs_eq_one (hT : 0 < T) {z : ℝ} (hz : 2 / T ≤ z) : Hs T z = 1 := by
  have hz' : 2 ≤ T * z := by rw [div_le_iff₀ hT] at hz; linarith
  rw [Hs_eq hT, ← integral_perronKernel]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu =>
    perronKernel_eq_zero fun h => hu (mem_Ici.2 (by linarith [h.1]))

theorem continuous_Hs (hT : 0 < T) : Continuous (Hs T) := by
  have hp := intervalIntegral.continuous_primitive
    (fun a b => integrable_perronKernel.intervalIntegrable (a := a) (b := b)) 0
  have e : Hs T = fun z => -∫ u in (0 : ℝ)..(-(T * z)), perronKernel u := by
    ext z
    rw [Hs_eq hT, integral_Ici_perronKernel, intervalIntegral.integral_symm]
  rw [e]
  exact (hp.comp (continuous_const.mul continuous_id).neg).neg

theorem monotone_Hs (hT : 0 < T) : Monotone (Hs T) := by
  intro z z' hzz
  rw [Hs_eq hT, Hs_eq hT]
  refine setIntegral_mono_set integrable_perronKernel.integrableOn
    (Eventually.of_forall fun u => perronKernel_nonneg u) (Eventually.of_forall fun u hu => ?_)
  have : -(T * z') ≤ -(T * z) := neg_le_neg (mul_le_mul_of_nonneg_left hzz hT.le)
  exact mem_Ici.2 (this.trans (mem_Ici.1 hu))

/-! ## The test function `f9` -/

theorem continuous_f9 (hT : 0 < T) : Continuous (f9 v T) :=
  (Real.continuous_exp.comp continuous_neg).mul
    ((continuous_Hs hT).comp (continuous_const.sub continuous_id))

theorem f9_eq_zero (hT : 0 < T) {x : ℝ} (hx : Real.log v - 1 / T < x) : f9 v T x = 0 := by
  rw [f9, Hs_eq_zero hT (by linarith), mul_zero]

theorem f9_nonneg (hT : 0 < T) (x : ℝ) : 0 ≤ f9 v T x :=
  mul_nonneg (Real.exp_pos _).le (Hs_nonneg hT _)

theorem f9_le (hT : 0 < T) (x : ℝ) : f9 v T x ≤ Real.exp (-x) :=
  mul_le_of_le_one_right (Real.exp_pos _).le (Hs_le_one hT _)

theorem integrable_f9_mul_exp (hT : 0 < T) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun x => f9 v T x * Real.exp (σ * x)) := by
  have hi := (integrableOn_exp_mul_Iic (by linarith : 0 < σ - 1) (Real.log v)).integrable_indicator
    measurableSet_Iic
  refine hi.mono' (((continuous_f9 hT).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (f9_nonneg hT x) (Real.exp_pos _).le)]
  by_cases hx : x ∈ Iic (Real.log v)
  · rw [indicator_of_mem hx]
    calc f9 v T x * Real.exp (σ * x) ≤ Real.exp (-x) * Real.exp (σ * x) :=
          mul_le_mul_of_nonneg_right (f9_le hT x) (Real.exp_pos _).le
      _ = Real.exp ((σ - 1) * x) := by rw [← Real.exp_add]; ring_nf
  · rw [indicator_of_notMem hx, f9_eq_zero hT, zero_mul]
    have : Real.log v < x := not_le.1 hx
    have : 0 < 1 / T := by positivity
    linarith

/-! ## The Laplace transform of `f9` -/

/-- `∫ e^{-wξ} ∫_{τ ≥ -ξ} h(τ) dτ dξ = ĥ(w)/w` for `Re w > 0` (Fubini). -/
theorem laplace_tail {h : ℝ → ℝ} (hc0 : Continuous h) (hsupp : HasCompactSupport h)
    {w : ℂ} (hw : 0 < w.re) :
    ∫ ξ : ℝ, (∫ τ in Ici (-ξ), (h τ : ℂ)) * cexp (-w * ξ) =
      (∫ τ : ℝ, (h τ : ℂ) * cexp (w * τ)) / w := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ τ, R < τ → h τ = 0 := by
    obtain ⟨R, hR⟩ := hsupp.isCompact.bddAbove
    exact ⟨R, fun τ hτ => image_eq_zero_of_notMem_tsupport fun hm => (hR hm).not_gt hτ⟩
  have hhi : Integrable (fun τ : ℝ => (h τ : ℂ)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (hsupp.comp_left ofReal_zero)
  set k : ℝ × ℝ → ℂ := indicator {p : ℝ × ℝ | -p.1 ≤ p.2}
    (fun p => (h p.2 : ℂ) * cexp (-w * p.1)) with hk_def
  have hS : MeasurableSet {p : ℝ × ℝ | -p.1 ≤ p.2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hexpi : Integrable (indicator (Ici (-R)) fun ξ : ℝ => Real.exp (-w.re * ξ)) := by
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) _
  have hk : Integrable k (volume.prod volume) := by
    refine Integrable.mono' (hexpi.mul_prod hhi.norm) ?_ (Eventually.of_forall fun p => ?_)
    · exact ((by fun_prop : Continuous _).aestronglyMeasurable).indicator hS
    · have hnn : 0 ≤ indicator (Ici (-R)) (fun ξ : ℝ => Real.exp (-w.re * ξ)) p.1 *
          ‖(h p.2 : ℂ)‖ :=
        mul_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _) (norm_nonneg _)
      by_cases hp : p ∈ {p : ℝ × ℝ | -p.1 ≤ p.2}
      · by_cases hz : h p.2 = 0
        · simp [hk_def, hz]
        · have : p.1 ∈ Ici (-R) := by
            have := not_lt.1 (mt (hR p.2) hz)
            have hp' : -p.1 ≤ p.2 := hp
            simp only [mem_Ici]
            linarith
          rw [hk_def]
          simp only [indicator_of_mem hp, indicator_of_mem this, norm_mul, Complex.norm_exp]
          simp [mul_comm]
      · simp only [hk_def, indicator_of_notMem hp, norm_zero]
        exact hnn
  have hkτ : ∀ ξ, ∫ τ, k (ξ, τ) = (∫ τ in Ici (-ξ), (h τ : ℂ)) * cexp (-w * ξ) := fun ξ => by
    have : (fun τ => k (ξ, τ)) =
        indicator (Ici (-ξ)) (fun τ => (h τ : ℂ) * cexp (-w * ξ)) := by
      ext τ
      simp [hk_def, indicator]
    rw [this, integral_indicator measurableSet_Ici, integral_mul_const]
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  have hkξ : ∀ τ, ∫ ξ, k (ξ, τ) = (h τ : ℂ) * cexp (w * τ) / w := fun τ => by
    have : (fun ξ => k (ξ, τ)) =
        indicator (Ici (-τ)) (fun ξ => (h τ : ℂ) * cexp (-w * ξ)) := by
      ext ξ
      simp [hk_def, indicator, neg_le]
    rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hw)]
    push_cast
    field_simp
  calc ∫ ξ : ℝ, (∫ τ in Ici (-ξ), (h τ : ℂ)) * cexp (-w * ξ) = ∫ ξ : ℝ, ∫ τ : ℝ, k (ξ, τ) := by
        simp only [hkτ]
    _ = ∫ τ : ℝ, ∫ ξ : ℝ, k (ξ, τ) := integral_integral_swap hk
    _ = _ := by simp only [hkξ, integral_div]

/-- `∫ T h₀(Tτ) e^{wτ} dτ = ĥ₀(w/T)`. -/
theorem integral_rescaled_perronKernel (hT : 0 < T) (w : ℂ) :
    ∫ τ : ℝ, ((T * perronKernel (T * τ) : ℝ) : ℂ) * cexp (w * τ) = hhat0 (w / T) := by
  have hT' : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.ne'
  calc ∫ τ : ℝ, ((T * perronKernel (T * τ) : ℝ) : ℂ) * cexp (w * τ)
      = ∫ τ : ℝ, (T : ℂ) * ((perronKernel (T * τ) : ℂ) * cexp (w / T * ↑(T * τ))) := by
        congr 1; ext τ; push_cast; field_simp
    _ = (T : ℂ) * ((T⁻¹ : ℝ) • ∫ y : ℝ, (perronKernel y : ℂ) * cexp (w / T * y)) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left
          (fun y : ℝ => (perronKernel y : ℂ) * cexp (w / T * y)) T, abs_of_pos (inv_pos.2 hT)]
    _ = hhat0 (w / T) := by
        rw [hhat0, real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hT', one_mul]

/-- **The transform of Step 9's test function**: `∫ f(x) e^{sx} dx = F(s)` for `Re s > 1`. -/
theorem integral_f9_mul_cexp (hT : 0 < T) (hv : 1 < v) {s : ℂ} (hs : 1 < s.re) :
    ∫ x, (f9 v T x : ℂ) * cexp (s * x) = F9 v T s := by
  set L := Real.log v
  have e : ∀ z : ℝ, (f9 v T (L - z) : ℂ) * cexp (s * ↑(L - z)) =
      cexp ((s - 1) * L) * ((Hs T z : ℂ) * cexp (-(s - 1) * z)) := fun z => by
    rw [f9, show Real.log v - (L - z) = z by simp [L]]
    simp only [ofReal_mul, ofReal_exp]
    rw [mul_right_comm, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  have hHs : ∀ z, (Hs T z : ℂ) = ∫ τ in Ici (-z), (((fun τ => T * perronKernel (T * τ)) τ : ℝ) :
      ℂ) := fun z => by
    rw [Hs]; exact integral_ofReal.symm
  have hc : Continuous fun τ => T * perronKernel (T * τ) :=
    continuous_const.mul (continuous_perronKernel.comp (continuous_const.mul continuous_id))
  have hsupp : HasCompactSupport fun τ => T * perronKernel (T * τ) :=
    (hasCompactSupport_perronKernel.comp_smul hT.ne').mul_left
  rw [← integral_sub_left_eq_self _ volume L]
  simp only [e, integral_const_mul, hHs]
  rw [laplace_tail hc hsupp (by simpa using hs), integral_rescaled_perronKernel hT, F9,
    cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (0 : ℝ) < v).ne'),
    ← ofReal_log (by linarith : (0 : ℝ) ≤ v), mul_comm (L : ℂ), mul_div_assoc]

/-! ## Bounds and differentiability of `ĥ₀` -/

theorem hhat0_eq (W : ℂ) : hhat0 W = cexp (-(3 / 2) * W) * boxFactor (1 / 38) W ^ 19 :=
  perronKernel_laplace_boxFactor W

lemma norm_hhat0_le_of_boxFactor {W : ℂ} {B : ℝ}
    (hB : ‖boxFactor (1 / 38) W‖ ≤ Real.exp (W.re / 38) * B) :
    ‖hhat0 W‖ ≤ Real.exp (-W.re) * B ^ 19 := by
  rw [hhat0_eq, norm_mul, norm_pow, Complex.norm_exp]
  calc Real.exp (-(3 / 2) * W).re * ‖boxFactor (1 / 38) W‖ ^ 19
      ≤ Real.exp (-(3 / 2) * W).re * (Real.exp (W.re / 38) * B) ^ 19 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB 19) (Real.exp_pos _).le
    _ = Real.exp (-W.re) * B ^ 19 := by
        rw [mul_pow, ← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        have : (-(3 / 2) * W).re = -(3 / 2) * W.re := by simp
        rw [this]; push_cast; ring

theorem norm_hhat0_le {W : ℂ} (hW : 0 ≤ W.re) : ‖hhat0 W‖ ≤ Real.exp (-W.re) := by
  have h := norm_hhat0_le_of_boxFactor (B := 1) (by
    have := norm_boxFactor_le (by norm_num : (0 : ℝ) < 1 / 38) W
    rw [abs_of_nonneg hW] at this
    rw [mul_one]; convert this using 2; ring)
  simpa using h

theorem norm_hhat0_le' {W : ℂ} (hW : 0 ≤ W.re) (hW0 : W ≠ 0) :
    ‖hhat0 W‖ ≤ Real.exp (-W.re) * (38 / ‖W‖) ^ 19 := by
  refine norm_hhat0_le_of_boxFactor ?_
  have h2 := norm_sinh_div_le' (W / 38)
  rw [← show boxFactor (1 / 38) W = Complex.sinh (W / 38) / (W / 38) by
    rw [boxFactor_eq (by norm_num) hW0]; push_cast; ring_nf] at h2
  rw [norm_div, show ‖(38 : ℂ)‖ = 38 by simp, show (W / 38).re = W.re / 38 by simp,
    abs_div, abs_of_nonneg hW, abs_of_pos (by norm_num : (0 : ℝ) < 38)] at h2
  refine h2.trans (le_of_eq ?_)
  have : ‖W‖ ≠ 0 := norm_ne_zero_iff.2 hW0
  field_simp

theorem continuous_hhat0 : Continuous hhat0 := by
  have e : hhat0 = fun W => ∫ x in Icc (-2 : ℝ) (-1), (perronKernel x : ℂ) * cexp (W * x) := by
    ext W
    rw [hhat0, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [perronKernel_eq_zero hx, ofReal_zero, zero_mul]]
  rw [e]
  have := continuous_perronKernel
  exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc

theorem differentiable_hhat0 : Differentiable ℂ hhat0 := by
  have hd : DifferentiableOn ℂ hhat0 (univ \ {0}) := by
    refine DifferentiableOn.congr (f := fun W =>
      cexp (-(3 / 2) * W) * (Complex.sinh (W / 38) / (W / 38)) ^ 19) (fun W hW => ?_)
      (fun W hW => perronKernel_laplace hW.2)
    have hW0 : W / 38 ≠ 0 := div_ne_zero hW.2 (by norm_num)
    exact ((differentiableAt_id.const_mul _).cexp.mul
      (((differentiableAt_id.div_const 38).csinh.div (differentiableAt_id.div_const 38)
        hW0).pow 19)).differentiableWithinAt
  exact differentiableOn_univ.1 ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    univ_mem).1 ⟨hd, continuous_hhat0.continuousAt⟩)

/-! ## Differentiability and bounds of `F9` -/

theorem differentiableOn_F9 (hv : 1 < v) : DifferentiableOn ℂ (F9 v T) {s | s ≠ 1} := by
  intro s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < v).ne'
  exact ((((differentiableAt_id.sub_const 1).const_cpow (Or.inl hv0)).mul
    (differentiable_hhat0.differentiableAt.comp s
      ((differentiableAt_id.sub_const 1).div_const _))).div
    (differentiableAt_id.sub_const 1) hs1).differentiableWithinAt

theorem differentiableOn_F9_re_gt_one (hv : 1 < v) :
    DifferentiableOn ℂ (F9 v T) {s | 1 < s.re} :=
  (differentiableOn_F9 hv).mono fun s hs h1 => by simp [h1] at hs

theorem differentiableOn_F9_strip (hv : 1 < v) :
    DifferentiableOn ℂ (F9 v T) ({s | 0 < s.re} \ {1}) :=
  (differentiableOn_F9 hv).mono fun _ hs => hs.2

theorem norm_F9 (hv : 1 < v) (s : ℂ) :
    ‖F9 v T s‖ = v ^ (s.re - 1) * ‖hhat0 ((s - 1) / T)‖ / ‖s - 1‖ := by
  rw [F9, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith), sub_re, one_re]

theorem norm_hhat0_contour_le (hT : 0 < T) (s : ℂ) :
    ‖hhat0 ((s - 1) / T)‖ ≤
      76 ^ 19 * Real.exp (2 * |(s - 1).re| / T) / (1 + ‖s - 1‖ / T) ^ 19 := by
  have h := norm_perronKernel_laplace_le ((s - 1) / T)
  rw [div_ofReal_re, abs_div, abs_of_pos hT, norm_div, norm_real, Real.norm_of_nonneg hT.le,
    ← mul_div_assoc] at h
  exact h

private lemma decay_aux {r t A B H : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    (hrA : 1 ≤ A * r) (ht : |t| ≤ r) (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hH2 : H * r ^ 19 ≤ B) :
    H / r ≤ 2 * (A + B) / (1 + t ^ 2) := by
  rw [div_le_div_iff₀ hr (by positivity)]
  have ht2 : t ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  rcases lt_or_ge r 1 with h1 | h1
  · have : r ^ 2 < 1 := by nlinarith
    have : H * (1 + t ^ 2) ≤ 2 := by nlinarith
    nlinarith
  · have hHr : H * r ≤ B := by
      have : r ≤ r ^ 19 := by
        calc r = r ^ 1 := (pow_one r).symm
          _ ≤ r ^ 19 := pow_le_pow_right₀ h1 (by norm_num)
      nlinarith
    have h2 : 1 + t ^ 2 ≤ 2 * r ^ 2 := by nlinarith
    calc H * (1 + t ^ 2) ≤ H * (2 * r ^ 2) := mul_le_mul_of_nonneg_left h2 hH0
      _ = 2 * r * (H * r) := by ring
      _ ≤ 2 * r * B := mul_le_mul_of_nonneg_left hHr (by positivity)
      _ ≤ 2 * (A + B) * r := by nlinarith

/-- **Decay of `F9` on `Re s ≥ c > 1`.** -/
theorem norm_F9_le (hT : 0 < T) (hv : 1 < v) {c σ : ℝ} (hc : 1 < c) (hσ : c ≤ σ) (t : ℝ) :
    ‖F9 v T (σ + t * I)‖ ≤
      (1 / (c - 1) + (38 * T) ^ 19) * 2 / v * Real.exp (1 / T) *
        Real.exp (σ * (Real.log v - 1 / T)) * (1 + σ) / (1 + t ^ 2) := by
  set s : ℂ := σ + t * I
  set W : ℂ := (s - 1) / T
  set r := ‖s - 1‖
  have hv0 : 0 < v := by linarith
  have hre : (s - 1).re = σ - 1 := by simp [s]
  have him : (s - 1).im = t := by simp [s]
  have hWre : W.re = (σ - 1) / T := by simp only [W, div_ofReal_re, hre]
  have hWre0 : 0 < W.re := by rw [hWre]; exact div_pos (by linarith) hT
  have hrσ : σ - 1 ≤ r := hre ▸ re_le_norm _
  have hr : 0 < r := by linarith
  have hW0 : W ≠ 0 := fun h => by simp [h] at hWre0
  have hWn : ‖W‖ = r / T := by
    simp only [W, norm_div, norm_real, Real.norm_of_nonneg hT.le, r]
  set H := ‖hhat0 W‖ * Real.exp W.re
  have hE := Real.exp_pos W.re
  have hH0 : 0 ≤ H := by positivity
  have hH1 : H ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (norm_hhat0_le hWre0.le) hE.le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have hH2 : H * r ^ 19 ≤ (38 * T) ^ 19 := by
    have := mul_le_mul_of_nonneg_right (norm_hhat0_le' hWre0.le hW0) hE.le
    rw [mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul, hWn,
      div_div_eq_mul_div] at this
    calc H * r ^ 19 ≤ (38 * T / r) ^ 19 * r ^ 19 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = (38 * T) ^ 19 := by rw [div_pow, div_mul_cancel₀ _ (by positivity)]
  have hc1 : 0 < c - 1 := by linarith
  have hrA : 1 ≤ 1 / (c - 1) * r := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
  have hD := decay_aux (by positivity) hr hrA (him ▸ abs_im_le_norm _) hH0 hH1 hH2
  have hP : v ^ (s.re - 1) * Real.exp (-W.re) =
      Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v := by
    have hsre : s.re = σ := by simp [s]
    rw [hsre, hWre, Real.rpow_def_of_pos hv0, ← Real.exp_add,
      show Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v =
        Real.exp (σ * (Real.log v - 1 / T) + 1 / T - Real.log v) by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hv0]]
    congr 1
    field_simp
    ring
  have hF : ‖F9 v T s‖ = v ^ (s.re - 1) * Real.exp (-W.re) * (H / r) := by
    rw [norm_F9 hv]
    simp only [H, r, W]
    rw [Real.exp_neg]
    field_simp
  rw [hF, hP]
  have hEv : 0 ≤ Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v := by positivity
  calc Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v * (H / r)
      ≤ Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v *
          (2 * (1 / (c - 1) + (38 * T) ^ 19) / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hD hEv
    _ ≤ Real.exp (σ * (Real.log v - 1 / T)) * Real.exp (1 / T) / v *
          (2 * (1 / (c - 1) + (38 * T) ^ 19) / (1 + t ^ 2)) * (1 + σ) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
    _ = _ := by ring

end Kernel9

end LocalPNT

end
