module

public import RequestProject.Beurling.OscMellin
public import RequestProject.Beurling.Window

/-!
# The weights of the absorbed elements (Section 4.1, bounds (i)–(iv) after (14))

For `a ∈ A`, the weight of `a` in the forward-window average `ρ_A(u) = #(A ∩ [u, u+h(u)])/h(u)`,
for a window `h` (`Absorbed.IsWin`: continuous, non-decreasing, `h(u) ≤ u^{1/8}`, slope
`d log h/d log u ≤ 1/8`; the window of the construction is `Absorbed.winH`), is

  `w_a(s) = a^s ∫_{u_a}^a u^{-s} g(u) du = ∫_{u_a}^a (a/u)^s g(u) du`,  `g = 1/h`,
  `u_a + h(u_a) = a`,

and `M = ∫_{u_a}^a g`. With `ε = h(a)/a ≤ a^{-7/8}`, for `0 ≤ σ ≤ 2`:

* (i)  `(u_a/a)^{1/8} ≤ h(u_a)/h(a) ≤ M ≤ 1` and `a/u_a ≤ (1 - ε)⁻¹`;
* (ii) `|w_a(s)| ≤ (a/u_a)^σ M ≤ 1 + 1.02 σ ε`;
* (iv) `|1 - w_a(s)| ≤ 1.01 (|s| + 1/8) ε`, hence `|1 - w_a(s)| ≤ 2 |t| ε` for `|t| ≥ 2`.

(Bound (iii) of the paper is not used.) The paper assumes `a ≥ X₀/2`; here `a ≥ 10⁶` suffices.
-/

@[expose] public section

open Complex Set Filter MeasureTheory intervalIntegral Absorbed

namespace Weights

/-- `M = ∫_{u}^{a} dv/h(v)`. -/
noncomputable def massM (h : ℝ → ℝ) (a u : ℝ) : ℝ := ∫ v in u..a, (h v)⁻¹

/-- `w_a(s) = ∫_{u}^{a} (a/v)^s dv/h(v)`. -/
noncomputable def weight (h : ℝ → ℝ) (a u : ℝ) (s : ℂ) : ℂ :=
  ∫ v in u..a, ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ)

/-- The standing hypotheses: `h` is a window, `a ≥ 10⁶`, `u > 0` with `u + h(u) = a`. -/
structure WeightHyp (h : ℝ → ℝ) (a u : ℝ) : Prop where
  win : IsWin h
  a_ge : 10 ^ 6 ≤ a
  u_pos : 0 < u
  u_eq : u + h u = a

/-- `(1 + y)^σ ≤ 1 + 1.002 σ y` for `0 ≤ σ ≤ 2` and `0 ≤ y ≤ 10⁻³`. -/
lemma one_add_rpow_le {y σ : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 1000) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 2) :
    (1 + y) ^ σ ≤ 1 + 1.002 * σ * y := by
  have h1 : (1 + y) ^ σ ≤ Real.exp (σ * y) := by
    calc (1 + y) ^ σ ≤ (Real.exp y) ^ σ :=
          Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp y]) hσ0
      _ = Real.exp (σ * y) := by rw [← Real.exp_mul]; ring_nf
  have hz : |σ * y| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hz)).2
  have : (σ * y) ^ 2 ≤ 0.002 * σ * y := by
    have : σ * y ≤ 0.002 := by nlinarith
    nlinarith [mul_nonneg hσ0 hy0]
  linarith

/-- `|e^z - 1| ≤ |z| e^{Re z}` for `Re z ≥ 0`. -/
lemma norm_cexp_sub_one_le_mul {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp z.re := by
  have hconv : Convex ℝ {w : ℂ | w.re ≤ z.re} := convex_halfSpace_re_le _
  have := hconv.norm_image_sub_le_of_norm_deriv_le (f := Complex.exp) (C := Real.exp z.re)
    (fun w _ => Complex.differentiableAt_exp)
    (fun w hw => by rw [Complex.deriv_exp, Complex.norm_exp]; exact Real.exp_le_exp.mpr hw)
    (show (0 : ℂ) ∈ {w : ℂ | w.re ≤ z.re} by simpa using hz)
    (show z ∈ {w : ℂ | w.re ≤ z.re} by simp)
  simpa [mul_comm] using this

namespace WeightHyp

variable {h : ℝ → ℝ} {a u : ℝ} (hw : WeightHyp h a u)
include hw

lemma a_pos : 0 < a := by linarith [hw.a_ge]

lemma one_le_a : 1 ≤ a := by linarith [hw.a_ge]

lemma u_lt_a : u < a := by
  have := hw.win.pos u hw.u_pos; linarith [hw.u_eq]

lemma a_sub_u : a - u = h u := by linarith [hw.u_eq]

/-- `ε = h(a)/a`. -/
lemma eps_pos : 0 < h a / a := div_pos (hw.win.pos a hw.a_pos) hw.a_pos

/-- `ε ≤ a^{-7/8} ≤ 10⁻⁴`. -/
lemma eps_le : h a / a ≤ 1 / 10 ^ 4 := by
  have ha := hw.a_pos
  have h1 : h a / a ≤ a ^ (1 / 8 : ℝ) / a :=
    div_le_div_of_nonneg_right (hw.win.le_rpow a ha) ha.le
  have e : a ^ (1 / 8 : ℝ) / a = a ^ (-(7 / 8 : ℝ)) := by
    rw [show (-(7 / 8 : ℝ)) = 1 / 8 - 1 by norm_num, Real.rpow_sub ha, Real.rpow_one]
  have h2 : a ^ (-(7 / 8 : ℝ)) ≤ ((10 : ℝ) ^ 6) ^ (-(7 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hw.a_ge (by norm_num)
  have h3 : ((10 : ℝ) ^ 6) ^ (-(7 / 8 : ℝ)) ≤ 1 / 10 ^ 4 := by
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
    have e : ((10 : ℝ) ^ 6) ^ (7 / 8 : ℝ) = 10 ^ (21 / 4 : ℝ) := by
      rw [← Real.rpow_natCast 10 6, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [e]
    calc (1 / 10 ^ 4 : ℝ)⁻¹ = 10 ^ (4 : ℝ) := by norm_num
      _ ≤ 10 ^ (21 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  linarith

lemma h_a_eq : h a = a * (h a / a) := by
  field_simp [hw.a_pos.ne']

/-- `u ≥ a (1 - ε)`. -/
lemma u_ge : a * (1 - h a / a) ≤ u := by
  have h1 : h u ≤ h a := hw.win.mono' hw.u_pos hw.u_lt_a.le
  have := hw.a_sub_u
  have e : a * (1 - h a / a) = a - h a := by field_simp [hw.a_pos.ne']
  rw [e]; linarith

/-- (i), second part: `a/u ≤ (1 - ε)⁻¹`. -/
theorem a_div_u_le : a / u ≤ (1 - h a / a)⁻¹ := by
  have hε := hw.eps_le
  rw [div_le_iff₀ hw.u_pos, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
  linarith [hw.u_ge]

lemma one_le_a_div_u : 1 ≤ a / u := by
  rw [le_div_iff₀ hw.u_pos]; linarith [hw.u_lt_a]

/-- `(1 - ε)⁻¹ ≤ 1 + 1.0002 ε`. -/
lemma inv_one_sub_le : (1 - h a / a)⁻¹ ≤ 1 + 1.0002 * (h a / a) := by
  have hε := hw.eps_le; have hε0 := hw.eps_pos
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

lemma a_div_u_le' : a / u ≤ 1 + 1.0002 * (h a / a) := hw.a_div_u_le.trans hw.inv_one_sub_le

/-- (i), first part: `(u/a)^{1/8} ≤ M ≤ 1`. -/
theorem massM_bounds : (u / a) ^ (1 / 8 : ℝ) ≤ massM h a u ∧ massM h a u ≤ 1 := by
  have hu := hw.u_pos; have hua := hw.u_lt_a.le
  have hcont : ContinuousOn (fun v : ℝ => (h v)⁻¹) (Icc u a) :=
    (hw.win.cont.mono fun v hv => lt_of_lt_of_le hu hv.1).inv₀
      fun v hv => (hw.win.pos v (lt_of_lt_of_le hu hv.1)).ne'
  have hint : IntervalIntegrable (fun v : ℝ => (h v)⁻¹) volume u a :=
    (hcont.mono (by rw [uIcc_of_le hua])).intervalIntegrable
  have hha := hw.win.pos a hw.a_pos
  have hhu := hw.win.pos u hu
  constructor
  · have hmono : ∫ v in u..a, (h a)⁻¹ ≤ massM h a u := by
      apply intervalIntegral.integral_mono_on hua intervalIntegrable_const hint
      intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le hu hv.1
      exact inv_anti₀ (hw.win.pos v hv0) (hw.win.mono' hv0 hv.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hw.a_sub_u] at hmono
    have hr := hw.win.ratio' hu hua
    have : (u / a) ^ (1 / 8 : ℝ) ≤ h u * (h a)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hha]; exact hr
    linarith
  · have hmono : massM h a u ≤ ∫ v in u..a, (h u)⁻¹ := by
      apply intervalIntegral.integral_mono_on hua hint intervalIntegrable_const
      intro v hv
      exact inv_anti₀ hhu (hw.win.mono' hu hv.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hw.a_sub_u, mul_inv_cancel₀ hhu.ne']
      at hmono
    exact hmono

lemma continuousOn_inv_h : ContinuousOn (fun v : ℝ => (h v)⁻¹) (Icc u a) :=
  (hw.win.cont.mono fun v hv => lt_of_lt_of_le hw.u_pos hv.1).inv₀
    fun v hv => (hw.win.pos v (lt_of_lt_of_le hw.u_pos hv.1)).ne'

lemma intervalIntegrable_inv_h : IntervalIntegrable (fun v : ℝ => (h v)⁻¹) volume u a :=
  (hw.continuousOn_inv_h.mono (by rw [uIcc_of_le hw.u_lt_a.le])).intervalIntegrable

lemma continuousOn_ratio_cpow (s : ℂ) :
    ContinuousOn (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s) (Icc u a) := fun v hv => by
  have hv0 : 0 < v := by linarith [hv.1, hw.u_pos]
  have h1 : ContinuousAt (fun v : ℝ => a / v) v := continuousAt_const.div continuousAt_id hv0.ne'
  have h2 := continuousAt_ofReal_cpow_const (a / v) s (Or.inr (div_pos hw.a_pos hv0).ne')
  exact (h2.comp h1).continuousWithinAt

lemma continuousOn_inv_hC : ContinuousOn (fun v : ℝ => (((h v)⁻¹ : ℝ) : ℂ)) (Icc u a) :=
  Complex.continuous_ofReal.comp_continuousOn hw.continuousOn_inv_h

lemma intervalIntegrable_weight (s : ℂ) :
    IntervalIntegrable (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ)) volume u a := by
  have hcont : ContinuousOn (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ))
      (Icc u a) := (hw.continuousOn_ratio_cpow s).mul hw.continuousOn_inv_hC
  exact (hcont.mono (by rw [uIcc_of_le hw.u_lt_a.le])).intervalIntegrable

/-- `(a/u)^σ ≤ 1.0005` for `σ ≤ 2`. -/
lemma a_div_u_rpow_le' {σ : ℝ} (hσ : σ ≤ 2) : (a / u) ^ σ ≤ 1.0005 := by
  have hε := hw.eps_le; have hε0 := hw.eps_pos
  have h1 := hw.one_le_a_div_u
  calc (a / u) ^ σ ≤ (a / u) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hσ
    _ ≤ (1 + 1.0002 * (h a / a)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hw.a_div_u_le' (by norm_num)
    _ ≤ 1.0005 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith

/-- **(ii)**: `|w_a(s)| ≤ (a/u_a)^σ M ≤ 1 + 1.02 σ ε` for `0 ≤ σ ≤ 2`. -/
theorem norm_weight_le {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖weight h a u s‖ ≤ (a / u) ^ s.re * massM h a u ∧
      (a / u) ^ s.re * massM h a u ≤ 1 + 1.02 * s.re * (h a / a) := by
  have hu := hw.u_pos; have hua := hw.u_lt_a.le
  have hM := hw.massM_bounds
  have hM0 : 0 ≤ massM h a u := le_trans (Real.rpow_nonneg (div_pos hu hw.a_pos).le _) hM.1
  constructor
  · unfold weight
    have hint := hw.intervalIntegrable_inv_h
    calc _ ≤ ∫ v in u..a, (a / u) ^ s.re * (h v)⁻¹ := by
          refine intervalIntegral.norm_integral_le_of_norm_le hua ?_ (hint.const_mul _)
          refine Filter.Eventually.of_forall fun v hv => ?_
          have hv0 : 0 < v := by linarith [hv.1]
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hw.a_pos hv0),
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
              (hw.win.pos v hv0).le)]
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (hw.win.pos v hv0).le)
          apply Real.rpow_le_rpow (div_pos hw.a_pos hv0).le _ hσ0
          exact div_le_div_of_nonneg_left hw.a_pos.le hu hv.1.le
      _ = (a / u) ^ s.re * massM h a u := by
          rw [intervalIntegral.integral_const_mul]; rfl
  · have hε := hw.eps_le; have hε0 := hw.eps_pos
    have h1 : (a / u) ^ s.re ≤ (1 + 1.0002 * (h a / a)) ^ s.re :=
      Real.rpow_le_rpow (by linarith [hw.one_le_a_div_u]) hw.a_div_u_le' hσ0
    have h2 := one_add_rpow_le (y := 1.0002 * (h a / a)) (by positivity) (by linarith) hσ0 hσ2
    have h3 : (a / u) ^ s.re * massM h a u ≤ (a / u) ^ s.re :=
      mul_le_of_le_one_right (Real.rpow_nonneg (by linarith [hw.one_le_a_div_u]) _) hM.2
    have : 1.002 * s.re * (1.0002 * (h a / a)) ≤ 1.02 * s.re * (h a / a) := by
      have := mul_nonneg hσ0 hε0.le
      nlinarith
    linarith

/-- **(iv)**: `|1 - w_a(s)| ≤ 1.01 (|s| + 1/8) ε` for `0 ≤ σ ≤ 2`. -/
theorem norm_one_sub_weight_le {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖1 - weight h a u s‖ ≤ 1.01 * (‖s‖ + 1 / 8) * (h a / a) := by
  have hu := hw.u_pos; have hua := hw.u_lt_a.le; have ha := hw.a_pos
  have hε := hw.eps_le; have hε0 := hw.eps_pos
  have hM := hw.massM_bounds
  have hint := hw.intervalIntegrable_inv_h
  have hintC : IntervalIntegrable (fun v : ℝ => (((h v)⁻¹ : ℝ) : ℂ)) volume u a :=
    (hw.continuousOn_inv_hC.mono (by rw [uIcc_of_le hua])).intervalIntegrable
  have hMC : ∫ v in u..a, (((h v)⁻¹ : ℝ) : ℂ) = (massM h a u : ℂ) := by
    rw [intervalIntegral.integral_ofReal]; rfl
  have hsplit : 1 - weight h a u s = ((1 - massM h a u : ℝ) : ℂ) +
      ∫ v in u..a, ((((h v)⁻¹ : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_sub hintC (hw.intervalIntegrable_weight s), hMC]
    unfold weight; push_cast; ring
  rw [hsplit]
  -- `1 - M ≤ 1.0002 ε/8`
  have h1M : 1 - massM h a u ≤ 1.0002 * (1 / 8) * (h a / a) := by
    have hy : (a / u) ^ (1 / 8 : ℝ) ≤ 1 + 1 / 8 * (1.0002 * (h a / a)) := by
      calc (a / u) ^ (1 / 8 : ℝ) ≤ (1 + 1.0002 * (h a / a)) ^ (1 / 8 : ℝ) :=
            Real.rpow_le_rpow (by linarith [hw.one_le_a_div_u]) hw.a_div_u_le' (by norm_num)
        _ ≤ 1 + 1 / 8 * (1.0002 * (h a / a)) :=
            rpow_one_add_le_one_add_mul_self (by nlinarith) (by norm_num) (by norm_num)
    have hinv : (u / a) ^ (1 / 8 : ℝ) = ((a / u) ^ (1 / 8 : ℝ))⁻¹ := by
      rw [← Real.inv_rpow (div_pos ha hu).le, inv_div]
    have hpos : 0 < (a / u) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (div_pos ha hu) _
    have : 1 - 1.0002 * (1 / 8) * (h a / a) ≤ (u / a) ^ (1 / 8 : ℝ) := by
      rw [hinv, inv_eq_one_div, le_div_iff₀ hpos]
      have hc : 0 ≤ 1.0002 * (1 / 8) * (h a / a) := by positivity
      have hc1 : 1.0002 * (1 / 8) * (h a / a) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy
        (by linarith : (0:ℝ) ≤ 1 - 1.0002 * (1 / 8) * (h a / a))]
    linarith [hM.1]
  have h1M0 : 0 ≤ 1 - massM h a u := by linarith [hM.2]
  -- the integral
  have hpt : ∀ v ∈ Ioc u a, ‖(((h v)⁻¹ : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ)‖ ≤
      (1.0008 * ‖s‖ * (h a / a)) * (h v)⁻¹ := by
    intro v hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hav : 0 < a / v := div_pos ha hv0
    have hhv := (inv_nonneg.mpr (hw.win.pos v hv0).le)
    have e : (((h v)⁻¹ : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ) =
        -(((a / v : ℝ) : ℂ) ^ s - 1) * (((h v)⁻¹ : ℝ) : ℂ) := by ring
    rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhv]
    apply mul_le_mul_of_nonneg_right _ hhv
    rw [Oscillation.ofReal_cpow_eq_exp hav]
    have hlog0 : 0 ≤ Real.log (a / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith [hv.2])
    have hre : ((Real.log (a / v) : ℂ) * s).re = Real.log (a / v) * s.re := by simp
    refine (norm_cexp_sub_one_le_mul (z := (Real.log (a / v) : ℂ) * s)
      (by rw [hre]; positivity)).trans ?_
    rw [hre, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hlog : Real.log (a / v) ≤ 1.0002 * (h a / a) := by
      have h1 : Real.log (a / v) ≤ a / v - 1 := Real.log_le_sub_one_of_pos hav
      have h2 : a / v ≤ a / u := div_le_div_of_nonneg_left ha.le hu hv.1.le
      linarith [hw.a_div_u_le']
    have hexp : Real.exp (Real.log (a / v) * s.re) ≤ 1.0005 := by
      rw [Real.exp_mul, Real.exp_log hav]
      calc (a / v) ^ s.re ≤ (a / u) ^ s.re :=
            Real.rpow_le_rpow hav.le (div_le_div_of_nonneg_left ha.le hu hv.1.le) hσ0
        _ ≤ 1.0005 := hw.a_div_u_rpow_le' hσ2
    have hsn := norm_nonneg s
    calc Real.log (a / v) * ‖s‖ * Real.exp (Real.log (a / v) * s.re)
        ≤ (1.0002 * (h a / a)) * ‖s‖ * 1.0005 := by gcongr
      _ ≤ 1.0008 * ‖s‖ * (h a / a) := by nlinarith [mul_nonneg hsn hε0.le]
  have hI : ‖∫ v in u..a, ((((h v)⁻¹ : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ))‖
      ≤ 1.0008 * ‖s‖ * (h a / a) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hua
      (Filter.Eventually.of_forall fun v hv => hpt v hv) (hint.const_mul _)).trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_of_le_one_right (by positivity) hM.2
  calc _ ≤ ‖((1 - massM h a u : ℝ) : ℂ)‖ + ‖∫ v in u..a, ((((h v)⁻¹ : ℝ) : ℂ) -
        ((a / v : ℝ) : ℂ) ^ s * (((h v)⁻¹ : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 1.0002 * (1 / 8) * (h a / a) + 1.0008 * ‖s‖ * (h a / a) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1M0]
        exact add_le_add h1M hI
    _ ≤ 1.01 * (‖s‖ + 1 / 8) * (h a / a) := by
        have := mul_nonneg (norm_nonneg s) hε0.le
        nlinarith

/-- **(iv), second form**: `|1 - w_a(s)| ≤ 2 |t| ε` for `|t| ≥ 2` and `0 ≤ σ ≤ 2`. -/
theorem norm_one_sub_weight_le' {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖1 - weight h a u s‖ ≤ 2 * |s.im| * (h a / a) := by
  refine (hw.norm_one_sub_weight_le hσ0 hσ2).trans ?_
  have hε0 := hw.eps_pos
  have hs : ‖s‖ ≤ 3 / 2 * |s.im| := by
    have h1 : ‖s‖ ^ 2 ≤ (3 / 2 * |s.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have : s.im * s.im = |s.im| ^ 2 := by rw [sq_abs]; ring
      nlinarith
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have : 1.01 * (‖s‖ + 1 / 8) ≤ 2 * |s.im| := by linarith
  exact mul_le_mul_of_nonneg_right this hε0.le

/-- `ε = h(a)/a ≤ a^{1/8 - 1}`. -/
lemma eps_le_rpow : h a / a ≤ a ^ ((1 / 8 : ℝ) - 1) := by
  have ha := hw.a_pos
  rw [Real.rpow_sub ha, Real.rpow_one]
  exact div_le_div_of_nonneg_right (hw.win.le_rpow a ha) ha.le

end WeightHyp

end Weights

end
