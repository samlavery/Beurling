module

public import RequestProject.Beurling.OscMellin

/-!
# The weights of the absorbed elements (Section 4.1, bounds (i)–(iv) after (14))

For `a ∈ A`, the weight of `a` in the forward-window average `ρ_A(u) = #(A ∩ [u, u+h(u)])/h(u)`,
`h(u) = u^b`, `b = θ/2`, is

  `w_a(s) = a^s ∫_{u_a}^a u^{-s} g(u) du = ∫_{u_a}^a (a/u)^s g(u) du`,  `g = 1/h`,
  `u_a + h(u_a) = a`,

and `M = ∫_{u_a}^a g`. With `ε = a^{b-1}`, for `0 ≤ σ ≤ 2`:

* (i)  `(u_a/a)^b ≤ M ≤ 1` and `a/u_a ≤ (1 - ε)⁻¹`;
* (ii) `|w_a(s)| ≤ (a/u_a)^σ M ≤ 1 + 1.02 σ ε`;
* (iii) `|w_a(s)| ≤ 2.01 a^{1-b}/|t|` for `t ≠ 0`;
* (iv) `|1 - w_a(s)| ≤ 1.01 (|s| + b) ε`, hence `|1 - w_a(s)| ≤ 2 |t| ε` for `|t| ≥ 2`.

The paper assumes `a ≥ X₀/2`; here `a ≥ 10⁶` suffices, and `0 < b ≤ 1/4` (as `θ ≤ 1/2`).
-/

@[expose] public section

open Complex Set Filter MeasureTheory intervalIntegral

namespace Weights

/-- `M = ∫_{u}^{a} v^{-b} dv`. -/
noncomputable def massM (b a u : ℝ) : ℝ := ∫ v in u..a, v ^ (-b)

/-- `w_a(s) = ∫_{u}^{a} (a/v)^s v^{-b} dv`. -/
noncomputable def weight (b a u : ℝ) (s : ℂ) : ℂ :=
  ∫ v in u..a, ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ)

/-- The standing hypotheses: `0 < b ≤ 1/4`, `a ≥ 10⁶`, `u > 0` with `u + u^b = a`. -/
structure WeightHyp (b a u : ℝ) : Prop where
  b_pos : 0 < b
  b_le : b ≤ 1 / 4
  a_ge : 10 ^ 6 ≤ a
  u_pos : 0 < u
  u_eq : u + u ^ b = a

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

variable {b a u : ℝ} (h : WeightHyp b a u)
include h

lemma a_pos : 0 < a := by linarith [h.a_ge]

lemma u_lt_a : u < a := by
  have := Real.rpow_pos_of_pos h.u_pos b; linarith [h.u_eq]

lemma a_sub_u : a - u = u ^ b := by linarith [h.u_eq]

lemma eps_pos : 0 < a ^ (b - 1) := Real.rpow_pos_of_pos h.a_pos _

lemma eps_le : a ^ (b - 1) ≤ 1 / 10 ^ 4 := by
  have ha1 : 1 ≤ a := by linarith [h.a_ge]
  have h1 : a ^ (b - 1) ≤ a ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ha1 (by linarith [h.b_le])
  have h2 : a ^ (-(3 / 4 : ℝ)) ≤ ((10 : ℝ) ^ 6) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h.a_ge (by norm_num)
  have h3 : ((10 : ℝ) ^ 6) ^ (-(3 / 4 : ℝ)) ≤ 1 / 10 ^ 4 := by
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
    have e : ((10 : ℝ) ^ 6) ^ (3 / 4 : ℝ) = 10 ^ (9 / 2 : ℝ) := by
      rw [← Real.rpow_natCast 10 6, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [e]
    calc (1 / 10 ^ 4 : ℝ)⁻¹ = 10 ^ (4 : ℝ) := by norm_num
      _ ≤ 10 ^ (9 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  linarith

lemma a_rpow_b : a ^ b = a * a ^ (b - 1) := by
  rw [Real.rpow_sub h.a_pos, Real.rpow_one, mul_div_assoc', mul_div_cancel_left₀ _ h.a_pos.ne']

/-- `u ≥ a (1 - ε)`. -/
lemma u_ge : a * (1 - a ^ (b - 1)) ≤ u := by
  have h1 : u ^ b ≤ a ^ b := Real.rpow_le_rpow h.u_pos.le h.u_lt_a.le h.b_pos.le
  have := h.a_sub_u
  rw [h.a_rpow_b] at h1
  nlinarith

/-- (i), second part: `a/u ≤ (1 - ε)⁻¹`. -/
theorem a_div_u_le : a / u ≤ (1 - a ^ (b - 1))⁻¹ := by
  have hε := h.eps_le
  rw [div_le_iff₀ h.u_pos, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
  linarith [h.u_ge]

lemma one_le_a_div_u : 1 ≤ a / u := by
  rw [le_div_iff₀ h.u_pos]; linarith [h.u_lt_a]

/-- `(1 - ε)⁻¹ ≤ 1 + 1.0002 ε`. -/
lemma inv_one_sub_le : (1 - a ^ (b - 1))⁻¹ ≤ 1 + 1.0002 * a ^ (b - 1) := by
  have hε := h.eps_le; have hε0 := h.eps_pos
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

lemma a_div_u_le' : a / u ≤ 1 + 1.0002 * a ^ (b - 1) := h.a_div_u_le.trans h.inv_one_sub_le

/-- `(a/u)^σ ≤ 1.01` for `σ ≤ 2` (used with `(1 - ε)^{-2} ≤ 1.01`). -/
lemma a_div_u_rpow_le {σ : ℝ} (hσ : σ ≤ 2) : (a / u) ^ σ ≤ 1.01 := by
  have hε := h.eps_le; have hε0 := h.eps_pos
  have h1 := h.one_le_a_div_u
  calc (a / u) ^ σ ≤ (a / u) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hσ
    _ ≤ (1 + 1.0002 * a ^ (b - 1)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) h.a_div_u_le' (by norm_num)
    _ ≤ 1.01 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith

/-- (i), first part: `(u/a)^b ≤ M ≤ 1`. -/
theorem massM_bounds : (u / a) ^ b ≤ massM b a u ∧ massM b a u ≤ 1 := by
  have hu := h.u_pos; have hua := h.u_lt_a.le
  have hcont : ContinuousOn (fun v : ℝ => v ^ (-b)) (Icc u a) :=
    fun v hv => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  have hint : IntervalIntegrable (fun v : ℝ => v ^ (-b)) volume u a :=
    (hcont.mono (by rw [uIcc_of_le hua])).intervalIntegrable
  constructor
  · have hmono : ∫ v in u..a, a ^ (-b) ≤ massM b a u := by
      apply intervalIntegral.integral_mono_on hua intervalIntegral.intervalIntegrable_const hint
      intro v hv
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hv.1]) hv.2 (by linarith [h.b_pos])
    rw [intervalIntegral.integral_const, smul_eq_mul, h.a_sub_u] at hmono
    rw [Real.div_rpow hu.le h.a_pos.le, div_eq_mul_inv, ← Real.rpow_neg h.a_pos.le]
    exact hmono
  · have hmono : massM b a u ≤ ∫ v in u..a, u ^ (-b) := by
      apply intervalIntegral.integral_mono_on hua hint intervalIntegral.intervalIntegrable_const
      intro v hv
      exact Real.rpow_le_rpow_of_nonpos hu hv.1 (by linarith [h.b_pos])
    rw [intervalIntegral.integral_const, smul_eq_mul, h.a_sub_u, ← Real.rpow_add hu] at hmono
    simpa using hmono

lemma intervalIntegrable_rpow : IntervalIntegrable (fun v : ℝ => v ^ (-b)) volume u a := by
  have hcont : ContinuousOn (fun v : ℝ => v ^ (-b)) (Icc u a) := fun v hv =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1, h.u_pos]))).continuousWithinAt
  exact (hcont.mono (by rw [uIcc_of_le h.u_lt_a.le])).intervalIntegrable

lemma continuousOn_ratio_cpow (s : ℂ) :
    ContinuousOn (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s) (Icc u a) := fun v hv => by
  have hv0 : 0 < v := by linarith [hv.1, h.u_pos]
  have h1 : ContinuousAt (fun v : ℝ => a / v) v := continuousAt_const.div continuousAt_id hv0.ne'
  have h2 := continuousAt_ofReal_cpow_const (a / v) s (Or.inr (div_pos h.a_pos hv0).ne')
  exact (h2.comp h1).continuousWithinAt

lemma intervalIntegrable_weight (s : ℂ) :
    IntervalIntegrable (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ)) volume u a := by
  have hcont : ContinuousOn (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ))
      (Icc u a) := by
    refine (h.continuousOn_ratio_cpow s).mul ?_
    intro v hv
    exact (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1, h.u_pos])))).continuousWithinAt
  exact (hcont.mono (by rw [uIcc_of_le h.u_lt_a.le])).intervalIntegrable

/-- `(a/u)^σ ≤ 1.0005` for `σ ≤ 2`. -/
lemma a_div_u_rpow_le' {σ : ℝ} (hσ : σ ≤ 2) : (a / u) ^ σ ≤ 1.0005 := by
  have hε := h.eps_le; have hε0 := h.eps_pos
  have h1 := h.one_le_a_div_u
  calc (a / u) ^ σ ≤ (a / u) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hσ
    _ ≤ (1 + 1.0002 * a ^ (b - 1)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) h.a_div_u_le' (by norm_num)
    _ ≤ 1.0005 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith

/-- **(ii)**: `|w_a(s)| ≤ (a/u_a)^σ M ≤ 1 + 1.02 σ ε` for `0 ≤ σ ≤ 2`. -/
theorem norm_weight_le {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖weight b a u s‖ ≤ (a / u) ^ s.re * massM b a u ∧
      (a / u) ^ s.re * massM b a u ≤ 1 + 1.02 * s.re * a ^ (b - 1) := by
  have hu := h.u_pos; have hua := h.u_lt_a.le
  have hM := h.massM_bounds
  have hM0 : 0 ≤ massM b a u := le_trans (Real.rpow_nonneg (div_pos hu h.a_pos).le _) hM.1
  constructor
  · unfold weight
    have hint := h.intervalIntegrable_rpow
    calc _ ≤ ∫ v in u..a, (a / u) ^ s.re * v ^ (-b) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hua ?_ (hint.const_mul _)
          refine Filter.Eventually.of_forall fun v hv => ?_
          have hv0 : 0 < v := by linarith [hv.1]
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos h.a_pos hv0),
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0.le _)
          apply Real.rpow_le_rpow (div_pos h.a_pos hv0).le _ hσ0
          exact div_le_div_of_nonneg_left h.a_pos.le hu hv.1.le
      _ = (a / u) ^ s.re * massM b a u := by
          rw [intervalIntegral.integral_const_mul]; rfl
  · have hε := h.eps_le; have hε0 := h.eps_pos
    have h1 : (a / u) ^ s.re ≤ (1 + 1.0002 * a ^ (b - 1)) ^ s.re :=
      Real.rpow_le_rpow (by linarith [h.one_le_a_div_u]) h.a_div_u_le' hσ0
    have h2 := one_add_rpow_le (y := 1.0002 * a ^ (b - 1)) (by positivity) (by linarith) hσ0 hσ2
    have h3 : (a / u) ^ s.re * massM b a u ≤ (a / u) ^ s.re :=
      mul_le_of_le_one_right (Real.rpow_nonneg (by linarith [h.one_le_a_div_u]) _) hM.2
    have : 1.002 * s.re * (1.0002 * a ^ (b - 1)) ≤ 1.02 * s.re * a ^ (b - 1) := by
      have := mul_nonneg hσ0 hε0.le
      nlinarith
    linarith

/-- Closed form: `w_a(s) = a^s (a^{1-s-b} - u^{1-s-b})/(1-s-b)` for `t ≠ 0`. -/
lemma weight_eq {s : ℂ} (ht : s.im ≠ 0) :
    weight b a u s = (a : ℂ) ^ s *
      (((a : ℂ) ^ (-s - b + 1) - (u : ℂ) ^ (-s - b + 1)) / (-s - b + 1)) := by
  have hu := h.u_pos; have ha := h.a_pos
  unfold weight
  have hpt : EqOn (fun v : ℝ => ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ))
      (fun v : ℝ => (a : ℂ) ^ s * (v : ℂ) ^ (-s - b)) (uIcc u a) := by
    intro v hv
    rw [uIcc_of_le h.u_lt_a.le] at hv
    have hv0 : 0 < v := by linarith [hv.1]
    simp only
    rw [Complex.ofReal_cpow hv0.le, Oscillation.ofReal_cpow_eq_exp (div_pos ha hv0),
      Oscillation.ofReal_cpow_eq_exp hv0, Oscillation.ofReal_cpow_eq_exp ha,
      Oscillation.ofReal_cpow_eq_exp hv0, ← Complex.exp_add, ← Complex.exp_add,
      Real.log_div ha.ne' hv0.ne']
    congr 1; push_cast; ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, integral_cpow]
  right
  refine ⟨fun e => ht ?_, fun h0 => ?_⟩
  · have := congrArg Complex.im e; simp at this; exact this
  · rw [uIcc_of_le h.u_lt_a.le] at h0; linarith [h0.1]

/-- **(iii)**: `|w_a(s)| ≤ 2.01 a^{1-b}/|t|` for `t ≠ 0` and `σ ≤ 2`. -/
theorem norm_weight_le_div {s : ℂ} (hσ2 : s.re ≤ 2) (ht : s.im ≠ 0) :
    ‖weight b a u s‖ ≤ 2.01 * a ^ (1 - b) / |s.im| := by
  have hu := h.u_pos; have ha := h.a_pos
  have htp : 0 < |s.im| := abs_pos.mpr ht
  rw [h.weight_eq ht, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha]
  have hden : |s.im| ≤ ‖-s - (b : ℂ) + 1‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp
  have hnum : ‖(a : ℂ) ^ (-s - b + 1) - (u : ℂ) ^ (-s - b + 1)‖ ≤
      a ^ (1 - s.re - b) + u ^ (1 - s.re - b) := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    congr 2 <;> simp <;> ring
  have e1 : a ^ s.re * a ^ (1 - s.re - b) = a ^ (1 - b) := by
    rw [← Real.rpow_add ha]; ring_nf
  have e2 : a ^ s.re * u ^ (1 - s.re - b) = (a / u) ^ s.re * u ^ (1 - b) := by
    rw [Real.div_rpow ha.le hu.le, show 1 - s.re - b = (1 - b) - s.re by ring,
      Real.rpow_sub hu]
    have := Real.rpow_pos_of_pos hu s.re
    field_simp
  have hub : u ^ (1 - b) ≤ a ^ (1 - b) :=
    Real.rpow_le_rpow hu.le h.u_lt_a.le (by linarith [h.b_le])
  have hau := h.a_div_u_rpow_le' hσ2
  have hpos1 : 0 ≤ (a / u) ^ s.re := Real.rpow_nonneg (div_pos ha hu).le _
  have hA : 0 ≤ a ^ (1 - b) := Real.rpow_nonneg ha.le _
  have hnum' : a ^ s.re * ‖(a : ℂ) ^ (-s - b + 1) - (u : ℂ) ^ (-s - b + 1)‖ ≤ 2.01 * a ^ (1 - b) := by
    calc _ ≤ a ^ s.re * (a ^ (1 - s.re - b) + u ^ (1 - s.re - b)) :=
          mul_le_mul_of_nonneg_left hnum (Real.rpow_nonneg ha.le _)
      _ = a ^ (1 - b) + (a / u) ^ s.re * u ^ (1 - b) := by rw [mul_add, e1, e2]
      _ ≤ a ^ (1 - b) + 1.0005 * a ^ (1 - b) := by gcongr
      _ ≤ 2.01 * a ^ (1 - b) := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ (htp.trans_le hden) htp]
  calc a ^ s.re * ‖(a : ℂ) ^ (-s - b + 1) - (u : ℂ) ^ (-s - b + 1)‖ * |s.im|
      ≤ 2.01 * a ^ (1 - b) * |s.im| := mul_le_mul_of_nonneg_right hnum' htp.le
    _ ≤ 2.01 * a ^ (1 - b) * ‖-s - (b : ℂ) + 1‖ := by gcongr

/-- **(iv)**: `|1 - w_a(s)| ≤ 1.01 (|s| + b) ε` for `0 ≤ σ ≤ 2`. -/
theorem norm_one_sub_weight_le {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖1 - weight b a u s‖ ≤ 1.01 * (‖s‖ + b) * a ^ (b - 1) := by
  have hu := h.u_pos; have hua := h.u_lt_a.le; have ha := h.a_pos
  have hε := h.eps_le; have hε0 := h.eps_pos
  have hM := h.massM_bounds
  have hint := h.intervalIntegrable_rpow
  have hintC : IntervalIntegrable (fun v : ℝ => ((v ^ (-b) : ℝ) : ℂ)) volume u a :=
    (ContinuousOn.intervalIntegrable (fun v hv => (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const _ _ (Or.inl (by
        rw [uIcc_of_le hua] at hv; linarith [hv.1])))).continuousWithinAt))
  have hMC : ∫ v in u..a, ((v ^ (-b) : ℝ) : ℂ) = (massM b a u : ℂ) := by
    rw [intervalIntegral.integral_ofReal]; rfl
  have hsplit : 1 - weight b a u s = ((1 - massM b a u : ℝ) : ℂ) +
      ∫ v in u..a, (((v ^ (-b) : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_sub hintC (h.intervalIntegrable_weight s), hMC]
    unfold weight; push_cast; ring
  rw [hsplit]
  -- `1 - M ≤ 1.0002 b ε`
  have h1M : 1 - massM b a u ≤ 1.0002 * b * a ^ (b - 1) := by
    have hb := h.b_pos; have hb4 := h.b_le
    have hy : (a / u) ^ b ≤ 1 + b * (1.0002 * a ^ (b - 1)) := by
      calc (a / u) ^ b ≤ (1 + 1.0002 * a ^ (b - 1)) ^ b :=
            Real.rpow_le_rpow (by linarith [h.one_le_a_div_u]) h.a_div_u_le' hb.le
        _ ≤ 1 + b * (1.0002 * a ^ (b - 1)) :=
            rpow_one_add_le_one_add_mul_self (by nlinarith) hb.le (by linarith)
    have hinv : (u / a) ^ b = ((a / u) ^ b)⁻¹ := by
      rw [← Real.inv_rpow (div_pos ha hu).le, inv_div]
    have hpos : 0 < (a / u) ^ b := Real.rpow_pos_of_pos (div_pos ha hu) _
    have : 1 - 1.0002 * b * a ^ (b - 1) ≤ (u / a) ^ b := by
      rw [hinv, inv_eq_one_div, le_div_iff₀ hpos]
      have hc : 0 ≤ 1.0002 * b * a ^ (b - 1) := by positivity
      have hc1 : 1.0002 * b * a ^ (b - 1) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy (by linarith : (0:ℝ) ≤ 1 - 1.0002 * b * a ^ (b - 1))]
    linarith [hM.1]
  have h1M0 : 0 ≤ 1 - massM b a u := by linarith [hM.2]
  -- the integral
  have hpt : ∀ v ∈ Ioc u a, ‖((v ^ (-b) : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ)‖ ≤
      (1.0008 * ‖s‖ * a ^ (b - 1)) * v ^ (-b) := by
    intro v hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hav : 0 < a / v := div_pos ha hv0
    have e : ((v ^ (-b) : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ) =
        -(((a / v : ℝ) : ℂ) ^ s - 1) * ((v ^ (-b) : ℝ) : ℂ) := by ring
    rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0.le _)
    rw [Oscillation.ofReal_cpow_eq_exp hav]
    have hlog0 : 0 ≤ Real.log (a / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith [hv.2])
    have hre : ((Real.log (a / v) : ℂ) * s).re = Real.log (a / v) * s.re := by simp
    refine (norm_cexp_sub_one_le_mul (z := (Real.log (a / v) : ℂ) * s)
      (by rw [hre]; positivity)).trans ?_
    rw [hre, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hlog : Real.log (a / v) ≤ 1.0002 * a ^ (b - 1) := by
      have h1 : Real.log (a / v) ≤ a / v - 1 := Real.log_le_sub_one_of_pos hav
      have h2 : a / v ≤ a / u := div_le_div_of_nonneg_left ha.le hu hv.1.le
      linarith [h.a_div_u_le']
    have hexp : Real.exp (Real.log (a / v) * s.re) ≤ 1.0005 := by
      rw [Real.exp_mul, Real.exp_log hav]
      calc (a / v) ^ s.re ≤ (a / u) ^ s.re :=
            Real.rpow_le_rpow hav.le (div_le_div_of_nonneg_left ha.le hu hv.1.le) hσ0
        _ ≤ 1.0005 := h.a_div_u_rpow_le' hσ2
    have hsn := norm_nonneg s
    calc Real.log (a / v) * ‖s‖ * Real.exp (Real.log (a / v) * s.re)
        ≤ (1.0002 * a ^ (b - 1)) * ‖s‖ * 1.0005 := by gcongr
      _ ≤ 1.0008 * ‖s‖ * a ^ (b - 1) := by nlinarith [mul_nonneg hsn hε0.le]
  have hI : ‖∫ v in u..a, (((v ^ (-b) : ℝ) : ℂ) - ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ))‖
      ≤ 1.0008 * ‖s‖ * a ^ (b - 1) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hua
      (Filter.Eventually.of_forall fun v hv => hpt v hv) (hint.const_mul _)).trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_of_le_one_right (by positivity) hM.2
  calc _ ≤ ‖((1 - massM b a u : ℝ) : ℂ)‖ + ‖∫ v in u..a, (((v ^ (-b) : ℝ) : ℂ) -
        ((a / v : ℝ) : ℂ) ^ s * ((v ^ (-b) : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 1.0002 * b * a ^ (b - 1) + 1.0008 * ‖s‖ * a ^ (b - 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1M0]
        exact add_le_add h1M hI
    _ ≤ 1.01 * (‖s‖ + b) * a ^ (b - 1) := by
        have := mul_nonneg (norm_nonneg s) hε0.le
        have := mul_nonneg h.b_pos.le hε0.le
        nlinarith

/-- **(iv), second form**: `|1 - w_a(s)| ≤ 2 |t| ε` for `|t| ≥ 2` and `0 ≤ σ ≤ 2`. -/
theorem norm_one_sub_weight_le' {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖1 - weight b a u s‖ ≤ 2 * |s.im| * a ^ (b - 1) := by
  refine (h.norm_one_sub_weight_le hσ0 hσ2).trans ?_
  have hε0 := h.eps_pos
  have hs : ‖s‖ ≤ 3 / 2 * |s.im| := by
    have h1 : ‖s‖ ^ 2 ≤ (3 / 2 * |s.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have : s.im * s.im = |s.im| ^ 2 := by rw [sq_abs]; ring
      nlinarith
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have : 1.01 * (‖s‖ + b) ≤ 2 * |s.im| := by linarith [h.b_le]
  exact mul_le_mul_of_nonneg_right this hε0.le

end WeightHyp

end Weights

end
