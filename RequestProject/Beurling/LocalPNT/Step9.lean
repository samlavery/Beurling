module

public import RequestProject.Beurling.LocalPNT.Step10Main
public import RequestProject.Beurling.LocalPNT.ContourGen
public import RequestProject.Beurling.LocalPNT.Smoothing
public import RequestProject.Beurling.LocalPNT.Kernel9
public import RequestProject.Beurling.LocalPNT.Num10

/-!
# Theorem 5.24(i): Step 9 (smoothed Perron formula)

With `T = e^{√log v}`, `T₁ = e^{2√log v}` and `c = 1 + 17 log Λ_p/Λ_p`, the smoothed sum
`∑ H(log(v/p^k))/(k p^k) - ∫ H(log(v/u)) dΠ₀/u` (`H = Hs T`) equals
`(1/2π) ∫ F9(c+it) Gright(c+it) dt` (`identity_Gright`), whose contour shift
(`contour_estimate_gen`, with `Q = v^{s-1} ĥ₀((s-1)/T) · dslope 𝔊₁ 1`, using `𝔊₁(1) = 0`) and
the smoothing error (`smoothing_error`) give (i) at the top height `v = y` (`lp_i_top_of`).
The numerics are isolated as hypotheses `N1`–`N3` of `lp_i_top_of`.
-/

@[expose] public section

open Set Real Complex MeasureTheory Construction Filter Topology
open scoped Interval

namespace LocalPNT

/-! ### Bounds for `F9` -/

section F9

variable {v T : ℝ}

theorem norm_F9_le_gen (hT : 0 < T) (hv : 1 < v) {s : ℂ} (hs : s ≠ 1) :
    ‖F9 v T s‖ ≤ v ^ (s.re - 1) * (76 ^ 19 * Real.exp (2 * |s.re - 1| / T)) / ‖s - 1‖ ∧
    ‖F9 v T s‖ ≤ v ^ (s.re - 1) * (76 ^ 19 * Real.exp (2 * |s.re - 1| / T)) * T ^ 19 /
      ‖s - 1‖ ^ 20 := by
  have hr : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have hk := norm_hhat0_contour_le hT s
  rw [Complex.sub_re, Complex.one_re] at hk
  rw [norm_F9 hv]
  set r := ‖s - 1‖
  set E := 76 ^ 19 * Real.exp (2 * |s.re - 1| / T)
  have hE : 0 ≤ E := by positivity
  have hv' : 0 ≤ v ^ (s.re - 1) := Real.rpow_nonneg (by linarith) _
  have hk' : ‖hhat0 ((s - 1) / T)‖ ≤ E / (1 + r / T) ^ 19 := by
    simpa [E, mul_div_assoc] using hk
  have h1 : E / (1 + r / T) ^ 19 ≤ E := div_le_self hE (one_le_pow₀ (by
    have : 0 ≤ r / T := by positivity
    linarith))
  have h2 : E / (1 + r / T) ^ 19 ≤ E * T ^ 19 / r ^ 19 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), mul_assoc E]
    show E * r ^ 19 ≤ E * (T ^ 19 * (1 + r / T) ^ 19)
    apply mul_le_mul_of_nonneg_left _ hE
    have : r ≤ T * (1 + r / T) := by rw [mul_add, mul_one, mul_div_cancel₀ _ hT.ne']; linarith
    calc r ^ 19 ≤ (T * (1 + r / T)) ^ 19 := pow_le_pow_left₀ hr.le this 19
      _ = T ^ 19 * (1 + r / T) ^ 19 := mul_pow _ _ _
  constructor
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hk'.trans h1) hv') hr.le
  · have := mul_le_mul_of_nonneg_left (hk'.trans h2) hv'
    calc v ^ (s.re - 1) * ‖hhat0 ((s - 1) / T)‖ / r ≤ v ^ (s.re - 1) * (E * T ^ 19 / r ^ 19) / r :=
          div_le_div_of_nonneg_right this hr.le
      _ = _ := by field_simp

end F9

/-- `c = 1 + 17 log L/L ≤ 9/8` for `L ≥ 10⁸`. -/
lemma c_le_nine_eighths {L : ℝ} (hL : 10 ^ 8 ≤ L) : 1 + 17 * Real.log L / L ≤ 9 / 8 := by
  have hl := Real.log_le_rpow_div (x := L) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2' : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : (10 : ℝ) ^ 4 ≤ L ^ (1 / 2 : ℝ) := by
    have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
      rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num] at this
  rw [div_div_eq_mul_div] at hl
  have : 17 * Real.log L / L ≤ 1 / 8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- `log(1/(c - 1)) ≤ log L` for `c - 1 = 17 log L/L`, `L ≥ 10⁸`. -/
lemma log_inv_c_sub_one_le {L : ℝ} (hL : 10 ^ 8 ≤ L) :
    Real.log (1 / (1 + 17 * Real.log L / L - 1)) ≤ Real.log L := by
  have hl : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hpos : 0 < 17 * Real.log L / L := by positivity
  rw [show 1 + 17 * Real.log L / L - 1 = 17 * Real.log L / L by ring]
  apply Real.log_le_log (by positivity)
  rw [one_div_div, div_le_iff₀ (by positivity)]
  nlinarith

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

set_option maxHeartbeats 8000000 in
/-- **Theorem 5.24(i) at the top height** (Step 9), with the numerics `N1`–`N3` as hypotheses
(they are discharged in `Num9`). -/
theorem lp_i_top_of
    (hL : 10 ^ 5 * Real.log X₀ ^ 2 * Real.log (Real.log X₀) ^ 2 ≤ Real.log y)
    (N1 : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (N2 : Lt (Real.exp (2 * Real.sqrt (Real.log y)) + 1) ≤
      logTy (Real.log X₀) (Real.log y) + 1)
    (N3 : ∀ a θ' : ℝ, 0.9 * (cZF (Real.log X₀) / (2 * Real.sqrt (Real.log y) + 442 +
        2 * Real.log (Real.log X₀) + Real.log (2 * Real.sqrt (Real.log y)))) ≤ a → θ' ≤ 0.51 →
      (1 / (2 * π)) * (GLam (Real.log X₀) (2 * Real.sqrt (Real.log y)) *
          (Real.exp (-(a * Real.log y)) * 76 ^ 19 * 1.0001 *
            (4 * Real.log (1 + Real.exp (2 * Real.sqrt (Real.log y)) / a)))
        + 2 * GLam (Real.log X₀) (2 * Real.sqrt (Real.log y)) *
          (Real.log y ^ 17 * 76 ^ 19 * 3 * Real.exp (-(19 * Real.sqrt (Real.log y))) /
            Real.exp (2 * Real.sqrt (Real.log y)))
        + (1.5 * Real.log (Real.log y) + 8) *
          (2 * (Real.log y ^ 17 * 76 ^ 19 * 3 / 19 *
            Real.exp (-(19 * Real.sqrt (Real.log y))))))
      + 10 / Real.exp (Real.sqrt (Real.log y)) + 2000 * Real.exp ((θ' - 1) * Real.log y)
      ≤ Real.exp 97 * Real.log X₀ ^ 2 *
        Real.exp (-(cLP (Real.log X₀) * Real.sqrt (Real.log y)))) :
    |piRecip P y - pi0Recip y| ≤
      Real.exp 97 * Real.log X₀ ^ 2 *
        Real.exp (-(cLP (Real.log X₀) * Real.sqrt (Real.log y))) := by
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log y with hLdef
  have hX := h.logX
  have hl18 := Num10.eighteen_le_log hX
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hL21 : 10 ^ 21 ≤ L := by
    have h1 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have h2 : (324 : ℝ) ≤ Real.log Λ ^ 2 := by nlinarith
    have h3 : (10 : ℝ) ^ 16 * 324 ≤ Λ ^ 2 * Real.log Λ ^ 2 :=
      mul_le_mul h1 h2 (by norm_num) (by positivity)
    nlinarith
  have hΛL : Λ + 1 ≤ L := by
    have h1 : Λ + 1 ≤ Λ ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 10 ^ 5 * Real.log Λ ^ 2 := by nlinarith
    have : Λ ^ 2 ≤ 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 := by nlinarith
    linarith
  have hy1 : 1 < y := by
    by_contra hc; push_neg at hc
    have := Real.log_nonpos hy0.le hc; linarith
  set s0 := Real.sqrt L with hs0def
  have hsq : s0 * s0 = L := Real.mul_self_sqrt (by linarith)
  have hs0 : 10 ^ 10 ≤ s0 := (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  set T := Real.exp s0 with hTdef
  have hT4 : 4 ≤ T := by have := Real.add_one_le_exp s0; linarith
  have hT0 : 0 < T := by linarith
  set T₁ := Real.exp (2 * s0) with hT₁def
  have hT1 : 1 ≤ T₁ := Real.one_le_exp (by linarith)
  have hT10 : 0 < T₁ := by linarith
  obtain ⟨G, hGd, hGe, hGr⟩ := h.exists_G1 hT1 N1 N2
  have hG1 : G 1 = 0 := h.G1_one hT1 hGd hGe hGr
  -- the abscissa `c`
  set c := 1 + 17 * Real.log L / L with hcdef
  have hc1 : c1 y < c := h.c1_lt_c (v := y) (by have := Real.exp_one_lt_d9; linarith) le_rfl hy0
  have hc98 : c ≤ 9 / 8 := c_le_nine_eighths (by linarith)
  have hc1' := h.c1_gt
  have hc1'' : 1 < c := by linarith
  -- the smoothing error
  have h2X : 2 * (X₀ : ℝ) ≤ y := by
    have hX0 := h.X0_pos
    rw [← Real.exp_log hX0, ← Real.exp_log hy0, ← hΛdef, ← hLdef]
    have : 2 * Real.exp Λ ≤ Real.exp (Λ + 1) := by
      rw [Real.exp_add]; have := Real.exp_one_gt_d9; nlinarith [Real.exp_pos Λ]
    exact this.trans (Real.exp_le_exp.2 hΛL)
  obtain ⟨-, hsm⟩ := h.smoothing_error h2X le_rfl hT4 (continuous_Hs hT0)
    (fun z => ⟨Hs_nonneg hT0 z, Hs_le_one hT0 z⟩) (fun z hz => Hs_eq_one hT0 hz)
    (fun z hz => Hs_eq_zero hT0 hz)
  -- the Mellin identity
  set c₀ := (c1 y + c) / 2
  obtain ⟨hI, hid⟩ := h.identity_Gright (f := f9 y T) (continuous_f9 hT0) (x₀ := L - 1 / T)
    (by have : 0 < 1 / T := by positivity
        linarith)
    (fun x hx => f9_eq_zero hT0 hx) (c₀ := c₀) (c := c) (by simp only [c₀]; linarith)
    (by simp only [c₀]; linarith) (by linarith) (F := F9 y T)
    ((differentiableOn_F9 hy1).mono fun s hs => by
      rintro rfl
      have : c₀ < (1 : ℂ).re := hs
      simp only [Complex.one_re, c₀] at this; linarith)
    (fun s hs => (integral_f9_mul_cexp hT0 hy1 (by linarith)).symm)
    (fun σ hσ => integrable_f9_mul_exp hT0 (by linarith))
    (fun σ hσ t => norm_F9_le hT0 hy1 hc1'' hσ t)
  -- the identity in terms of the smoothed sums
  set Sm := (∑ jk ∈ P.pps y, Hs T (Real.log (y / P.p jk.1 ^ (jk.2 + 1))) /
      (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) -
    ∫ u in Ioi 1, Hs T (Real.log (y / u)) * (pi0Dens u / u) with hSmdef
  have hSm : (∑ jk ∈ P.pps y, f9 y T (Real.log (P.p jk.1 ^ (jk.2 + 1))) / ((jk.2 : ℝ) + 1) -
      ∫ u in Ioi (1 : ℝ), f9 y T (Real.log u) * pi0Dens u) = Sm := by
    congr 1
    · refine Finset.sum_congr rfl fun jk _ => ?_
      have hp := P.pp_pos jk
      rw [f9, Real.exp_neg, Real.exp_log hp, ← Real.log_div hy0.ne' hp.ne']
      field_simp
    · refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
      rw [f9, Real.exp_neg, Real.exp_log hu0, ← Real.log_div hy0.ne' hu0.ne']
      field_simp
  rw [hSm] at hid
  have hSmle : |Sm| ≤
      (1 / (2 * π)) * ‖∫ t : ℝ, F9 y T (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hid, norm_mul]
    apply le_of_eq; congr 1
    rw [norm_div, norm_mul]; simp [abs_of_pos Real.pi_pos]
  -- the contour shift
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  set a := 0.9 * etat Λ T₁ / 3.79 with hadef
  have ha0 : 0 < a := by have := etat_pos hΛ1 T₁; positivity
  have ha1 : a ≤ 1 / 10 ^ 10 := by
    have := etat_le hX T₁
    rw [hadef, div_le_iff₀ (by norm_num)]; nlinarith
  have hc0U : c0 Λ T₁ < 1 - a := by
    have hηT1 := etat_ge_near (Λ := Λ) (t := T₁) (t' := T₁ + 1) hΛ1
      (by rw [abs_of_pos hT10, abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_pos hT10, abs_of_pos (by linarith)])
    simp only [c0, hadef]
    have : 0.9 * etat Λ T₁ / 3.79 < 0.99 * etat Λ (T₁ + 1) / 3.79 := by
      apply div_lt_div_of_pos_right _ (by norm_num)
      have := etat_pos hΛ1 T₁; nlinarith
    linarith
  have hRU : [[1 - a, c]] ×ℂ [[-T₁, T₁]] ⊆ rectU Λ T₁ := by
    rintro z ⟨h1, h2⟩
    rw [Set.uIcc_of_le (by linarith)] at h1
    rw [Set.uIcc_of_le (by linarith)] at h2
    exact ⟨⟨lt_of_lt_of_le hc0U h1.1, by linarith [h1.2]⟩,
      ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  have hUo : IsOpen (rectU Λ T₁) := isOpen_Ioo.reProdIm isOpen_Ioo
  have h1U : (1 : ℂ) ∈ rectU Λ T₁ := by
    refine ⟨⟨?_, by norm_num⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
    simp only [Complex.one_re]; linarith
  have hdsl : DifferentiableOn ℂ (dslope G 1) (rectU Λ T₁) :=
    (differentiableOn_dslope (hUo.mem_nhds h1U)).2 hGd
  have hy0' : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  set Q : ℂ → ℂ := fun s => (y : ℂ) ^ (s - 1) * hhat0 ((s - 1) / T) * dslope G 1 s
  have hQd : DifferentiableOn ℂ Q ([[1 - a, c]] ×ℂ [[-T₁, T₁]]) := by
    refine DifferentiableOn.mul ?_ (hdsl.mono hRU)
    exact (((differentiable_id.sub_const 1).const_cpow (Or.inl hy0')).mul
      (differentiable_hhat0.comp ((differentiable_id.sub_const 1).div_const _))).differentiableOn
  have hQ : ∀ s ∈ rectU Λ T₁, s ≠ 1 → Q s = F9 y T s * G s := by
    intro s _ hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
    simp only [Q, F9]
    rw [dslope_of_ne _ hs, slope_def_field, hG1, sub_zero]
    field_simp
  set Gb := GLam Λ (2 * s0)
  have hGb : 190 * Yt Λ T₁ ≤ Gb := Num10.Yt_le_GLam hΛ1 (by linarith)
  have hGb0 : 0 < Gb := by
    simp only [Gb, GLam]; have := Real.log_nonneg hΛ1; positivity
  -- (A)
  set Ca := y ^ (-a) * (76 ^ 19 * Real.exp (2 * a / T)) with hCadef
  have hCa0 : 0 < Ca := by positivity
  set gA : ℝ → ℝ := fun t => Ca / 2 * (4 * (2 / a) / (2 + 2 / a * |t|))
  have hD2 : 0 < 2 / a := by positivity
  have hgAc : Continuous gA :=
    continuous_const.mul (continuous_const.div (continuous_const.add
      (continuous_const.mul continuous_abs)) (fun t => by positivity))
  have hA : ∀ t : ℝ, |t| ≤ T₁ →
      ‖F9 y T (((1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 : ℝ) : ℂ) + t * I)‖ ≤ gA t := by
    intro t _
    set s : ℂ := ((1 - a : ℝ) : ℂ) + t * I
    have hre : s.re = 1 - a := by simp [s]
    have hs1 : s - 1 = ((-a : ℝ) : ℂ) + t * I := by simp only [s]; push_cast; ring
    have hns : s ≠ 1 := by intro e; rw [e] at hre; simp at hre; linarith
    have hr0 : a ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [hs1] at this ⊢; simpa [abs_of_pos ha0] using this
    have hrt : |t| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [hs1] at this ⊢; simpa using this
    have hr : 0 < ‖s - 1‖ := lt_of_lt_of_le ha0 hr0
    have hF := (norm_F9_le_gen hT0 hy1 hns).1
    rw [hre, show 1 - a - 1 = -a by ring, abs_neg, abs_of_pos ha0] at hF
    have hm := min_le_four_div (m := 2 * (‖F9 y T s‖ / Ca)) (t := t) hD2
      (by
        have hF' : ‖F9 y T s‖ * ‖s - 1‖ ≤ Ca := (le_div_iff₀ hr).1 hF
        rw [mul_div_assoc', div_le_div_iff₀ hCa0 ha0]
        nlinarith [norm_nonneg (F9 y T s)])
      (fun ht0 => by
        have ht : 0 < |t| := abs_pos.2 ht0
        have hF' : ‖F9 y T s‖ * ‖s - 1‖ ≤ Ca := (le_div_iff₀ hr).1 hF
        rw [mul_div_assoc', div_le_div_iff₀ hCa0 ht]
        nlinarith [norm_nonneg (F9 y T s)])
    show ‖F9 y T s‖ ≤ gA t
    simp only [gA]
    rw [mul_div_assoc', div_le_iff₀ hCa0] at hm
    nlinarith
  have hIA : ∫ t in (-T₁)..T₁, gA t ≤ Ca * (4 * Real.log (1 + T₁ / a)) := by
    simp only [gA]
    rw [intervalIntegral.integral_const_mul, integral_four_div_le hD2 hT10.le]
    apply le_of_eq; field_simp; ring_nf
  -- (B) and (C)
  have hL1 : 1 ≤ L := by linarith
  have hyc : y ^ (c - 1) = L ^ 17 := by
    rw [Real.rpow_def_of_pos hy0, ← hLdef, show c - 1 = 17 * Real.log L / L by ring,
      show L * (17 * Real.log L / L) = 17 * Real.log L by field_simp, ← Real.log_rpow
        (by linarith), Real.exp_log (by positivity)]
    norm_cast
  have hexp3 : ∀ σ : ℝ, |σ - 1| ≤ 1 / 8 → 76 ^ 19 * Real.exp (2 * |σ - 1| / T) ≤ 76 ^ 19 * 3 := by
    intro σ hσ
    have : 2 * |σ - 1| / T ≤ 1 := by rw [div_le_one hT0]; linarith
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have := (Real.exp_le_exp.2 this).trans h3
    gcongr
  have hTT : T ^ 19 / T₁ ^ 20 = Real.exp (-(19 * s0)) / T₁ := by
    simp only [T, T₁]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sub]
    congr 1; push_cast; ring
  set IB := L ^ 17 * 76 ^ 19 * 3 * Real.exp (-(19 * s0)) / T₁
  have hB : ∀ σ : ℝ, 1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 ≤ σ → σ ≤ c → ∀ t : ℝ, |t| = T₁ →
      ‖F9 y T (σ + t * I)‖ ≤ IB := by
    intro σ hσ1 hσ2 t ht
    set s : ℂ := (σ : ℂ) + t * I
    have hre : s.re = σ := by simp [s]
    have hs1 : s - 1 = ((σ - 1 : ℝ) : ℂ) + t * I := by simp only [s]; push_cast; ring
    have hns : s ≠ 1 := by
      intro e; have := congrArg Complex.im e; simp [s] at this; rw [this] at ht; simp at ht
      linarith
    have hrt : T₁ ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [hs1] at this ⊢; simpa [ht] using this
    have hF := (norm_F9_le_gen hT0 hy1 hns).2
    rw [hre] at hF
    have hσa : |σ - 1| ≤ 1 / 8 := by
      rw [abs_le]; constructor <;> [skip; linarith]
      have : 1 - a ≤ σ := hσ1; linarith
    have h1 : y ^ (σ - 1) ≤ L ^ 17 := hyc ▸ Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith)
    have h2 := hexp3 σ hσa
    have h3 : T ^ 19 / ‖s - 1‖ ^ 20 ≤ T ^ 19 / T₁ ^ 20 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hT10.le hrt 20)
    calc ‖F9 y T s‖ ≤ y ^ (σ - 1) * (76 ^ 19 * Real.exp (2 * |σ - 1| / T)) * T ^ 19 /
          ‖s - 1‖ ^ 20 := hF
      _ = y ^ (σ - 1) * (76 ^ 19 * Real.exp (2 * |σ - 1| / T)) * (T ^ 19 / ‖s - 1‖ ^ 20) := by
          ring
      _ ≤ L ^ 17 * (76 ^ 19 * 3) * (T ^ 19 / T₁ ^ 20) := by gcongr
      _ = IB := by rw [hTT]; simp only [IB]; ring
  set gC : ℝ → ℝ := fun r => L ^ 17 * 76 ^ 19 * 3 / 2 * (2 / |r| * (19 / (|r| * (19 / T))) ^ 19)
  have hω : 0 < 19 / T := by positivity
  obtain ⟨hTi, hTv⟩ := integral_tail_le (k := 19) hT10 hω (by norm_num)
  have hgCe : EqOn gC (fun r => L ^ 17 * 76 ^ 19 * 3 / 2 *
      (2 / r * ((19 : ℕ) / (r * (19 / T))) ^ 19)) (Ioi T₁) := by
    intro r hr
    simp only [gC, abs_of_pos (lt_trans hT10 hr)]; push_cast; ring
  have hTi' : IntegrableOn (fun r => L ^ 17 * 76 ^ 19 * 3 / 2 *
      (2 / r * ((19 : ℕ) / (r * (19 / T))) ^ 19)) (Ioi T₁) := hTi.const_mul _
  have hgC : IntegrableOn gC (Ioi T₁) := hTi'.congr_fun hgCe.symm measurableSet_Ioi
  have hgC0 : ∀ t, 0 ≤ gC t := fun t => by simp only [gC]; positivity
  set IC := L ^ 17 * 76 ^ 19 * 3 / 19 * Real.exp (-(19 * s0))
  have hIC : ∫ t in Ioi T₁, gC t ≤ IC := by
    rw [setIntegral_congr_fun measurableSet_Ioi hgCe, integral_const_mul, hTv]
    apply le_of_eq
    have : (19 : ℕ) / (T₁ * (19 / T)) = Real.exp (-s0) := by
      simp only [T, T₁]; push_cast
      rw [show (19 : ℝ) / (Real.exp (2 * s0) * (19 / Real.exp s0)) =
        Real.exp s0 / Real.exp (2 * s0) by field_simp, ← Real.exp_sub]
      ring_nf
    rw [this, ← Real.exp_nat_mul]; simp only [IC]; push_cast; ring_nf
  have hC : ∀ t : ℝ, T₁ ≤ |t| → ‖F9 y T (c + t * I)‖ ≤ gC |t| := by
    intro t ht
    set s : ℂ := (c : ℂ) + t * I
    have hre : s.re = c := by simp [s]
    have hs1 : s - 1 = ((c - 1 : ℝ) : ℂ) + t * I := by simp only [s]; push_cast; ring
    have hns : s ≠ 1 := by intro e; rw [e] at hre; simp at hre; linarith
    have hrt : |t| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [hs1] at this ⊢; simpa using this
    have hF := (norm_F9_le_gen hT0 hy1 hns).2
    rw [hre, hyc] at hF
    have h2 := hexp3 c (by rw [abs_of_pos (by linarith)]; linarith)
    have hta : 0 < |t| := by linarith
    have h3 : T ^ 19 / ‖s - 1‖ ^ 20 ≤ T ^ 19 / |t| ^ 20 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hta.le hrt 20)
    calc ‖F9 y T s‖ ≤ L ^ 17 * (76 ^ 19 * Real.exp (2 * |c - 1| / T)) * T ^ 19 /
          ‖s - 1‖ ^ 20 := hF
      _ = L ^ 17 * (76 ^ 19 * Real.exp (2 * |c - 1| / T)) * (T ^ 19 / ‖s - 1‖ ^ 20) := by ring
      _ ≤ L ^ 17 * (76 ^ 19 * 3) * (T ^ 19 / |t| ^ 20) := by gcongr
      _ = gC |t| := by simp only [gC, abs_abs]; field_simp
  have hCE := h.contour_estimate_gen hT1 N1 N2 hGd hGe hGr hc1 hc98 hQd hQ hGb hI
    (hgAc.intervalIntegrable _ _) hA hIA hB hgC hgC0 hC hIC
  -- the numerics
  have ha : 0.9 * (cZF Λ / (2 * s0 + 442 + 2 * Real.log Λ + Real.log (2 * s0))) ≤ a := by
    have := Num10.cZF_div_le_etat hX (L := 2 * s0) (by linarith)
    rw [hadef, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have hθ' := (thetaPrime_bounds h.theta_mem hX).2
  have hN := N3 a (thetaPrime θ X₀) ha hθ'
  have hCa : Ca ≤ Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 := by
    have e1 : y ^ (-a) = Real.exp (-(a * L)) := by
      rw [Real.rpow_def_of_pos hy0, ← hLdef]; ring_nf
    have hx0 : 0 < 2 * a / T := by positivity
    have hx1 : 2 * a / T ≤ 1 / 10 ^ 10 := by
      rw [div_le_iff₀ hT0]; nlinarith
    have e2 : Real.exp (2 * a / T) ≤ 1.0001 := by
      have := Real.exp_bound_div_one_sub_of_interval' hx0 (by linarith)
      refine this.le.trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    rw [hCadef, e1]
    have := Real.exp_pos (-(a * L))
    nlinarith
  have hlog0 : 0 ≤ Real.log (1 + T₁ / a) := Real.log_nonneg (by
    have : 0 ≤ T₁ / a := by positivity
    linarith)
  have hIB0 : 0 ≤ IB := by positivity
  have hIC0 : 0 ≤ IC := by positivity
  have hcc : c - (1 - a) ≤ 1 := by linarith
  have hlc : Real.log (1 / (c - 1)) ≤ Real.log L := by
    have := log_inv_c_sub_one_le (L := L) (by linarith)
    rwa [← hcdef] at this
  have key : ‖∫ t : ℝ, F9 y T (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)‖ ≤
      GLam Λ (2 * s0) * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 * (4 * Real.log (1 + T₁ / a)))
        + 2 * GLam Λ (2 * s0) * IB + (1.5 * Real.log L + 8) * (2 * IC) := by
    refine hCE.trans ?_
    have hlc0 : 0 ≤ 1.5 * Real.log (1 / (c - 1)) + 8 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / (c - 1) by
        rw [le_div_iff₀ (by linarith)]; linarith)
      linarith
    have t1 : Gb * (Ca * (4 * Real.log (1 + T₁ / a))) ≤
        Gb * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 * (4 * Real.log (1 + T₁ / a))) := by
      gcongr
    have t2 : 2 * (c - (1 - a)) * Gb * IB ≤ 2 * Gb * IB := by
      have := mul_le_mul_of_nonneg_right hcc (mul_nonneg hGb0.le hIB0)
      nlinarith
    have t3 : (1.5 * Real.log (1 / (c - 1)) + 8) * (2 * IC) ≤
        (1.5 * Real.log L + 8) * (2 * IC) := by
      gcongr
    exact add_le_add (add_le_add t1 t2) t3
  have hyθ : y ^ (thetaPrime θ X₀ - 1) = Real.exp ((thetaPrime θ X₀ - 1) * L) := by
    rw [Real.rpow_def_of_pos hy0, ← hLdef, mul_comm]
  rw [hyθ] at hsm
  have hpi : 0 < 1 / (2 * π) := by positivity
  have := abs_sub_abs_le_abs_sub (piRecip P y - pi0Recip y) Sm
  have h2 := mul_le_mul_of_nonneg_left key hpi.le
  linarith

end LPHyp

end LocalPNT

end
