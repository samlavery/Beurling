module

public import RequestProject.Beurling.Noise.BSL57PD

/-!
# Lemma 5.7, remainder (b) (04c-saias.tex, lines 440-450): `remB : RemB`

`ρ₂ = ½ E_π[D'² e^{D'₊} 1[w ≤ Ū]]`. With `D'² ≤ 2X²` termwise, (P3) and the moments
`M₈(r) = ∑_k C(8,k) k!/r^{k+1}`, `M₆(r) = ∑_k C(6,k) k!/r^{k+1}` (`rho2_gen`), we get
the three bounds of (b). For `u ≥ u₀ - 2` the `a'`-part is reduced to the slack bound of
Lemma 5.7 (`ℓa'² ≤ 1.4926 α' ℓ(s_a)₊ + 0.806 α'√ℓ + 0.6497`), as in the paper.
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- `M₈(r) = ∑_k C(8,k) k!/r^{k+1}`. -/
noncomputable def M8 (r : ℝ) : ℝ :=
  1 / r + 8 / r ^ 2 + 2 * 28 / r ^ 3 + 6 * 56 / r ^ 4 + 24 * 70 / r ^ 5 + 120 * 56 / r ^ 6 +
    720 * 28 / r ^ 7 + 5040 * 8 / r ^ 8 + 40320 / r ^ 9

/-- `M₆(r) = ∑_k C(6,k) k!/r^{k+1}`. -/
noncomputable def M6 (r : ℝ) : ℝ :=
  1 / r + 6 / r ^ 2 + 2 * 15 / r ^ 3 + 6 * 20 / r ^ 4 + 24 * 15 / r ^ 5 + 120 * 6 / r ^ 6 +
    720 / r ^ 7

lemma M8_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ M8 r := by unfold M8; positivity
lemma M6_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ M6 r := by unfold M6; positivity

/-- **The general bound for `ρ₂`.** -/
lemma LargeRange.rho2_gen (hR : LargeRange τ ℓ u) {H X1 X2 rmin : ℝ} (hH : 0 ≤ H)
    (_hX1 : 0 ≤ X1) (_hX2 : 0 ≤ X2) (hrmin : 0 < rmin)
    (hr : rmin ≤ Dickman.ratio (u - 1) - 0.0012)
    (hhead : ∀ w, u - 1 < w → w ≤ u → Dp ℓ u w ^ 2 ≤ H)
    (htail : ∀ w, u < w → w ≤ Uf τ ℓ →
      0 ≤ Dp ℓ u w ∧ Dp ℓ u w ≤ X1 * (1 + (w - u)) ^ 4 + X2 * (1 + (w - u)) ^ 3) :
    rho2 τ ℓ u ≤ 1.0004 / 2 * (H + 2 * (X1 ^ 2 * M8 rmin + X2 ^ 2 * M6 rmin) / u) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  set K : ℝ := 2 * 1.0004
  have hK : 0 ≤ K := by norm_num
  have hm := master9 (u := u) (γ := 0.0012) (A := 1.0004 * H) (rmin := rmin) hu hrmin hr
    (by positivity) (a0 := K * (X1 ^ 2 + X2 ^ 2)) (a1 := K * (8 * X1 ^ 2 + 6 * X2 ^ 2))
    (a2 := K * (28 * X1 ^ 2 + 15 * X2 ^ 2)) (a3 := K * (56 * X1 ^ 2 + 20 * X2 ^ 2))
    (a4 := K * (70 * X1 ^ 2 + 15 * X2 ^ 2)) (a5 := K * (56 * X1 ^ 2 + 6 * X2 ^ 2))
    (a6 := K * (28 * X1 ^ 2 + X2 ^ 2)) (a7 := K * (8 * X1 ^ 2)) (a8 := K * X1 ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (S := Ioc (u - 1) (Uf τ ℓ)) Ioc_subset_Ioi_self measurableSet_Ioc
    (f := fun w => Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0))
    (by
      apply integrableOn_Ioc_of_continuousAt (by linarith)
      intro w hw
      have hD := continuousAt_Dp (u := u) hℓ0 hw
      exact (((hD.pow 2).mul (hD.max continuousAt_const).rexp).mul
        ((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt)).div
        continuousAt_id hw.ne')
    (fun w _ => by positivity)
    (by
      intro w hw hwu
      beta_reduce
      have he := hR.exp_Dp_le hw.1.le hw.2
      rw [max_eq_right (by linarith : w - u ≤ 0), mul_zero, Real.exp_zero, mul_one] at he
      have h1 := hhead w hw.1 hwu
      calc Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0) ≤ H * 1.0004 :=
            mul_le_mul h1 he (Real.exp_pos _).le hH
        _ = 1.0004 * H := by ring)
    (by
      intro w hw huw
      beta_reduce
      have he := hR.exp_Dp_le hw.1.le hw.2
      rw [max_eq_left (by linarith : 0 ≤ w - u)] at he
      obtain ⟨h0, h1⟩ := htail w huw hw.2
      have hs : 0 ≤ w - u := by linarith
      have hsq : Dp ℓ u w ^ 2 ≤ 2 * (X1 ^ 2 * (1 + (w - u)) ^ 8 + X2 ^ 2 * (1 + (w - u)) ^ 6) := by
        have h2 := pow_le_pow_left₀ h0 h1 2
        have h3 : (X1 * (1 + (w - u)) ^ 4 + X2 * (1 + (w - u)) ^ 3) ^ 2 ≤
            2 * (X1 ^ 2 * (1 + (w - u)) ^ 8 + X2 ^ 2 * (1 + (w - u)) ^ 6) := by
          nlinarith [sq_nonneg (X1 * (1 + (w - u)) ^ 4 - X2 * (1 + (w - u)) ^ 3)]
        linarith
      calc Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0)
          ≤ 2 * (X1 ^ 2 * (1 + (w - u)) ^ 8 + X2 ^ 2 * (1 + (w - u)) ^ 6) *
              (1.0004 * Real.exp (0.0012 * (w - u))) :=
            mul_le_mul hsq he (Real.exp_pos _).le (by positivity)
        _ = _ := by simp only [K]; ring)
  unfold rho2
  have e : 1.0004 * H + (K * (X1 ^ 2 + X2 ^ 2) / rmin + K * (8 * X1 ^ 2 + 6 * X2 ^ 2) / rmin ^ 2 +
      2 * (K * (28 * X1 ^ 2 + 15 * X2 ^ 2)) / rmin ^ 3 +
      6 * (K * (56 * X1 ^ 2 + 20 * X2 ^ 2)) / rmin ^ 4 +
      24 * (K * (70 * X1 ^ 2 + 15 * X2 ^ 2)) / rmin ^ 5 +
      120 * (K * (56 * X1 ^ 2 + 6 * X2 ^ 2)) / rmin ^ 6 +
      720 * (K * (28 * X1 ^ 2 + X2 ^ 2)) / rmin ^ 7 + 5040 * (K * (8 * X1 ^ 2)) / rmin ^ 8 +
      40320 * (K * X1 ^ 2) / rmin ^ 9) / u =
      2 * (1.0004 / 2 * (H + 2 * (X1 ^ 2 * M8 rmin + X2 ^ 2 * M6 rmin) / u)) := by
    simp only [K]; unfold M8 M6; field_simp; ring
  rw [e] at hm
  linarith

/-! ## Numerical values of the moments -/

lemma M8_4588 : M8 4.5888 ≤ 4.21 := by unfold M8; norm_num
lemma M6_4588 : M6 4.5888 ≤ 1.36 := by unfold M6; norm_num
lemma M8_2188 : M8 2.1888 ≤ 312 := by unfold M8; norm_num
lemma M8_09988 : M8 0.9988 ≤ 110800 := by unfold M8; norm_num

/-! ## Auxiliary bounds -/

lemma LargeRange.absDA_head (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    |11 / ℓ * hA u w| ≤ 4 * (11 * Lam u / ℓ) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have h1 := hA_head_upper hu hw1 hwu
  have h2 := hA_head_lower hu hw1 hwu
  have h15 : (1 + u) / u ≤ 1.5 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : |hA u w| ≤ 4 * Lam u := by
    rw [abs_le]; constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_right h15 hΛ0]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 11 / ℓ)]
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
  have e : 11 / ℓ * (4 * Lam u) = 4 * (11 * Lam u / ℓ) := by ring
  linarith

lemma LargeRange.DA_tail_le (hR : LargeRange τ ℓ u) {w : ℝ} (huw : u ≤ w) :
    0 ≤ 11 / ℓ * hA u w ∧ 11 / ℓ * hA u w ≤ 8 * (11 * Lam u / ℓ) * (1 + (w - u)) ^ 4 := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  obtain ⟨h0, h1⟩ := hA_tail hu huw
  have hs : 0 ≤ w - u := by linarith
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have h15 : (1 + u) / u ≤ 1.5 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : (1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3 ≤ 8 * (1 + (w - u)) ^ 4 := by
    have : 1 ≤ (1 + (w - u)) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨mul_nonneg (by positivity) h0, ?_⟩
  have h3 : hA u w ≤ Lam u * (8 * (1 + (w - u)) ^ 4) := h1.trans
    (mul_le_mul_of_nonneg_left h2 hΛ0)
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
  have e : 11 / ℓ * (Lam u * (8 * (1 + (w - u)) ^ 4)) =
      8 * (11 * Lam u / ℓ) * (1 + (w - u)) ^ 4 := by ring
  linarith

lemma LargeRange.ell_eq (hR : LargeRange τ ℓ u) : ℓ = u0 ℓ ^ 4 := by
  have hsq : u0 ℓ ^ 2 = √ℓ := u0_sq hR.ℓ_pos.le
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, Real.sq_sqrt hR.ℓ_pos.le]

lemma LargeRange.lam_ge (hR : LargeRange τ ℓ u) : 90 ≤ lamL τ ℓ * u0 ℓ ^ 2 := by
  have hU := hR.U_ge
  have hu0 := hR.u0_ge
  have hℓ := hR.ell_eq
  have hlog : 10 ≤ Real.log (2 + Uf τ ℓ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [exp_ten_le]
  unfold lamL
  have hℓ0 := hR.ℓ_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hℓ0]
  have h9 : 9 * u0 ℓ ^ 2 ≤ Uf τ ℓ ^ 2 := by nlinarith
  have e : 90 * ℓ = 90 * u0 ℓ ^ 4 := congrArg (90 * ·) hℓ
  rw [e]
  nlinarith [mul_le_mul h9 hlog (by norm_num) (sq_nonneg (Uf τ ℓ)), sq_nonneg (u0 ℓ)]

/-- `ℓa'² ≤ 1.4926 α' ℓ(s_a)₊ + 0.806 α'√ℓ + 0.6497` for `u ≥ u₀ - 2` (from the slack). -/
lemma LargeRange.ap_sq_le (hR : LargeRange τ ℓ u) (hbig : u0 ℓ - 2 ≤ u) :
    ℓ * aprime ℓ u ^ 2 ≤ 1.4926 * alphaL τ ℓ * (ℓ * max (sA ℓ u) 0) +
      0.806 * alphaL τ ℓ * √ℓ + 0.6497 := by
  have hℓ0 := hR.ℓ_pos
  have hsq := hR.sqrt_pos
  have ha0 := hR.ap_nonneg
  have hap := hR.ap_le
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  obtain ⟨hs1, -⟩ := lemma57Slack τ ℓ u hR
  have hs := hs1 hbig
  have hℓq : ℓ * (1 / √ℓ) = √ℓ := by
    field_simp; rw [Real.sq_sqrt hℓ0.le]
  have hq2 : ℓ * (1 / √ℓ) ^ 2 = 1 := by
    field_simp; rw [Real.sq_sqrt hℓ0.le]
  have e054 : 0.54 / √ℓ = 0.54 * (1 / √ℓ) := by ring
  rw [e054] at hs
  set q := 1 / √ℓ
  have hq0 : 0 ≤ q := by positivity
  set a := aprime ℓ u
  rcases le_or_gt 0 (sA ℓ u) with hpos | hneg
  · rw [max_eq_left hpos]
    have ha : a ≤ (sA ℓ u + 0.54 * q) / 0.67 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have h1 : ℓ * a ^ 2 ≤ ℓ * a * ((sA ℓ u + 0.54 * q) / 0.67) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_left ha (mul_nonneg hℓ0.le ha0)
    have h2 : ℓ * a * ((sA ℓ u + 0.54 * q) / 0.67) =
        (a * (ℓ * sA ℓ u) + 0.54 * a * (ℓ * q)) / 0.67 := by ring
    rw [h2, hℓq] at h1
    have h3 : a * (ℓ * sA ℓ u) ≤ alphaL τ ℓ * (ℓ * sA ℓ u) :=
      mul_le_mul_of_nonneg_right hap (mul_nonneg hℓ0.le hpos)
    have h4 : 0.54 * a * √ℓ ≤ 0.54 * alphaL τ ℓ * √ℓ :=
      mul_le_mul_of_nonneg_right (by linarith) hsq.le
    have h5 : 0 ≤ alphaL τ ℓ * (ℓ * sA ℓ u) := mul_nonneg hα0 (mul_nonneg hℓ0.le hpos)
    have h6 : 0 ≤ alphaL τ ℓ * √ℓ := mul_nonneg hα0 hsq.le
    rw [le_div_iff₀ (by norm_num)] at h1
    nlinarith
  · rw [max_eq_right hneg.le, mul_zero, mul_zero, zero_add]
    have ha : a ≤ 0.54 / 0.67 * q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
    have h1 : a ^ 2 ≤ (0.54 / 0.67 * q) ^ 2 := pow_le_pow_left₀ ha0 ha 2
    have h2 : ℓ * a ^ 2 ≤ (0.54 / 0.67) ^ 2 * (ℓ * q ^ 2) := by
      have := mul_le_mul_of_nonneg_left h1 hℓ0.le
      nlinarith
    rw [hq2] at h2
    have := mul_nonneg hα0 hsq.le
    nlinarith

lemma Lam_le_u2log {u : ℝ} (h27 : 27 ≤ u) : Lam u ≤ 1.09 * (u ^ 2 * Real.log (1 + u)) := by
  unfold Lam
  have hl := log_ge_329 (x := 1 + u) (by linarith)
  have hd : Real.log (2 + u) - Real.log (1 + u) ≤ 1 / (1 + u) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < (2 + u) / (1 + u) by positivity)
    have e : (2 + u) / (1 + u) - 1 = 1 / (1 + u) := by field_simp; ring
    linarith
  have h1 : 1 / (1 + u) ≤ 1 / 28 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : Real.log (2 + u) ≤ 1.0109 * Real.log (1 + u) := by nlinarith
  have h3 : (1 + u) ^ 2 ≤ 1.0755 * u ^ 2 := by nlinarith
  have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  calc (1 + u) ^ 2 * Real.log (2 + u) ≤ (1.0755 * u ^ 2) * (1.0109 * Real.log (1 + u)) :=
        mul_le_mul h3 h2 hl0 (by positivity)
    _ ≤ 1.09 * (u ^ 2 * Real.log (1 + u)) := by nlinarith [sq_nonneg u]

lemma LargeRange.tL_le (hR : LargeRange τ ℓ u) :
    ℓ * (11 * Lam u / ℓ) ^ 2 ≤ 121.121 * lamL τ ℓ * Lam u := by
  have hℓ0 := hR.ℓ_pos
  have hΛ := hR.Lam_le
  have hΛ0 := Lam_nonneg (x := u) (by linarith [hR.2.2.2.1])
  have e : ℓ * (11 * Lam u / ℓ) ^ 2 = 121 * Lam u * (Lam u / ℓ) := by field_simp; ring
  rw [e]
  have h : Lam u / ℓ ≤ 1.001 * lamL τ ℓ := by rw [div_le_iff₀ hℓ0]; linarith
  nlinarith

lemma LargeRange.lamX_ge (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) :
    90 * (Kp * u ^ 2 * 3.29) ≤ lamL τ ℓ * Xu u * u0 ℓ ^ 2 := by
  have hl := hR.lam_ge
  have hlog := log_ge_329 (x := 1 + u) (by linarith)
  have hX : Kp * u ^ 2 * 3.29 ≤ Xu u := by
    unfold Xu Kp; exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hX0 : 0 ≤ Kp * u ^ 2 * 3.29 := by unfold Kp; positivity
  have := mul_le_mul hl hX hX0 (by positivity)
  nlinarith

set_option maxHeartbeats 800000 in
/-- **(b)**, `u ≥ 27`, `u ≥ u₀ - 2`. -/
lemma LargeRange.remB_big (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) (hbig : u0 ℓ - 2 ≤ u) :
    ℓ * rho2 τ ℓ u ≤ 4000 * lamL τ ℓ * Xu u + 4.7 * alphaL τ ℓ * (ℓ * max (sA ℓ u) 0) +
      2.54 * alphaL τ ℓ * √ℓ + 2.1 := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  set L := 11 * Lam u / ℓ with hLdef
  set a := aprime ℓ u
  set q := 1 / √ℓ with hqdef
  have hL0 : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have ha0 := hR.ap_nonneg
  have hq0 : 0 ≤ q := by have := hR.sqrt_pos; positivity
  have hr : 4.5888 ≤ Dickman.ratio (u - 1) - 0.0012 := by
    have := ratio_ge_459 (v := u - 1) (by linarith); linarith
  have h2 := hR.rho2_gen (H := 2 * (4 * L) ^ 2 + 2 * (1.2502 * a + 0.0314 * q) ^ 2)
    (X1 := 8 * L) (X2 := a + q) (rmin := 4.5888) (by positivity) (by positivity)
    (by positivity) (by norm_num) hr
    (by
      intro w hw1 hwu
      rw [Dp_eq_Da hℓ0 (by linarith)]
      have h1 := hR.absDA_head hw1.le hwu
      obtain ⟨h3, -⟩ := hR.Da_head hw1.le hwu
      have e : 0.0314 / √ℓ = 0.0314 * q := by simp only [q]; ring
      rw [e] at h3
      have hx := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      have hy := sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2
      nlinarith [sq_nonneg (11 / ℓ * hA u w - Da ℓ u w)])
    (by
      intro w huw hwU
      obtain ⟨hA0, hA1⟩ := hR.DA_tail_le huw.le
      obtain ⟨hd0, hd1⟩ := hR.Da_tail huw.le
      rw [Dp_eq_Da hℓ0 (by linarith)]
      have hs : 0 ≤ w - u := by linarith
      have hc3 : (w - u) + 0.2502 ≤ (1 + (w - u)) ^ 3 := by nlinarith [sq_nonneg (w - u)]
      have hc3' : (w - u) ^ 2 + 0.2502 * (w - u) + 0.0314 ≤ (1 + (w - u)) ^ 3 := by
        nlinarith [sq_nonneg (w - u), pow_nonneg hs 3]
      have e : ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ =
          q * ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) := by simp only [q]; ring
      rw [e] at hd1
      constructor
      · linarith
      · have := mul_le_mul_of_nonneg_left hc3 ha0
        have := mul_le_mul_of_nonneg_left hc3' hq0
        nlinarith)
  -- numeric
  have hM8 := M8_4588
  have hM6 := M6_4588
  have hM80 := M8_nonneg (r := 4.5888) (by norm_num)
  have hM60 := M6_nonneg (r := 4.5888) (by norm_num)
  have hu3 : 31620 ≤ u := by linarith
  have htL := hR.tL_le
  have htA := hR.ap_sq_le hbig
  have hq2 : ℓ * q ^ 2 = 1 := by simp only [q]; field_simp; rw [Real.sq_sqrt hℓ0.le]
  set tL := ℓ * L ^ 2
  set tA := ℓ * a ^ 2
  have htL0 : 0 ≤ tL := by positivity
  have htA0 : 0 ≤ tA := by positivity
  have hmain : ℓ * rho2 τ ℓ u ≤ 0.5002 * (32 * tL + 4 * 1.5631 * tA + 4 * 0.000986 +
      (128 * 4.21 * tL + 2 * 1.36 * (2 * tA + 2)) / u) := by
    have h3 := mul_le_mul_of_nonneg_left h2 hℓ0.le
    refine h3.trans ?_
    have hH : ℓ * (2 * (4 * L) ^ 2 + 2 * (1.2502 * a + 0.0314 * q) ^ 2) ≤
        32 * tL + 4 * 1.5631 * tA + 4 * 0.000986 := by
      have : (1.2502 * a + 0.0314 * q) ^ 2 ≤ 2 * (1.2502 * a) ^ 2 + 2 * (0.0314 * q) ^ 2 := by
        nlinarith [sq_nonneg (1.2502 * a - 0.0314 * q)]
      have := mul_le_mul_of_nonneg_left this hℓ0.le
      simp only [tL, tA]
      nlinarith
    have hT : ℓ * (2 * ((8 * L) ^ 2 * M8 4.5888 + (a + q) ^ 2 * M6 4.5888)) ≤
        128 * 4.21 * tL + 2 * 1.36 * (2 * tA + 2) := by
      have hsq : ℓ * (a + q) ^ 2 ≤ 2 * tA + 2 := by
        have : (a + q) ^ 2 ≤ 2 * a ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (a - q)]
        have := mul_le_mul_of_nonneg_left this hℓ0.le
        simp only [tA]; nlinarith
      have e : ℓ * (2 * ((8 * L) ^ 2 * M8 4.5888 + (a + q) ^ 2 * M6 4.5888)) =
          128 * M8 4.5888 * tL + 2 * M6 4.5888 * (ℓ * (a + q) ^ 2) := by simp only [tL]; ring
      rw [e]
      have : 0 ≤ ℓ * (a + q) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq hM60, mul_le_mul_of_nonneg_left hM6 this]
    have e : ℓ * (1.0004 / 2 * ((2 * (4 * L) ^ 2 + 2 * (1.2502 * a + 0.0314 * q) ^ 2) +
        2 * ((8 * L) ^ 2 * M8 4.5888 + (a + q) ^ 2 * M6 4.5888) / u)) =
        0.5002 * (ℓ * (2 * (4 * L) ^ 2 + 2 * (1.2502 * a + 0.0314 * q) ^ 2) +
          ℓ * (2 * ((8 * L) ^ 2 * M8 4.5888 + (a + q) ^ 2 * M6 4.5888)) / u) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add hH (div_le_div_of_nonneg_right hT hu0.le)
  -- the remaining arithmetic
  have hdiv : (128 * 4.21 * tL + 2 * 1.36 * (2 * tA + 2)) / u ≤
      (128 * 4.21 * tL + 2 * 1.36 * (2 * tA + 2)) / 31620 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hu3
  have hΛ := Lam_le_u2log h27
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hlog := log_ge_329 (x := 1 + u) (by linarith)
  have hX : Kp * (u ^ 2 * Real.log (1 + u)) = Xu u := by unfold Xu; ring
  have hKp : Kp = 2.2 := rfl
  have h4 : tL ≤ 121.121 * 1.09 * lamL τ ℓ * (u ^ 2 * Real.log (1 + u)) := by
    have := mul_le_mul_of_nonneg_left hΛ (by positivity : 0 ≤ 121.121 * lamL τ ℓ)
    nlinarith
  have hS0 : 0 ≤ alphaL τ ℓ * (ℓ * max (sA ℓ u) 0) :=
    mul_nonneg hα0 (mul_nonneg hℓ0.le (le_max_right _ _))
  have hS1 : 0 ≤ alphaL τ ℓ * √ℓ := mul_nonneg hα0 (Real.sqrt_nonneg _)
  have hlX : 0 ≤ lamL τ ℓ * (u ^ 2 * Real.log (1 + u)) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u); positivity
  rw [← hX, hKp]
  nlinarith

lemma LargeRange.ap_zero (_hR : LargeRange τ ℓ u) (hu2 : u < u0 ℓ - 2) : aprime ℓ u = 0 := by
  unfold aprime; rw [max_eq_right (by linarith)]; simp

lemma tQ_small_aux {dd u0 lX u : ℝ} (hu0 : 31622 ≤ u0) (hdd : u0 / 2.1 ≤ dd)
    (hlX : 90 * (2.2 * 27 ^ 2 * 3.29) ≤ lX * u0 ^ 2) (hu : 27 ≤ u) (hlX0 : 0 ≤ lX) :
    2 * 1.36 * (1 / dd ^ 2) ≤ 0.001 * lX * u := by
  have hdd0 : 0 < dd := lt_of_lt_of_le (by positivity) hdd
  have hdd3 : u0 ^ 2 / 4.41 ≤ dd ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hdd 2
    rw [div_pow] at this; norm_num at this ⊢; linarith
  have h6 : 1 / dd ^ 2 ≤ 4.41 / u0 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by norm_num)] at hdd3; linarith
  have hu0p : 0 < u0 ^ 2 := by positivity
  have h8 : 2 * 1.36 * (4.41 / u0 ^ 2) ≤ 0.001 * lX * u := by
    rw [mul_div_assoc', div_le_iff₀ hu0p]
    have : 0.001 * lX * u * u0 ^ 2 ≥ 0.001 * 27 * (lX * u0 ^ 2) := by
      have := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0:ℝ) ≤ 0.001)
        (mul_nonneg hlX0 hu0p.le))
      nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 2 * 1.36)
  linarith

lemma remB_mid_num {R tL tQ u lam lg X : ℝ}
    (hmain : R ≤ 0.5002 * (16 * tL + (128 * 4.21 * tL / u + 2 * 1.36 * tQ / u)))
    (hQ : 2 * 1.36 * tQ / u ≤ 0.001 * (lam * X))
    (h4 : tL ≤ 121.121 * 1.09 * lam * (u ^ 2 * lg)) (htL0 : 0 ≤ tL) (_htQ0 : 0 ≤ tQ)
    (h27 : 27 ≤ u) (hX : Kp * (u ^ 2 * lg) = X) (_hlam : 0 ≤ lam) :
    R ≤ 4000 * lam * X + lam * X := by
  have hKp : Kp = 2.2 := rfl
  rw [hKp] at hX
  have hu0 : 0 < u := by linarith
  have hdiv : 128 * 4.21 * tL / u ≤ 128 * 4.21 * tL / 27 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) h27
  have hlX : 0 ≤ lam * (u ^ 2 * lg) := by
    by_contra h; push_neg at h
    have : tL < 0 := by nlinarith
    linarith
  have hX' : lam * X = 2.2 * (lam * (u ^ 2 * lg)) := by rw [← hX]; ring
  have hlX2 : 0 ≤ lam * X := by rw [hX']; positivity
  nlinarith

set_option maxHeartbeats 800000 in
/-- **(b)**, `27 ≤ u < u₀ - 2`. -/
lemma LargeRange.remB_mid (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) (hsm : u < u0 ℓ - 2) :
    ℓ * rho2 τ ℓ u ≤ 4000 * lamL τ ℓ * Xu u + lamL τ ℓ * Xu u := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  set L := 11 * Lam u / ℓ with hLdef
  set q := 1 / √ℓ with hqdef
  have hL0 : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hq0 : 0 ≤ q := by have := hR.sqrt_pos; positivity
  have hr : 4.5888 ≤ Dickman.ratio (u - 1) - 0.0012 := by
    have := ratio_ge_459 (v := u - 1) (by linarith); linarith
  have hap := hR.ap_zero hsm
  -- the cofactor of the shift: `D_a ≤ X₂ (1+s)³`
  set dd := u0 ℓ - 0.26 - u
  have hdd : 1.74 ≤ dd := by simp only [dd]; linarith
  set X2 := if u0 ℓ / 2 ≤ u then q else q / dd with hX2def
  have hX20 : 0 ≤ X2 := by simp only [X2]; split_ifs <;> positivity
  have hDa : ∀ w, u < w → w ≤ Uf τ ℓ → Da ℓ u w ≤ X2 * (1 + (w - u)) ^ 3 := by
    intro w huw hwU
    obtain ⟨hd0, hd1⟩ := hR.Da_tail huw.le
    rw [hap, zero_mul, zero_add] at hd1
    have hs : 0 ≤ w - u := by linarith
    have e : ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ =
        q * ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) := by simp only [q]; ring
    rw [e] at hd1
    have hc2 : (w - u) ^ 2 + 0.2502 * (w - u) + 0.0314 ≤ (1 + (w - u)) ^ 2 := by nlinarith
    have hp2 : 0 ≤ (1 + (w - u)) ^ 2 := sq_nonneg _
    have hd2 : Da ℓ u w ≤ q * (1 + (w - u)) ^ 2 :=
      hd1.trans (mul_le_mul_of_nonneg_left hc2 hq0)
    simp only [X2]
    split_ifs with hc
    · have : (1 + (w - u)) ^ 2 ≤ (1 + (w - u)) ^ 3 := by
        have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + (w - u)) hp2
        nlinarith
      nlinarith
    · rcases le_or_gt w (u0 ℓ - 0.26) with hw | hw
      · rw [hR.Da_zero_low hsm (by linarith) hw]; positivity
      · have hsd : dd ≤ w - u := by simp only [dd]; linarith
        have hdd0 : 0 < dd := by linarith
        have h4 : (1 + (w - u)) ^ 2 ≤ (1 + (w - u)) ^ 3 / dd := by
          rw [le_div_iff₀ hdd0]
          have : (1 + (w - u)) ^ 2 * dd ≤ (1 + (w - u)) ^ 2 * (1 + (w - u)) :=
            mul_le_mul_of_nonneg_left (by linarith) hp2
          nlinarith
        have h3 : q * (1 + (w - u)) ^ 2 ≤ q / dd * (1 + (w - u)) ^ 3 := by
          calc q * (1 + (w - u)) ^ 2 ≤ q * ((1 + (w - u)) ^ 3 / dd) :=
                mul_le_mul_of_nonneg_left h4 hq0
            _ = q / dd * (1 + (w - u)) ^ 3 := by ring
        linarith
  have h2 := hR.rho2_gen (H := (4 * L) ^ 2) (X1 := 8 * L) (X2 := X2) (rmin := 4.5888)
    (by positivity) (by positivity) hX20 (by norm_num) hr
    (by
      intro w hw1 hwu
      rw [Dp_eq_Da hℓ0 (by linarith), hR.Da_zero_low hsm (by linarith) (by linarith), add_zero]
      have h1 := hR.absDA_head hw1.le hwu
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2)
    (by
      intro w huw hwU
      obtain ⟨hA0, hA1⟩ := hR.DA_tail_le huw.le
      obtain ⟨hd0, -⟩ := hR.Da_tail huw.le
      have hd1 := hDa w huw hwU
      rw [Dp_eq_Da hℓ0 (by linarith)]
      constructor <;> linarith)
  -- numeric
  have hM8 := M8_4588
  have hM6 := M6_4588
  have hM80 := M8_nonneg (r := 4.5888) (by norm_num)
  have hM60 := M6_nonneg (r := 4.5888) (by norm_num)
  have htL := hR.tL_le
  set tL := ℓ * L ^ 2
  have htL0 : 0 ≤ tL := by positivity
  set tQ := ℓ * X2 ^ 2
  have htQ0 : 0 ≤ tQ := by positivity
  have hmain : ℓ * rho2 τ ℓ u ≤ 0.5002 * (16 * tL + (128 * 4.21 * tL + 2 * 1.36 * tQ) / u) := by
    have h3 := mul_le_mul_of_nonneg_left h2 hℓ0.le
    refine h3.trans ?_
    have e1 : ℓ * (1.0004 / 2 * ((4 * L) ^ 2 + 2 * ((8 * L) ^ 2 * M8 4.5888 +
        X2 ^ 2 * M6 4.5888) / u)) = 0.5002 * (16 * tL + ℓ * (2 * ((8 * L) ^ 2 * M8 4.5888 +
        X2 ^ 2 * M6 4.5888)) / u) := by simp only [tL]; ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hu0.le
    have e : ℓ * (2 * ((8 * L) ^ 2 * M8 4.5888 + X2 ^ 2 * M6 4.5888)) =
        128 * M8 4.5888 * tL + 2 * M6 4.5888 * tQ := by simp only [tL, tQ]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hM8 htL0, mul_le_mul_of_nonneg_right hM6 htQ0]
  -- `tQ / u ≤ 0.0001 · λX`
  have hlX := hR.lamX_ge h27
  have hKp : Kp = 2.2 := rfl
  have hu2 : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
  have hq2 : ℓ * q ^ 2 = 1 := by simp only [q]; field_simp; rw [Real.sq_sqrt hℓ0.le]
  have hX0 : 0 ≤ Xu u := by
    unfold Xu Kp; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u); positivity
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hQ : 2 * 1.36 * tQ / u ≤ 0.001 * (lamL τ ℓ * Xu u) := by
    simp only [tQ, X2]
    split_ifs with hc
    · rw [hq2]
      rw [div_le_iff₀ hu0]
      -- `λX ≥ 90·2.2·3.29 u²/u₀² ≥ 162 · (u/u₀)² · ... ≥ 40` for `u ≥ u₀/2`
      have hu2' : u0 ℓ ^ 2 ≤ 4 * u ^ 2 := by nlinarith
      have h4 : 90 * (Kp * u ^ 2 * 3.29) ≤ lamL τ ℓ * Xu u * (4 * u ^ 2) :=
        hlX.trans (mul_le_mul_of_nonneg_left hu2' (mul_nonneg hlam0 hX0))
      rw [hKp] at h4
      have hu4 : 0 < u ^ 2 := by positivity
      have h5 : 162.8 ≤ lamL τ ℓ * Xu u := by nlinarith
      nlinarith
    · have hdd0 : 0 < dd := by linarith
      have e : ℓ * (q / dd) ^ 2 = 1 / dd ^ 2 := by
        rw [div_pow, ← mul_div_assoc, hq2]
      rw [e, div_le_iff₀ hu0]
      have hdd2 : u0 ℓ / 2.1 ≤ dd := by
        rw [div_le_iff₀ (by norm_num)]; simp only [dd]; push_neg at hc; linarith
      have h7 : 90 * (2.2 * 27 ^ 2 * 3.29) ≤ lamL τ ℓ * Xu u * u0 ℓ ^ 2 := by
        have : 2.2 * 27 ^ 2 * 3.29 ≤ Kp * u ^ 2 * 3.29 := by
          rw [hKp]; nlinarith
        linarith
      exact tQ_small_aux huu0 hdd2 h7 h27 (mul_nonneg hlam0 hX0)
  -- the `λ X` part
  have hΛ := Lam_le_u2log h27
  have h4 : tL ≤ 121.121 * 1.09 * lamL τ ℓ * (u ^ 2 * Real.log (1 + u)) := by
    have := mul_le_mul_of_nonneg_left hΛ (by positivity : 0 ≤ 121.121 * lamL τ ℓ)
    nlinarith
  have hX : Kp * (u ^ 2 * Real.log (1 + u)) = Xu u := by unfold Xu; ring
  rw [add_div] at hmain
  exact remB_mid_num hmain hQ h4 htL0 htQ0 h27 hX hlam0

lemma Lam_10_le : Lam 10 ≤ 121 * 2.7726 := by
  unfold Lam
  have h : Real.log (2 + 10) ≤ 4 * Real.log 2 := by
    have e : (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) := by rw [Real.log_pow]; norm_num
    rw [e]; exact Real.log_le_log (by norm_num) (by norm_num)
  have := Real.log_two_lt_d9
  norm_num at h ⊢
  nlinarith

/-- The numerical part of (b) for `u < 27`. -/
lemma remB_small_num {ℓ Λ M u : ℝ} (hℓ : 0 < ℓ) (_hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M) (hu : 0 < u)
    (hb : 121 * Λ ^ 2 * (16 + 256 * M / u) + 4.025 * M / u ≤ 4.59e15) :
    ℓ * (1.0004 / 2 * ((4 * (11 * Λ / ℓ)) ^ 2 + 2 * ((8 * (11 * Λ / ℓ) + 1.003 / ℓ) ^ 2 * M +
      0 ^ 2 * M6 0.9988) / u)) ≤ 2300000000000000 / ℓ := by
  have e : ℓ * (1.0004 / 2 * ((4 * (11 * Λ / ℓ)) ^ 2 + 2 * ((8 * (11 * Λ / ℓ) + 1.003 / ℓ) ^ 2 * M +
      0 ^ 2 * M6 0.9988) / u)) = 0.5002 * (1936 * Λ ^ 2 + 2 * (88 * Λ + 1.003) ^ 2 * M / u) / ℓ
      := by field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hℓ.le
  have h1 : (88 * Λ + 1.003) ^ 2 ≤ 2 * (7744 * Λ ^ 2) + 2 * 1.006009 := by
    nlinarith [sq_nonneg (88 * Λ - 1.003)]
  have h2 : 2 * (88 * Λ + 1.003) ^ 2 * M / u ≤ (30976 * Λ ^ 2 + 4.024036) * M / u := by
    apply div_le_div_of_nonneg_right _ hu.le
    nlinarith
  have h3 : (30976 * Λ ^ 2 + 4.024036) * M / u = 121 * Λ ^ 2 * (256 * M / u) +
      4.024036 * M / u := by ring
  have h4 : 4.024036 * M / u ≤ 4.025 * M / u :=
    div_le_div_of_nonneg_right (by nlinarith) hu.le
  have h6 : 121 * Λ ^ 2 * (16 + 256 * M / u) = 1936 * Λ ^ 2 + 121 * Λ ^ 2 * (256 * M / u) := by
    ring
  linarith

set_option maxHeartbeats 800000 in
/-- **(b)**, `u < 27`. -/
lemma LargeRange.remB_small (hR : LargeRange τ ℓ u) (h27 : u < 27) :
    ℓ * rho2 τ ℓ u ≤ 2300000000000000 / ℓ + Real.exp (-(u0 ℓ / 3)) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  set L := 11 * Lam u / ℓ with hLdef
  set c := 1.003 / ℓ
  have hL0 : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hc0 : 0 ≤ c := by positivity
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have hsm : u < u0 ℓ - 2 := by linarith
  have key : ∀ rmin : ℝ, 0 < rmin → rmin ≤ Dickman.ratio (u - 1) - 0.0012 →
      ℓ * rho2 τ ℓ u ≤ ℓ * (1.0004 / 2 * ((4 * L) ^ 2 + 2 * ((8 * L + c) ^ 2 * M8 rmin +
        0 ^ 2 * M6 rmin) / u)) := by
    intro rmin hrmin hr
    apply mul_le_mul_of_nonneg_left _ hℓ0.le
    refine hR.rho2_gen (H := (4 * L) ^ 2) (X1 := 8 * L + c) (X2 := 0) (rmin := rmin)
      (by positivity) (by positivity) le_rfl hrmin hr ?_ ?_
    · intro w hw1 hwu
      rw [Dp_eq_Da hℓ0 (by linarith), hR.Da_zero_low hsm (by linarith) (by linarith), add_zero]
      have h1 := hR.absDA_head hw1.le hwu
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    · intro w huw hwU
      obtain ⟨hA0, hA1⟩ := hR.DA_tail_le huw.le
      obtain ⟨hd0, hd1⟩ := hR.Da_small h27 huw.le
      rw [Dp_eq_Da hℓ0 (by linarith)]
      have hs : 0 ≤ w - u := by linarith
      have hc4 : (w - u) ^ 2 * (1 + (w - u)) ^ 2 ≤ (1 + (w - u)) ^ 4 := by
        have : (w - u) ^ 2 ≤ (1 + (w - u)) ^ 2 := pow_le_pow_left₀ hs (by linarith) 2
        nlinarith [sq_nonneg (1 + (w - u))]
      have e : 1.003 * (w - u) ^ 2 * (1 + (w - u)) ^ 2 / ℓ =
          c * ((w - u) ^ 2 * (1 + (w - u)) ^ 2) := by simp only [c]; ring
      rw [e] at hd1
      constructor
      · linarith
      · have := mul_le_mul_of_nonneg_left hc4 hc0
        nlinarith
  have hE := Real.exp_pos (-(u0 ℓ / 3))
  rcases le_or_gt u 10 with h10 | h10
  · have h := key 0.9988 (by norm_num) (by linarith [hR.r0_ge_one])
    have hΛ : Lam u ≤ 121 * 2.7726 := (Lam_mono (by linarith) h10).trans Lam_10_le
    have hM := M8_09988
    have hM0 := M8_nonneg (r := 0.9988) (by norm_num)
    have hb : 121 * Lam u ^ 2 * (16 + 256 * M8 0.9988 / u) + 4.025 * M8 0.9988 / u ≤ 4.59e15 := by
      have h1 : M8 0.9988 / u ≤ 110800 / 2 := by
        rw [div_le_div_iff₀ hu0 (by norm_num)]; nlinarith
      have h2 : Lam u ^ 2 ≤ (121 * 2.7726) ^ 2 := pow_le_pow_left₀ hΛ0 hΛ 2
      have e1 : 256 * M8 0.9988 / u = 256 * (M8 0.9988 / u) := by ring
      have e2 : 4.025 * M8 0.9988 / u = 4.025 * (M8 0.9988 / u) := by ring
      rw [e1, e2]
      have h3 : 0 ≤ M8 0.9988 / u := by positivity
      have h4 : 16 + 256 * (M8 0.9988 / u) ≤ 16 + 256 * (110800 / 2) := by linarith
      calc 121 * Lam u ^ 2 * (16 + 256 * (M8 0.9988 / u)) + 4.025 * (M8 0.9988 / u)
          ≤ 121 * (121 * 2.7726) ^ 2 * (16 + 256 * (110800 / 2)) + 4.025 * (110800 / 2) := by
            gcongr
        _ ≤ 4.59e15 := by norm_num
    have hn := remB_small_num hℓ0 hΛ0 hM0 hu0 hb
    have e : ℓ * (1.0004 / 2 * ((4 * L) ^ 2 + 2 * ((8 * L + c) ^ 2 * M8 0.9988 + 0 ^ 2 *
        M6 0.9988) / u)) = ℓ * (1.0004 / 2 * ((4 * (11 * Lam u / ℓ)) ^ 2 +
        2 * ((8 * (11 * Lam u / ℓ) + 1.003 / ℓ) ^ 2 * M8 0.9988 + 0 ^ 2 * M6 0.9988) / u)) := rfl
    linarith
  · have h := key 2.1888 (by norm_num) (by linarith [ratio_ge_219 (v := u - 1) (by linarith)])
    have hΛ : Lam u ≤ 784 * 3.4658 := (Lam_mono (by linarith) h27.le).trans Lam_27_le
    have hM := M8_2188
    have hM0 := M8_nonneg (r := 2.1888) (by norm_num)
    have hb : 121 * Lam u ^ 2 * (16 + 256 * M8 2.1888 / u) + 4.025 * M8 2.1888 / u ≤ 4.59e15 := by
      have h1 : M8 2.1888 / u ≤ 312 / 10 := by
        rw [div_le_div_iff₀ hu0 (by norm_num)]; nlinarith
      have h2 : Lam u ^ 2 ≤ (784 * 3.4658) ^ 2 := pow_le_pow_left₀ hΛ0 hΛ 2
      have e1 : 256 * M8 2.1888 / u = 256 * (M8 2.1888 / u) := by ring
      have e2 : 4.025 * M8 2.1888 / u = 4.025 * (M8 2.1888 / u) := by ring
      rw [e1, e2]
      have h3 : 0 ≤ M8 2.1888 / u := by positivity
      calc 121 * Lam u ^ 2 * (16 + 256 * (M8 2.1888 / u)) + 4.025 * (M8 2.1888 / u)
          ≤ 121 * (784 * 3.4658) ^ 2 * (16 + 256 * (312 / 10)) + 4.025 * (312 / 10) := by
            gcongr
        _ ≤ 4.59e15 := by norm_num
    have hn := remB_small_num (M := M8 2.1888) hℓ0 hΛ0 hM0 hu0 hb
    have hn' : ℓ * (1.0004 / 2 * ((4 * L) ^ 2 + 2 * ((8 * L + c) ^ 2 * M8 2.1888 + 0 ^ 2 *
        M6 2.1888) / u)) ≤ 2300000000000000 / ℓ := by
      have e : 0 ^ 2 * M6 2.1888 = (0 : ℝ) ^ 2 * M6 0.9988 := by simp
      rw [e]; exact hn
    linarith

/-- **Remainder (b)** (lines 440-450). -/
theorem remB : RemB := by
  intro τ ℓ u hR
  refine ⟨fun h27 hbig => hR.remB_big h27 hbig, fun h27 hsm => ?_, fun h27 => hR.remB_small h27⟩
  have h := hR.remB_mid h27 hsm
  have e : 4000 * lamL τ ℓ * Xu u + lamL τ ℓ * Xu u =
      4000 * lamL τ ℓ * Xu u + lamL τ ℓ * Xu u := rfl
  linarith

end BSaias.Large

end
