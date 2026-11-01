module

public import RequestProject.Beurling.Noise.BSL57PA
public import RequestProject.Beurling.Noise.BSL57PRed

/-!
# Lemma 5.7, remainder (d) (04c-saias.tex, lines 456-460): `remD : RemD`

`ℓρ₄ ≤ K' E_π[(1+w) D'₊ e^{D'₊} 1[w ≤ Ū]]` (`rho4_le`); by (P1)–(P3) and the moments with
`r(u-1) - 0.0012 ≥ 4.5888` (`u ≥ 27`) this is at most `(1+u)(27.4λ + 0.56α')`, below
`(0.21λ + 0.004α') K'u² log(1+u)`. For `u < 27`, `a' = 0` and `D_a` vanishes below
`u₀ - 0.26`, so `D_a ≤ 1.003 s²(1+s)²/ℓ`, and the bound is `≤ 1.95·10⁹/ℓ ≤ 2·10⁹/ℓ`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

variable {τ ℓ u : ℝ}

lemma log_ge_329 {x : ℝ} (hx : 27 ≤ x) : 3.29 ≤ Real.log x := by
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl3 : (1.098 : ℝ) ≤ Real.log 3 := by
    have := Real.log_two_gt_d9
    have h3 : Real.log 3 = Real.log 2 + Real.log 1.5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h15 : (0.405 : ℝ) ≤ Real.log 1.5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_bound' (x := (0.405 : ℝ)) (by norm_num) (by norm_num) (n := 4)
        (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    linarith
  have := Real.log_le_log (by norm_num) hx
  linarith

lemma Lam_27_le : Lam 27 ≤ 784 * 3.4658 := by
  unfold Lam
  have h : Real.log (2 + 27) ≤ 5 * Real.log 2 := by
    have e : (5 : ℝ) * Real.log 2 = Real.log (2 ^ 5) := by rw [Real.log_pow]; norm_num
    rw [e]; exact Real.log_le_log (by norm_num) (by norm_num)
  have := Real.log_two_lt_d9
  norm_num at h ⊢
  nlinarith

/-- The `L`-only polynomial identity for remainder (d). -/
lemma polyD_eq (L h a q t : ℝ) :
    (1 + t) * (L * (h + 8 * t * (1 + t) ^ 3) + a * (t + 0.2502) +
      (t ^ 2 + 0.2502 * t + 0.0314) * q) =
    (L * h + 0.2502 * a + 0.0314 * q) +
      ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) * t +
      ((8 * L + a + 0.2502 * q) + (24 * L + q)) * t ^ 2 + ((24 * L + q) + 24 * L) * t ^ 3 +
      (24 * L + 8 * L) * t ^ 4 + 8 * L * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 := by ring

lemma momD_big {K L h a q : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (_hh0 : 0 ≤ h) (hh : h ≤ 28 / 27) :
    K * (L * h + 0.2502 * a + 0.0314 * q) / 4.5888 +
      K * ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9 ≤ K * (2.448 * L + 0.1346 * a + 0.0597 * q) := by
  have hLh : L * h ≤ 28 / 27 * L := by nlinarith
  have e : K * (L * h + 0.2502 * a + 0.0314 * q) / 4.5888 +
      K * ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9 = K * ((L * h) * (1 / 4.5888 + 1 / 4.5888 ^ 2) +
        L * (8 / 4.5888 ^ 2 + 64 / 4.5888 ^ 3 + 288 / 4.5888 ^ 4 + 768 / 4.5888 ^ 5 +
          960 / 4.5888 ^ 6) +
        a * (0.2502 / 4.5888 + 1.2502 / 4.5888 ^ 2 + 2 / 4.5888 ^ 3) +
        q * (0.0314 / 4.5888 + 0.2816 / 4.5888 ^ 2 + 2.5004 / 4.5888 ^ 3 + 6 / 4.5888 ^ 4)) := by
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hK
  norm_num
  nlinarith

lemma momD_total {K L h a q u : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hh0 : 0 ≤ h) (hh : h ≤ 28 / 27) (h27 : 27 ≤ u) :
    K * (L * h + 0.2502 * a + 0.0314 * q) + (K * (L * h + 0.2502 * a + 0.0314 * q) / 4.5888 +
      K * ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9) / u ≤ K * (1.1282 * L + 0.2552 * a + 0.0337 * q) := by
  have hT := momD_big hK hL ha hq hh0 hh
  have hT0 : 0 ≤ K * (L * h + 0.2502 * a + 0.0314 * q) / 4.5888 +
      K * ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9 := by positivity
  generalize K * (L * h + 0.2502 * a + 0.0314 * q) / 4.5888 +
      K * ((L * h + 0.2502 * a + 0.0314 * q) + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9 = T at hT hT0 ⊢
  have hTu : T / u ≤ K * (2.448 * L + 0.1346 * a + 0.0597 * q) / 27 :=
    (div_le_div_of_nonneg_left hT0 (by norm_num) h27).trans
      (div_le_div_of_nonneg_right hT (by norm_num))
  have hLh : L * h ≤ 28 / 27 * L := by nlinarith
  have h1 : K * (L * h + 0.2502 * a + 0.0314 * q) ≤
      K * (28 / 27 * L + 0.2502 * a + 0.0314 * q) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  have h2 : K * (2.448 * L + 0.1346 * a + 0.0597 * q) / 27 ≤
      K * (0.0907 * L + 0.005 * a + 0.0023 * q) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_nonneg hK hL; have := mul_nonneg hK ha; have := mul_nonneg hK hq
    nlinarith
  have h3 : K * (28 / 27 * L + 0.2502 * a + 0.0314 * q) +
      K * (0.0907 * L + 0.005 * a + 0.0023 * q) ≤ K * (1.1282 * L + 0.2552 * a + 0.0337 * q) := by
    have := mul_nonneg hK hL; have := mul_nonneg hK ha; have := mul_nonneg hK hq
    nlinarith
  linarith

lemma remD_big_num {R L lam α a q u : ℝ}
    (h1 : R ≤ Kp * (1.0004 * (1 + u) * (1.1282 * L + 0.2552 * a + 0.0337 * q)))
    (hL : L ≤ 11.011 * lam) (ha : a ≤ α) (hq : q ≤ α / 63244) (hlam : 0 ≤ lam) (hα : 0 ≤ α)
    (h27 : 27 ≤ u) (hlog : 3.29 ≤ Real.log (1 + u)) :
    R ≤ (0.21 * lam + 0.004 * α) * Xu u := by
  have hKp : Kp = 2.2 := rfl
  have hX : Kp * u ^ 2 * 3.29 ≤ Xu u := by
    unfold Xu; rw [hKp]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hb : 1.1282 * L + 0.2552 * a + 0.0337 * q ≤ 12.423 * lam + 0.2553 * α := by nlinarith
  have hc : Kp * (1.0004 * (1 + u) * (1.1282 * L + 0.2552 * a + 0.0337 * q)) ≤
      Kp * (1.0004 * (1 + u) * (12.423 * lam + 0.2553 * α)) := by
    rw [hKp]; apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  have hu2 : 27 * u ≤ u ^ 2 := by nlinarith
  have hd : Kp * (1.0004 * (1 + u) * (12.423 * lam + 0.2553 * α)) ≤
      (0.21 * lam + 0.004 * α) * (Kp * u ^ 2 * 3.29) := by
    rw [hKp]
    have e1 : 2.2 * (1.0004 * (1 + u) * (12.423 * lam + 0.2553 * α)) =
        lam * (2.2 * 1.0004 * 12.423 * (1 + u)) + α * (2.2 * 1.0004 * 0.2553 * (1 + u)) := by
      ring
    have e2 : (0.21 * lam + 0.004 * α) * (2.2 * u ^ 2 * 3.29) =
        lam * (0.21 * 2.2 * 3.29 * u ^ 2) + α * (0.004 * 2.2 * 3.29 * u ^ 2) := by ring
    rw [e1, e2]
    have t1 : 2.2 * 1.0004 * 12.423 * (1 + u) ≤ 0.21 * 2.2 * 3.29 * u ^ 2 := by nlinarith
    have t2 : 2.2 * 1.0004 * 0.2553 * (1 + u) ≤ 0.004 * 2.2 * 3.29 * u ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t1 hlam, mul_le_mul_of_nonneg_left t2 hα]
  calc R ≤ _ := h1
    _ ≤ _ := hc
    _ ≤ _ := hd
    _ ≤ (0.21 * lam + 0.004 * α) * Xu u := mul_le_mul_of_nonneg_left hX (by positivity)

/-- **Remainder (d)**, `u ≥ 27`: the integral bound. -/
lemma LargeRange.remD_big_int (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) :
    ℓ * rho4 τ ℓ u ≤ Kp * (1.0004 * (1 + u) * (1.1282 * (11 * Lam u / ℓ) +
      0.2552 * aprime ℓ u + 0.0337 * (1 / √ℓ))) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  set L := 11 * Lam u / ℓ with hLdef
  set h := (1 + u) / u
  set a := aprime ℓ u
  set q := 1 / √ℓ
  have hL0 : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hh0 : 0 ≤ h := by positivity
  have ha0 := hR.ap_nonneg
  have hq0 : 0 ≤ q := by have := hR.sqrt_pos; positivity
  set K := 1.0004 * (1 + u)
  have hK0 : 0 ≤ K := by positivity
  set p0 := L * h + 0.2502 * a + 0.0314 * q
  have hp0 : 0 ≤ p0 := by positivity
  have hr : 4.5888 ≤ Dickman.ratio (u - 1) - 0.0012 := by
    have := ratio_ge_459 (v := u - 1) (by linarith); linarith
  have hS := hR.Uf_ge
  have hm := master9 (u := u) (γ := 0.0012) (A := K * p0) (rmin := 4.5888) hu (by norm_num) hr
    (by positivity) (a0 := K * p0) (a1 := K * (p0 + (8 * L + a + 0.2502 * q)))
    (a2 := K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) (a3 := K * ((24 * L + q) + 24 * L))
    (a4 := K * (24 * L + 8 * L)) (a5 := K * (8 * L)) (a6 := 0) (a7 := 0) (a8 := 0)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) le_rfl le_rfl le_rfl (S := Ioc (u - 1) (Uf τ ℓ)) Ioc_subset_Ioi_self
    measurableSet_Ioc (f := fun w => (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0))
    (by
      apply integrableOn_Ioc_of_continuousAt (by linarith)
      intro w hw
      have hD := continuousAt_Dp (u := u) hℓ0 hw
      exact ((((continuousAt_const.add continuousAt_id).mul (hD.max continuousAt_const)).mul
        (hD.max continuousAt_const).rexp).mul ((Dickman.continuous_rho.comp
          (continuous_id.sub continuous_const)).continuousAt)).div continuousAt_id hw.ne')
    (by
      intro w hw
      have : 0 ≤ 1 + w := by linarith [hw.1]
      positivity)
    (by
      intro w hw hwu
      have hw1 : u - 1 ≤ w := hw.1.le
      have he := hR.exp_Dp_le hw1 hw.2
      rw [max_eq_right (by linarith : w - u ≤ 0), mul_zero, Real.exp_zero, mul_one] at he
      have hD : max (Dp ℓ u w) 0 ≤ p0 := by
        apply max_le _ hp0
        rw [Dp_eq_Da hℓ0 (by linarith)]
        have h1 := hA_head_upper hu hw1 hwu
        obtain ⟨-, h2⟩ := hR.Da_head hw1 hwu
        have h3 : 11 / ℓ * hA u w ≤ L * h := by
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
          have e : 11 / ℓ * ((1 + u) / u * Lam u) = L * h := by
            simp only [L, h]; ring
          linarith
        have e : 0.0314 / √ℓ = 0.0314 * q := by simp only [q]; ring
        simp only [p0]; linarith
      have hw0 : 0 ≤ 1 + w := by linarith
      calc (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0)
          ≤ (1 + u) * p0 * 1.0004 :=
            mul_le_mul (mul_le_mul (by linarith) hD (le_max_right _ _) (by linarith)) he
              (Real.exp_pos _).le (by positivity)
        _ = K * p0 := by simp only [K]; ring)
    (by
      intro w hw huw
      beta_reduce
      have he := hR.exp_Dp_le hw.1.le hw.2
      rw [max_eq_left (by linarith : 0 ≤ w - u)] at he
      obtain ⟨hD0, hD⟩ := hR.Dp_tail huw.le
      rw [max_eq_left hD0] at he ⊢
      have hs : 0 ≤ w - u := by linarith
      have h1w : 1 + w ≤ (1 + u) * (1 + (w - u)) := by nlinarith
      have hP0 : 0 ≤ L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) + a * ((w - u) + 0.2502) +
          ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q := by positivity
      have hD' : Dp ℓ u w ≤ L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) + a * ((w - u) + 0.2502) +
          ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q := by
        have e : ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ =
            ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q := by simp only [q]; ring
        simp only [L, h, a] at hD ⊢; linarith
      have hpoly := polyD_eq L h a q (w - u)
      calc (1 + w) * Dp ℓ u w * Real.exp (Dp ℓ u w)
          ≤ ((1 + u) * (1 + (w - u))) * (L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) +
              a * ((w - u) + 0.2502) + ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q) *
              (1.0004 * Real.exp (0.0012 * (w - u))) :=
            mul_le_mul (mul_le_mul h1w hD' hD0 (by positivity)) he (Real.exp_pos _).le
              (by positivity)
        _ = (K * p0 + K * (p0 + (8 * L + a + 0.2502 * q)) * (w - u) +
              K * ((8 * L + a + 0.2502 * q) + (24 * L + q)) * (w - u) ^ 2 +
              K * ((24 * L + q) + 24 * L) * (w - u) ^ 3 + K * (24 * L + 8 * L) * (w - u) ^ 4 +
              K * (8 * L) * (w - u) ^ 5 + 0 * (w - u) ^ 6 + 0 * (w - u) ^ 7 +
              0 * (w - u) ^ 8) * Real.exp (0.0012 * (w - u)) := by
            have e2 : ((1 + u) * (1 + (w - u))) * (L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) +
                a * ((w - u) + 0.2502) + ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q) *
                (1.0004 * Real.exp (0.0012 * (w - u))) = K * ((1 + (w - u)) *
                (L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) + a * ((w - u) + 0.2502) +
                ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * q)) *
                Real.exp (0.0012 * (w - u)) := by simp only [K]; ring
            rw [e2, hpoly]; simp only [p0]; ring)
  -- assemble
  have hρ4 := hR.rho4_le
  have hKp : Kp = 2.2 := rfl
  have hfin : ℓ * rho4 τ ℓ u ≤ Kp * (K * p0 + (K * p0 / 4.5888 +
      K * (p0 + (8 * L + a + 0.2502 * q)) / 4.5888 ^ 2 +
      2 * (K * ((8 * L + a + 0.2502 * q) + (24 * L + q))) / 4.5888 ^ 3 +
      6 * (K * ((24 * L + q) + 24 * L)) / 4.5888 ^ 4 + 24 * (K * (24 * L + 8 * L)) / 4.5888 ^ 5 +
      120 * (K * (8 * L)) / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7 + 5040 * 0 / 4.5888 ^ 8 +
      40320 * 0 / 4.5888 ^ 9) / u) := by
    refine hρ4.trans ?_
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hm (by rw [hKp]; norm_num)
  have hh : h ≤ 28 / 27 := by simp only [h]; rw [div_le_iff₀ hu0]; linarith
  refine hfin.trans (mul_le_mul_of_nonneg_left ?_ (by rw [hKp]; norm_num))
  exact momD_total hK0 hL0 ha0 hq0 hh0 hh h27

/-- **Remainder (d)**, `u ≥ 27`. -/
lemma LargeRange.remD_big (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) :
    ℓ * rho4 τ ℓ u ≤ (0.21 * lamL τ ℓ + 0.004 * alphaL τ ℓ) * Xu u := by
  have hℓ0 := hR.ℓ_pos
  have hu := hR.2.2.2.1
  have h1 := hR.remD_big_int h27
  have hΛ := hR.Lam_le
  have hL : 11 * Lam u / ℓ ≤ 11.011 * lamL τ ℓ := by rw [div_le_iff₀ hℓ0]; nlinarith
  have hap := hR.ap_le
  have hq : 1 / √ℓ ≤ alphaL τ ℓ / 63244 := hR.inv_sqrt_le
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hlog := log_ge_329 (x := 1 + u) (by linarith)
  exact remD_big_num h1 hL hap hq hlam0 hα0 h27 hlog

/-! ## `u < 27` -/

/-- For `u < u₀ - 2`, `a(ℓ, u) = 0` and `D_a = a(m, w)` vanishes for `w ≤ u₀ - 0.26`. -/
lemma LargeRange.Da_zero_low (hR : LargeRange τ ℓ u) (hu2 : u < u0 ℓ - 2) {w : ℝ}
    (hw1 : 1 ≤ w) (hw : w ≤ u0 ℓ - 0.26) : Da ℓ u w = 0 := by
  have hℓ0 := hR.ℓ_pos
  unfold Da
  rw [aQ_eq_zero (m := ℓ) (by linarith)]
  rcases le_or_gt w (u0 ℓ - 3) with h3 | h3
  · rw [aQ_mOf_eq_zero_low hℓ0 hw1 h3]; ring
  · rw [aQ_mOf_eq_zero_mid hR.2.2.1 h3.le hw]; ring

/-- For `u < 27` and `w ≥ u`: `0 ≤ D_a ≤ 1.003 s²(1+s)²/ℓ`. -/
lemma LargeRange.Da_small (hR : LargeRange τ ℓ u) (h27 : u < 27) {w : ℝ} (huw : u ≤ w) :
    0 ≤ Da ℓ u w ∧ Da ℓ u w ≤ 1.003 * (w - u) ^ 2 * (1 + (w - u)) ^ 2 / ℓ := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 := hR.u0_ge
  have hs : 0 ≤ w - u := by linarith
  have hRHS : 0 ≤ 1.003 * (w - u) ^ 2 * (1 + (w - u)) ^ 2 / ℓ := by positivity
  have hDa : Da ℓ u w = aQ (mOf ℓ w) w := by
    unfold Da; rw [aQ_eq_zero (m := ℓ) (by linarith)]; ring
  rw [hDa]
  refine ⟨aQ_nonneg _ _, ?_⟩
  rcases le_or_gt w (u0 ℓ - 0.26) with hw | hw
  · have := hR.Da_zero_low (by linarith) (by linarith) hw
    rw [hDa] at this; rw [this]; exact hRHS
  · have h1 := aQ_mOf_le hR.2.2.1 (w := w) (by linarith)
    have hsq := hR.sqrt_pos
    have hm : max (w - u0 ℓ) 0 ≤ w - u := max_le (by linarith) hs
    have hm0 : 0 ≤ max (w - u0 ℓ) 0 := le_max_right _ _
    have h2 : aQ (mOf ℓ w) w ≤ (1 + (w - u)) ^ 2 / √ℓ := by
      refine h1.trans ?_
      have e : (max (w - u0 ℓ) 0) ^ 2 / (2 * √ℓ) + 0.2502 * max (w - u0 ℓ) 0 / √ℓ +
          0.0314 / √ℓ = ((max (w - u0 ℓ) 0) ^ 2 / 2 + 0.2502 * max (w - u0 ℓ) 0 + 0.0314) / √ℓ
          := by field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hsq.le
      nlinarith [pow_le_pow_left₀ hm0 hm 2]
    refine h2.trans ?_
    -- `√ℓ ≤ 1.003 s²`
    have hsu : u0 ℓ - 27.26 ≤ w - u := by linarith
    have hsq2 : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
    have hkey : √ℓ ≤ 1.003 * (w - u) ^ 2 := by
      rw [← hsq2]
      have : (u0 ℓ - 27.26) ^ 2 ≤ (w - u) ^ 2 := pow_le_pow_left₀ (by linarith) hsu 2
      nlinarith
    have hℓ' : ℓ ≤ 1.003 * (w - u) ^ 2 * √ℓ := by
      have := Real.mul_self_sqrt hℓ0.le
      nlinarith
    rw [div_le_div_iff₀ hsq hℓ0]
    have hp : 0 ≤ (1 + (w - u)) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hℓ' hp
    linarith

lemma momD_small_val (K L h c : ℝ) :
    K * (L * h) / 0.9988 + K * (L * h + 8 * L) / 0.9988 ^ 2 +
      2 * (K * (8 * L + (24 * L + c))) / 0.9988 ^ 3 +
      6 * (K * ((24 * L + c) + (24 * L + 2 * c))) / 0.9988 ^ 4 +
      24 * (K * ((24 * L + 2 * c) + (8 * L + c))) / 0.9988 ^ 5 +
      120 * (K * (8 * L + c)) / 0.9988 ^ 6 + 720 * 0 / 0.9988 ^ 7 + 5040 * 0 / 0.9988 ^ 8 +
      40320 * 0 / 0.9988 ^ 9 = K * ((L * h) * (1 / 0.9988 + 1 / 0.9988 ^ 2) +
        L * (8 / 0.9988 ^ 2 + 64 / 0.9988 ^ 3 + 288 / 0.9988 ^ 4 + 768 / 0.9988 ^ 5 +
          960 / 0.9988 ^ 6) +
        c * (2 / 0.9988 ^ 3 + 18 / 0.9988 ^ 4 + 72 / 0.9988 ^ 5 + 120 / 0.9988 ^ 6)) := by
  ring

lemma momD_small_total {K L h c u : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hh0 : 0 ≤ h) (hh : h ≤ 1.5) (hu : 2 ≤ u) :
    K * (L * h) + (K * (L * h) / 0.9988 + K * (L * h + 8 * L) / 0.9988 ^ 2 +
      2 * (K * (8 * L + (24 * L + c))) / 0.9988 ^ 3 +
      6 * (K * ((24 * L + c) + (24 * L + 2 * c))) / 0.9988 ^ 4 +
      24 * (K * ((24 * L + 2 * c) + (8 * L + c))) / 0.9988 ^ 5 +
      120 * (K * (8 * L + c)) / 0.9988 ^ 6 + 720 * 0 / 0.9988 ^ 7 + 5040 * 0 / 0.9988 ^ 8 +
      40320 * 0 / 0.9988 ^ 9) / u ≤ K * (1053.7 * L + 106.8 * c) := by
  rw [momD_small_val]
  have hLh : L * h ≤ 1.5 * L := by nlinarith
  have hLh0 : 0 ≤ L * h := mul_nonneg hL hh0
  set T := (L * h) * (1 / 0.9988 + 1 / 0.9988 ^ 2) +
        L * (8 / 0.9988 ^ 2 + 64 / 0.9988 ^ 3 + 288 / 0.9988 ^ 4 + 768 / 0.9988 ^ 5 +
          960 / 0.9988 ^ 6) +
        c * (2 / 0.9988 ^ 3 + 18 / 0.9988 ^ 4 + 72 / 0.9988 ^ 5 + 120 / 0.9988 ^ 6) with hT
  have hT1 : T ≤ 2104.3 * L + 213.5 * c := by
    simp only [hT]; norm_num; nlinarith
  have hT0 : 0 ≤ T := by simp only [hT]; positivity
  have h2 : K * T / u ≤ K * T / 2 :=
    div_le_div_of_nonneg_left (mul_nonneg hK hT0) (by norm_num) hu
  have h3 : K * T / 2 ≤ K * (1052.15 * L + 106.75 * c) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hT1 hK
    nlinarith
  have h4 : K * (L * h) ≤ K * (1.5 * L) := mul_le_mul_of_nonneg_left hLh hK
  have h5 : K * (1.5 * L) + K * (1052.15 * L + 106.75 * c) ≤ K * (1053.7 * L + 106.8 * c) := by
    have := mul_nonneg hK hL; have := mul_nonneg hK hc; nlinarith
  linarith

lemma remD_small_num {u ℓ : ℝ} (hu : 2 ≤ u) (h27 : u < 27) (hℓ0 : 0 < ℓ) :
    Kp * (1.0004 * (1 + u) * (1053.7 * (11 * Lam u / ℓ) + 106.8 * (1.003 / ℓ))) ≤
      2000000000 / ℓ := by
  have hΛ : Lam u ≤ Lam 27 := Lam_mono (by linarith) h27.le
  have hΛ27 := Lam_27_le
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have hKp : Kp = 2.2 := rfl
  rw [hKp]
  have e : 2.2 * (1.0004 * (1 + u) * (1053.7 * (11 * Lam u / ℓ) + 106.8 * (1.003 / ℓ))) =
      (2.2 * 1.0004 * (1053.7 * 11 * ((1 + u) * Lam u) + 106.8 * 1.003 * (1 + u))) / ℓ := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hℓ0.le
  have h3 : (1 + u) * Lam u ≤ 28 * (784 * 3.4658) := by
    have := mul_le_mul (by linarith : 1 + u ≤ 28) (hΛ.trans hΛ27) hΛ0 (by norm_num)
    linarith
  nlinarith

set_option maxHeartbeats 800000 in
/-- **Remainder (d)**, `u < 27`. -/
lemma LargeRange.remD_small (hR : LargeRange τ ℓ u) (h27 : u < 27) :
    ℓ * rho4 τ ℓ u ≤ 2000000000 / ℓ := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  set L := 11 * Lam u / ℓ with hLdef
  set h := (1 + u) / u
  set c := 1.003 / ℓ
  have hL0 : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hh0 : 0 ≤ h := by positivity
  have hc0 : 0 ≤ c := by positivity
  set K := 1.0004 * (1 + u)
  have hK0 : 0 ≤ K := by positivity
  have hr : 0.9988 ≤ Dickman.ratio (u - 1) - 0.0012 := by linarith [hR.r0_ge_one]
  have hm := master9 (u := u) (γ := 0.0012) (A := K * (L * h)) (rmin := 0.9988) hu (by norm_num)
    hr (by positivity) (a0 := K * (L * h)) (a1 := K * (L * h + 8 * L))
    (a2 := K * (8 * L + (24 * L + c))) (a3 := K * ((24 * L + c) + (24 * L + 2 * c)))
    (a4 := K * ((24 * L + 2 * c) + (8 * L + c))) (a5 := K * (8 * L + c)) (a6 := 0) (a7 := 0)
    (a8 := 0) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) le_rfl le_rfl le_rfl (S := Ioc (u - 1) (Uf τ ℓ)) Ioc_subset_Ioi_self
    measurableSet_Ioc (f := fun w => (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0))
    (by
      apply integrableOn_Ioc_of_continuousAt (by linarith)
      intro w hw
      have hD := continuousAt_Dp (u := u) hℓ0 hw
      exact ((((continuousAt_const.add continuousAt_id).mul (hD.max continuousAt_const)).mul
        (hD.max continuousAt_const).rexp).mul ((Dickman.continuous_rho.comp
          (continuous_id.sub continuous_const)).continuousAt)).div continuousAt_id hw.ne')
    (by
      intro w hw
      have : 0 ≤ 1 + w := by linarith [hw.1]
      positivity)
    (by
      intro w hw hwu
      have hw1 : u - 1 ≤ w := hw.1.le
      have he := hR.exp_Dp_le hw1 hw.2
      rw [max_eq_right (by linarith : w - u ≤ 0), mul_zero, Real.exp_zero, mul_one] at he
      have hD : max (Dp ℓ u w) 0 ≤ L * h := by
        apply max_le _ (by positivity)
        rw [Dp_eq_Da hℓ0 (by linarith), hR.Da_zero_low (by linarith) (by linarith)
          (by linarith)]
        have h1 := hA_head_upper hu hw1 hwu
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
        have e : 11 / ℓ * ((1 + u) / u * Lam u) = L * h := by simp only [L, h]; ring
        linarith
      have hw0 : 0 ≤ 1 + w := by linarith
      calc (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0)
          ≤ (1 + u) * (L * h) * 1.0004 :=
            mul_le_mul (mul_le_mul (by linarith) hD (le_max_right _ _) (by linarith)) he
              (Real.exp_pos _).le (by positivity)
        _ = K * (L * h) := by simp only [K]; ring)
    (by
      intro w hw huw
      beta_reduce
      have he := hR.exp_Dp_le hw.1.le hw.2
      rw [max_eq_left (by linarith : 0 ≤ w - u)] at he
      obtain ⟨hA0, hA1⟩ := hA_tail hu huw.le
      obtain ⟨hd0, hd1⟩ := hR.Da_small h27 huw.le
      have hs : 0 ≤ w - u := by linarith
      have hD0 : 0 ≤ Dp ℓ u w := by
        rw [Dp_eq_Da hℓ0 (by linarith)]
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ 11 / ℓ) hA0; linarith
      rw [max_eq_left hD0] at he ⊢
      have hD : Dp ℓ u w ≤ L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) +
          c * ((w - u) ^ 2 * (1 + (w - u)) ^ 2) := by
        rw [Dp_eq_Da hℓ0 (by linarith)]
        have := mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
        have e1 : 11 / ℓ * (Lam u * ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3)) =
            L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) := by simp only [L, h]; ring
        have e2 : 1.003 * (w - u) ^ 2 * (1 + (w - u)) ^ 2 / ℓ =
            c * ((w - u) ^ 2 * (1 + (w - u)) ^ 2) := by simp only [c]; ring
        linarith
      have h1w : 1 + w ≤ (1 + u) * (1 + (w - u)) := by nlinarith
      calc (1 + w) * Dp ℓ u w * Real.exp (Dp ℓ u w)
          ≤ ((1 + u) * (1 + (w - u))) * (L * (h + 8 * (w - u) * (1 + (w - u)) ^ 3) +
              c * ((w - u) ^ 2 * (1 + (w - u)) ^ 2)) *
              (1.0004 * Real.exp (0.0012 * (w - u))) :=
            mul_le_mul (mul_le_mul h1w hD hD0 (by positivity)) he (Real.exp_pos _).le
              (by positivity)
        _ = _ := by simp only [K]; ring)
  have hρ4 := hR.rho4_le
  have hKp : Kp = 2.2 := rfl
  have hfin : ℓ * rho4 τ ℓ u ≤ Kp * (K * (L * h) + (K * (L * h) / 0.9988 +
      K * (L * h + 8 * L) / 0.9988 ^ 2 + 2 * (K * (8 * L + (24 * L + c))) / 0.9988 ^ 3 +
      6 * (K * ((24 * L + c) + (24 * L + 2 * c))) / 0.9988 ^ 4 +
      24 * (K * ((24 * L + 2 * c) + (8 * L + c))) / 0.9988 ^ 5 +
      120 * (K * (8 * L + c)) / 0.9988 ^ 6 + 720 * 0 / 0.9988 ^ 7 + 5040 * 0 / 0.9988 ^ 8 +
      40320 * 0 / 0.9988 ^ 9) / u) := by
    refine hρ4.trans ?_
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hm (by rw [hKp]; norm_num)
  have hh : h ≤ 1.5 := by simp only [h]; rw [div_le_iff₀ hu0]; linarith
  have htot := momD_small_total hK0 hL0 hc0 hh0 hh hu
  have h2 := hfin.trans (mul_le_mul_of_nonneg_left htot (by rw [hKp]; norm_num))
  exact h2.trans (remD_small_num hu h27 hℓ0)

/-- **Remainder (d)** (lines 456-460). -/
theorem remD : RemD := by
  intro τ ℓ u hR
  exact ⟨fun h27 => hR.remD_big h27, fun h27 => hR.remD_small h27⟩

end BSaias.Large

end
