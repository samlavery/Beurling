module

public import RequestProject.Beurling.Noise.BSL57RDefs
public import RequestProject.Beurling.Noise.BSL57

/-!
# Lemma 5.7: the remainders (a)–(f) added (lines 488-498), and Step 7(ii) from them

* `lemma57Ineq_of_remC` : `Lemma57Ineq` from the assembled bound `Lemma57RemC`;
* `remC_of_six` : `Lemma57RemC` from the six remainder bounds `RemA`–`RemF`;
* `regionLarge_of_six` : Step 7(ii) (`RegionLarge`) from `RemA`–`RemF`.
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- **Lemma 5.7, main inequality**, from the assembled remainder bound (lines 499-502). -/
theorem lemma57Ineq_of_remC (hrem : Lemma57RemC) : Lemma57Ineq := by
  intro τ ℓ u hR
  obtain ⟨hτ, hτℓ, hℓ, hu, -⟩ := id hR
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hdec := l57_decomp hR
  obtain ⟨hr27, hrs⟩ := hrem τ ℓ u hR
  have heq := epsL_eq (τ := τ) (ℓ := ℓ)
  have hlam := lamL_nonneg (τ := τ) hℓ0
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hℓ0 _
  have hε0 : 0 ≤ epsL τ ℓ := by rw [heq]; positivity
  have hκ0 : 0 ≤ kappa τ := by unfold kappa; linarith
  have hPB := PhiBen_nonneg (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0
  have hq1 : 1 / ℓ ≤ 900000000000000000 / ℓ :=
    div_le_div_of_nonneg_right (by norm_num) hℓ0.le
  have hq2 : 2500000000000000 / ℓ ≤ 900000000000000000 / ℓ :=
    div_le_div_of_nonneg_right (by norm_num) hℓ0.le
  rcases le_or_gt 27 u with h27 | h27
  · have hc : Kp * u ^ 2 * Real.log (1 + u) ≤ cfun τ ℓ u := by
      have := c0_ge h27
      unfold cfun
      nlinarith [mul_nonneg hℓ0.le hPB]
    have hc0 : 0 ≤ cfun τ ℓ u := by
      have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u)
      have : 0 ≤ Kp * u ^ 2 * Real.log (1 + u) := by unfold Kp; positivity
      linarith
    have hmax : ℓ * max (sA ℓ u) 0 = max (ℓ * sA ℓ u) 0 := by
      rw [mul_max_of_nonneg _ _ hℓ0.le, mul_zero]
    have hR27 := hr27 h27
    rw [hmax] at hR27
    refine alg_big hdec hR27 hε0 (by rw [heq]; linarith) (by rw [heq]; linarith) hc0
      (by split_ifs <;> norm_num) hq1 (neg_slack hR h27 hε0 hc)
  · have hbig : u < u0 ℓ - 2 := by linarith [u0_ge hℓ]
    rw [if_neg (not_le.mpr hbig)]
    obtain ⟨hsa, -⟩ := (lemma57Slack τ ℓ u hR).2 hbig
    have hc := cfun_ge_small hτ hτℓ hℓ hu h27.le
    exact alg_small hdec (hrs h27) hε0 (by rw [heq]; linarith) (by linarith) hsa hq2

/-! ## Auxiliary bounds for the assembly -/

lemma exp_ten_le : Real.exp 10 ≤ 31621 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 10 ≤ (2.7182818286 : ℝ) ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 10
  norm_num at this; linarith

/-- `e^{-u₀/3} ≤ 1/ℓ` for `ℓ ≥ 10¹⁸`. -/
lemma exp_neg_u0_le (hℓ : 1000000000000000000 ≤ ℓ) : Real.exp (-(u0 ℓ / 3)) ≤ 1 / ℓ := by
  have hu0 := u0_ge hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hsq : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
  have h4 : u0 ℓ ^ 4 = ℓ := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, Real.sq_sqrt hℓ0.le]
  set x := u0 ℓ / 3
  have hx : 10540 ≤ x := by simp only [x]; linarith
  have h5 := Real.pow_div_factorial_le_exp (x := x) (by linarith) 5
  norm_num [Nat.factorial] at h5
  have hℓx : ℓ = 81 * x ^ 4 := by rw [← h4]; simp only [x]; ring
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le hℓ0
  rw [hℓx]
  nlinarith [pow_pos (by linarith : (0 : ℝ) < x) 4]

/-- For `2 ≤ u ≤ 27`, `ℓΦ_ben ≥ 1.069·10⁷` (refining `cfun_ge_small`). -/
lemma ellPhiBen_ge_small (hτ : 100000000 ≤ τ) (hτℓ : 30 * τ < ℓ)
    (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) (hu27 : u ≤ 27) :
    10690000 ≤ ℓ * PhiBen τ ℓ u := by
  have hu0 : 0 < u := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hκ : 400000000 ≤ kappa τ := by unfold kappa; linarith
  have hκ0 : 0 ≤ kappa τ := by linarith
  have hκu : kappa τ ≤ 4 * ℓ / 30 + 1500 := by unfold kappa; linarith
  set y := kappa τ / (u * ℓ)
  have hy0 : 0 ≤ y := div_nonneg hκ0 (by positivity)
  have hy1 : y ≤ 0.07 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hr : Real.log 3 ≤ Dickman.ratio u :=
    le_trans ratio_two_ge (Dickman.ratio_monotoneOn (Set.mem_Ici.mpr (by norm_num))
      (Set.mem_Ici.mpr (by linarith)) hu)
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
  have hexp : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have h1 := Real.add_one_le_exp y
    rw [Real.exp_neg]
    have : (Real.exp y)⁻¹ ≤ 1 / (1 + y) := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have e : y / (1 + y) = 1 - 1 / (1 + y) := by field_simp; ring
    linarith
  have hPB := PhiBen_ge (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0
  have hℓy : ℓ * y = kappa τ / u := by simp only [y]; field_simp
  have hyy : ℓ * (y / (1 + y)) ≥ kappa τ / u / 1.07 := by
    rw [mul_div_assoc', hℓy]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  rcases le_or_gt 4 u with h4 | h4
  · have hm : 0.7723 ≤ 1 - 1 / (u * Dickman.ratio u) := by
      have : 4.392 ≤ u * Dickman.ratio u := by nlinarith
      have : 1 / (u * Dickman.ratio u) ≤ 1 / 4.392 := one_div_le_one_div_of_le (by norm_num) this
      norm_num at this ⊢; linarith
    have h2 : 400000000 / 27 ≤ kappa τ / u := by
      rw [div_le_div_iff₀ (by norm_num) hu0]; nlinarith
    have := mul_le_mul_of_nonneg_left (le_trans (mul_le_mul hexp hm (by norm_num)
      (by linarith [Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)])) hPB) hℓ0.le
    have h0 : 0 ≤ y / (1 + y) := div_nonneg hy0 (by linarith)
    have hyy' : kappa τ / u ≤ 1.07 * (ℓ * (y / (1 + y))) := by
      have := hyy.le; rw [div_le_iff₀ (by norm_num)] at this; linarith
    clear_value y
    linarith
  · have hm : 0.5446 ≤ 1 - 1 / (u * Dickman.ratio u) := by
      have : 2.196 ≤ u * Dickman.ratio u := by nlinarith
      have : 1 / (u * Dickman.ratio u) ≤ 1 / 2.196 := one_div_le_one_div_of_le (by norm_num) this
      norm_num at this ⊢; linarith
    have h2 : 400000000 / 4 ≤ kappa τ / u := by
      rw [div_le_div_iff₀ (by norm_num) hu0]; nlinarith
    have := mul_le_mul_of_nonneg_left (le_trans (mul_le_mul hexp hm (by norm_num)
      (by linarith [Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)])) hPB) hℓ0.le
    have h0 : 0 ≤ y / (1 + y) := div_nonneg hy0 (by linarith)
    have hyy' : kappa τ / u ≤ 1.07 * (ℓ * (y / (1 + y))) := by
      have := hyy.le; rw [div_le_iff₀ (by norm_num)] at this; linarith
    clear_value y
    linarith

/-- `Φ`-dominance with the paper's ratio: `ℓΦ_ben ≤ 1.0596 c(u)` for `2 ≤ u ≤ 27`. -/
lemma ellPhiBen_le_c (hτ : 100000000 ≤ τ) (hτℓ : 30 * τ < ℓ)
    (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) (hu27 : u ≤ 27) :
    ℓ * PhiBen τ ℓ u ≤ 1.0596 * cfun τ ℓ u := by
  have h1 := ellPhiBen_ge_small hτ hτℓ hℓ hu hu27
  have h2 := c0_ge_small hu hu27
  unfold cfun
  linarith

/-! ## The assembly -/

/-- **The remainders (a)–(f) added** (lines 488-498): `Lemma57RemC` from `RemA`–`RemF`. -/
theorem remC_of_six (hA : RemA) (hB : RemB) (hC : RemC) (hD : RemD) (hE : RemE)
    (hF : RemF) : Lemma57RemC := by
  intro τ ℓ u hR
  obtain ⟨hτ, hτℓ, hℓ, hu, hU⟩ := id hR
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hlam := lamL_nonneg (τ := τ) hℓ0
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hκ0 : 0 ≤ kappa τ := by unfold kappa; linarith
  have hPB := mul_nonneg hℓ0.le (PhiBen_nonneg (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hℓ0 _
  have hu0 := u0_ge hℓ
  obtain ⟨a1, a2⟩ := hA τ ℓ u hR
  obtain ⟨b1, b2, b3⟩ := hB τ ℓ u hR
  obtain ⟨c1, c2⟩ := hC τ ℓ u hR
  obtain ⟨d1, d2⟩ := hD τ ℓ u hR
  obtain ⟨e1', e2', e3'⟩ := hE τ ℓ u hR
  obtain ⟨f1, f2⟩ := hF τ ℓ u hR
  have hRs : Rsum τ ℓ u = ℓ * rho1 τ ℓ u + ℓ * rho2 τ ℓ u + ℓ * rho3 τ ℓ u +
      ℓ * rho4 τ ℓ u + ℓ * E3term τ ℓ u (paperCut τ ℓ) + ℓ * Tterm τ ℓ u := by
    unfold Rsum; ring
  set S := ℓ * max (sA ℓ u) 0
  have hS0 : 0 ≤ S := mul_nonneg hℓ0.le (le_max_right _ _)
  set p := ℓ ^ (-(1 / 8 : ℝ))
  -- the tail
  have hT : ℓ * Tterm τ ℓ u ≤ 0.035 * p * S + 1 / ℓ := by
    by_cases hc : Uf τ ℓ - u ≤ (Uf τ ℓ - u0 ℓ) / 2
    · have h := mul_le_mul_of_nonneg_left (f1 hc) hℓ0.le
      have : ℓ * (0.035 * p * sA ℓ u) ≤ 0.035 * p * S := by
        have h2 := mul_le_mul_of_nonneg_left (le_max_left (sA ℓ u) 0)
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 0.035) hp.le)
        have h3 := mul_le_mul_of_nonneg_left h2 hℓ0.le
        simp only [S]; linarith
      have : 0 ≤ 1 / ℓ := by positivity
      linarith
    · have := f2 hc
      have : 0 ≤ 0.035 * p * S := by positivity
      linarith
  refine ⟨fun h27 => ?_, fun h27 => ?_⟩
  · -- `u ≥ 27`
    have hX0 : 0 ≤ Xu u := by
      unfold Xu Kp; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u); positivity
    have hXc : Xu u ≤ cfun τ ℓ u := by
      have := c0_ge h27; unfold cfun Xu; linarith
    have hΦc : ℓ * PhiBen τ ℓ u ≤ cfun τ ℓ u := by
      have := c0_ge h27; unfold cfun at *
      have : 0 ≤ Xu u := hX0; unfold Xu at this; linarith
    have hρ3 : ℓ * rho3 τ ℓ u ≤ 0.72 * alphaL τ ℓ * Xu u := by
      by_cases h : u < u0 ℓ + 0.74
      · have := mul_le_mul_of_nonneg_left (c1 h) hℓ0.le
        have : 0 ≤ 0.72 * alphaL τ ℓ * Xu u := by positivity
        linarith
      · exact c2 (not_lt.mp h)
    have hlX := mul_le_mul_of_nonneg_left hXc hlam
    have haX := mul_le_mul_of_nonneg_left hXc hα
    have hlΦ := mul_le_mul_of_nonneg_left hΦc hlam
    have haΦ := mul_le_mul_of_nonneg_left hΦc hα
    have hlX0 := mul_nonneg hlam hX0
    have haX0 := mul_nonneg hα hX0
    have hd := d1 h27
    have ha := a2 h27
    rw [hRs]
    by_cases hbig : u0 ℓ - 2 ≤ u
    · rw [if_pos hbig]
      have hb := b1 h27 hbig
      have he := e1' h27 hbig
      -- `2.54 α'√ℓ ≤ 0.12 α' c`, from `c ≥ X ≥ 21.78 √ℓ`
      have hsq : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
      have hu2 : 0.99 * √ℓ ≤ u ^ 2 := by
        have hsq2 := u0_sq hℓ0.le
        nlinarith
      have hL : 10 ≤ Real.log (1 + u) := by
        rw [Real.le_log_iff_exp_le (by linarith)]; linarith [exp_ten_le]
      have hXs : 21.78 * √ℓ ≤ Xu u := by
        unfold Xu Kp; linarith [mul_le_mul hu2 hL (by norm_num) (sq_nonneg u)]
      have hsc : 2.54 * alphaL τ ℓ * √ℓ ≤ 0.12 * alphaL τ ℓ * cfun τ ℓ u := by
        have := mul_le_mul_of_nonneg_left (hXs.trans hXc) hα
        linarith [mul_nonneg hα hsq.le]
      linarith
    · rw [if_neg hbig]
      push_neg at hbig
      have hb := b2 h27 hbig
      have he := e2' h27 hbig
      have hαS := mul_nonneg hα hS0
      linarith
  · -- `u < 27`
    have hbig : u < u0 ℓ - 2 := by linarith
    have hΦc := ellPhiBen_le_c hτ hτℓ hℓ hu h27.le
    have hρ3 : ℓ * rho3 τ ℓ u ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (c1 (by linarith)) hℓ0.le
      linarith
    have hT' : ℓ * Tterm τ ℓ u ≤ 1 / ℓ := by
      by_cases hc : Uf τ ℓ - u ≤ (Uf τ ℓ - u0 ℓ) / 2
      · obtain ⟨-, hs0⟩ := (lemma57Slack τ ℓ u hR).2 hbig
        have h := mul_le_mul_of_nonneg_left (f1 hc) hℓ0.le
        have : ℓ * (0.035 * p * sA ℓ u) = 0.035 * p * (ℓ * sA ℓ u) := by ring
        have : 0.035 * p * (ℓ * sA ℓ u) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hs0
        have : 0 ≤ 1 / ℓ := by positivity
        linarith
      · exact f2 hc
    have hE0 := exp_neg_u0_le hℓ
    have hlΦ := mul_le_mul_of_nonneg_left hΦc hlam
    have haΦ := mul_le_mul_of_nonneg_left hΦc hα
    have hc0 : 0 ≤ cfun τ ℓ u := by linarith [cfun_ge_small hτ hτℓ hℓ hu h27.le]
    have hb := b3 h27
    have hd := d2 h27
    have he := e3' h27
    have hinv : 0 < ℓ⁻¹ := inv_pos.mpr hℓ0
    have hlc := mul_nonneg hlam hc0
    have hac := mul_nonneg hα hc0
    simp only [div_eq_mul_inv, one_mul] at hb hd he hE0 hT' ⊢
    rw [hRs]
    linarith

/-- **Step 7(ii) of the proof of Theorem 5.6** from the six remainder bounds of Lemma 5.7. -/
theorem regionLarge_of_six (hA : RemA) (hB : RemB) (hC : RemC) (hD : RemD) (hE : RemE)
    (hF : RemF) : RegionLarge :=
  regionLarge_of_lemma57 (lemma57Ineq_of_remC (remC_of_six hA hB hC hD hE hF))
    lemma57Eps lemma57Slack

end BSaias.Large

end
