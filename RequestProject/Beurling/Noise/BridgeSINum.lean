module

public import RequestProject.Beurling.Noise.BridgeRankin
public import RequestProject.Beurling.Noise.BridgeSIBlocks
public import RequestProject.Beurling.Noise.BSL57Final

/-!
# Lemma 5.32: the bound for one block, and the numerical facts

* `block_term_le` : for a block `(M_k, 2M_k]` with `log M_k ≥ max(τ, 10³⁴)`,
  `W_t(M_k; 2N/M_k)/σ_k ≤ 1.002 · 38.3 · τ ρ(u_k - 1)/(ℓ_k σ_k) + e^{14}(log z_k) e^{-ℓ_k^{1/4}}`
  (`z_k = 2N/M_k`): Lemma 5.8 if `u_k ≤ ℓ_k^{1/4}` (there `a = 0` and `A ≤ 0.0019`), and the
  Rankin bound (Lemma 5.30) if `u_k > ℓ_k^{1/4}`, which covers Region 2 of the paper and the part
  `ℓ^{1/4} < u ≤ U(ℓ)` of Region 1;
* `log_ratio_le` : `log((1+y)/(1-y)) ≤ 2.1 y` for `0 ≤ y ≤ 1/6`;
* `partB_small` : part (B) is `≤ 0.01 ητ/J`;
* `tail_small` : the Rankin terms are negligible.
-/

@[expose] public section

open Real Finset

namespace BridgeSI

/-- `A(ℓ, u) ≤ 0.0019` for `ℓ ≥ 10³⁴` and `0 ≤ u ≤ ℓ^{1/4}`. -/
lemma A_small {ℓ u : ℝ} (hℓ : 10000000000000000000000000000000000 ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.u0 ℓ) : BSCert.Z2.A ℓ u ≤ 0.0019 := by
  set s := BSaias.u0 ℓ with hsdef
  have hℓ0 : 0 < ℓ := by linarith
  have hs4 : s ^ 4 = ℓ := by
    rw [hsdef, BSaias.u0, BSCert.Z2.u0, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hℓ0.le]
  have hs0 : 0 ≤ s := by rw [hsdef, BSaias.u0, BSCert.Z2.u0]; positivity
  have hs : 300000000 ≤ s := by
    by_contra hc; push_neg at hc
    have : s ^ 4 < 300000000 ^ 4 := pow_lt_pow_left₀ hc hs0 (by norm_num)
    rw [hs4] at this; norm_num at this; linarith
  have hss : 17000 ≤ √s := by rw [Real.le_sqrt (by norm_num) hs0]; nlinarith
  unfold BSCert.Z2.A
  rw [div_le_iff₀ hℓ0]
  have hlog : Real.log (2 + u) ≤ 2 * √(2 + s) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < √(2 + u) by positivity)
    have h2 : Real.log (2 + u) = 2 * Real.log √(2 + u) := by
      rw [← Real.log_rpow (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
      norm_num
    have h3 : √(2 + u) ≤ √(2 + s) := Real.sqrt_le_sqrt (by linarith)
    linarith
  have h2s : √(2 + s) ≤ 1.001 * √s := by
    rw [show (1.001 : ℝ) * √s = √(1.001 ^ 2 * s) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcube : (1 + u) ^ 3 ≤ 1.001 * s ^ 3 := by
    have : (1 + u) ^ 3 ≤ (1 + s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h1 : 4000 * s ^ 2 ≤ s ^ 3 := by
      have := mul_le_mul_of_nonneg_left (show (4000 : ℝ) ≤ s by linarith) (sq_nonneg s)
      nlinarith
    have h2 : 3 * s + 1 ≤ s ^ 2 := by nlinarith
    nlinarith
  have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hss0 : 0 ≤ √s := Real.sqrt_nonneg s
  have hsq : √s * √s = s := Real.mul_self_sqrt hs0
  calc 11 * (1 + u) ^ 3 * Real.log (2 + u) ≤ 11 * (1.001 * s ^ 3) * (2 * (1.001 * √s)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hcube (by norm_num)) (hlog.trans
          (by linarith)) hl0 (by positivity)
    _ ≤ 0.0019 * ℓ := by
        rw [← hs4]
        have : s ^ 3 * √s * 17000 ≤ s ^ 3 * √s * √s :=
          mul_le_mul_of_nonneg_left hss (by positivity)
        have e : s ^ 3 * √s * √s = s ^ 4 := by rw [mul_assoc, hsq]; ring
        nlinarith

/-- `log((1+y)/(1-y)) ≤ 2.1 y` for `0 ≤ y ≤ 1/6`. -/
lemma log_ratio_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 6) :
    Real.log ((1 + y) / (1 - y)) ≤ 2.1 * y := by
  rw [Real.log_div (by linarith) (by linarith)]
  have ha := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith)
  have hb := LemS.neg_log_one_sub_le h0 (by linarith)
  have hc : y ^ 2 / (2 * (1 - y)) ≤ 0.1 * y := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

variable {P : BeurlingSystem}

set_option maxHeartbeats 1000000 in
/-- **One block of Lemma 5.32 (A).** -/
theorem block_term_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {t N Mk : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hMk : 1 ≤ Mk) (hℓτ : Real.log t ≤ Real.log Mk)
    (hℓ : 10000000000000000000000000000000000 ≤ Real.log Mk) (hMkZ : 2 * Mk ≤ Z)
    (hz10 : Real.exp 10 ≤ 2 * N / Mk) (hzZ : 2 * N / Mk ≤ Z)
    (hσ : 1 ≤ Real.log (N / (2 * Mk))) :
    P.Wsm t Mk (BeurlingSystem.SIu N Mk) / Real.log (N / (2 * Mk)) ≤
      1.002 * 38.3 * Real.log t * Dickman.rho (BeurlingSystem.SIu N Mk - 1) /
          (Real.log Mk * Real.log (N / (2 * Mk))) +
        Real.exp 14 * Real.log (2 * N / Mk) * Real.exp (-BSaias.u0 (Real.log Mk)) := by
  set ℓ := Real.log Mk with hℓdef
  set σ := Real.log (N / (2 * Mk)) with hσdef
  set z := 2 * N / Mk with hzdef
  set u := BeurlingSystem.SIu N Mk with hudef
  have hMk0 : 0 < Mk := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hz1 : 1 < z := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hz10
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have hu : u = ℓ / Real.log z := rfl
  have hu0 : 0 < u := by rw [hu]; positivity
  have hMke : Mk = Real.exp ℓ := (Real.exp_log hMk0).symm
  have hrest : 0 ≤ Real.exp 14 * Real.log z * Real.exp (-BSaias.u0 ℓ) := by positivity
  have hmain0 : 0 ≤ 1.002 * 38.3 * Real.log t * Dickman.rho (u - 1) / (ℓ * σ) := by
    have := Dickman.rho_pos (u - 1); positivity
  rcases le_or_gt u (BSaias.u0 ℓ) with hsm | hbig
  · -- Lemma 5.8
    have hUf : u ≤ BSaias.Uf (Real.log t) ℓ := by
      unfold BSaias.Uf
      have : 0 ≤ BSaias.u0 ℓ * √(2 * Real.log (ℓ / Real.log t) + 4) := by
        unfold BSaias.u0 BSCert.Z2.u0; positivity
      linarith
    have h58 := P.lemma_5_8_full h ht hτ hℓτ hu0.le hUf (by rw [← hMke]; exact hMkZ)
    rw [← hMke] at h58
    have hQ : BSaias.Qf ℓ u ≤ 0.0019 := by
      unfold BSaias.Qf BSaias.aQ
      rw [max_eq_right (by linarith), show (0 : ℝ) ^ 2 / (2 * √ℓ) = 0 by simp, add_zero]
      exact A_small hℓ hu0.le hsm
    have hexpQ : Real.exp (BSaias.Qf ℓ u) ≤ 1.002 := by
      refine (Real.exp_le_exp.mpr hQ).trans ?_
      have := Real.exp_bound' (x := (0.0019 : ℝ)) (by norm_num) (by norm_num) (n := 2)
        (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have hPhi := BSaias.PhiInf_le hτ
    have hPhi0 : 0 ≤ BSaias.PhiInf (Real.log t) := by
      unfold BSaias.PhiInf BSaias.C0; positivity
    have hτ0 : 0 < Real.log t := by linarith
    have hρ := Dickman.rho_pos (u - 1)
    have hW : P.Wsm t Mk u ≤ 1.002 * 38.3 * Real.log t * Dickman.rho (u - 1) / ℓ := by
      refine h58.trans ?_
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right
        hℓ0]
      have h1 : BSaias.PhiInf (Real.log t) * Real.exp (BSaias.Qf ℓ u) ≤ 38.3 * 1.002 :=
        mul_le_mul hPhi hexpQ (Real.exp_pos _).le (by norm_num)
      have h2 : 0 ≤ Real.log t * Dickman.rho (u - 1) := by positivity
      nlinarith
    calc P.Wsm t Mk u / σ ≤ 1.002 * 38.3 * Real.log t * Dickman.rho (u - 1) / ℓ / σ :=
          div_le_div_of_nonneg_right hW hσ0.le
      _ = 1.002 * 38.3 * Real.log t * Dickman.rho (u - 1) / (ℓ * σ) := by rw [div_div]
      _ ≤ _ := le_add_of_nonneg_right hrest
  · -- the Rankin bound
    have hWv : P.Wsm t Mk u ≤ P.vSmooth Mk z := by
      have := P.Wsm_le_vSmooth (t := t) (ℓ := ℓ) hu0
      rw [← hMke] at this
      have e : Real.exp (ℓ / u) = z := by
        have : ℓ / u = Real.log z := by rw [hu]; field_simp
        rw [this, Real.exp_log (by linarith)]
      rwa [e] at this
    have hR := BeurlingSystem.HBS.rankin_crude h (ℓ := ℓ) hz10 hzZ
    rw [← hMke] at hR
    have hR' : P.vSmooth Mk z ≤ Real.exp 14 * Real.log z * Real.exp (-BSaias.u0 ℓ) := by
      refine hR.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [← hu]; linarith
    calc P.Wsm t Mk u / σ ≤ P.Wsm t Mk u := by
          rw [div_le_iff₀ hσ0]
          have : 0 ≤ P.Wsm t Mk u := by
            unfold BeurlingSystem.Wsm
            exact Finset.sum_nonneg fun e _ => div_nonneg zero_le_one (P.val_pos e).le
          nlinarith
      _ ≤ Real.exp 14 * Real.log z * Real.exp (-BSaias.u0 ℓ) := hWv.trans hR'
      _ ≤ _ := le_add_of_nonneg_left hmain0

/-- `log x ≤ 0.0002 x` for `x ≥ 10⁸` (as in `BridgeSIPrime`). -/
lemma log_le_small' {x : ℝ} (hx : 100000000 ≤ x) : Real.log x ≤ 0.0002 * x := by
  have hx0 : 0 < x := by linarith
  have hs : 10000 ≤ √x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  have h1 : Real.log x = 2 * Real.log √x := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr hx0), Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have h2 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3 : √x * √x = x := Real.mul_self_sqrt hx0.le
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Part (B) is negligible**: `2 e^{14} Λ₁ e^{-(J - log 2)/Λ₁} ≤ 0.01 ητ/J` for `Λ ≥ 10⁸`,
`Λ₁ = 100Λ³`, `J ≥ 300Λ⁴`, `η ≥ e^{-2Λ}`, `τ ≥ Λ`. -/
lemma partB_small {Λ J η τ : ℝ} (hΛ : 100000000 ≤ Λ) (hJ : 300 * Λ ^ 4 ≤ J)
    (hη : Real.exp (-(2 * Λ)) ≤ η) (hτ : Λ ≤ τ) :
    2 * Real.exp 14 * (100 * Λ ^ 3) * Real.exp (-((J - Real.log 2) / (100 * Λ ^ 3))) ≤
      0.01 * η * τ / J := by
  have hΛ0 : 0 < Λ := by linarith
  set L1 := 100 * Λ ^ 3 with hL1
  have hL10 : 0 < L1 := by positivity
  have hJ0 : 0 < J := lt_of_lt_of_le (by positivity) hJ
  set x := J / L1 with hx
  have hx3 : 3 * Λ ≤ x := by
    rw [hx, le_div_iff₀ hL10, hL1]; nlinarith
  have hJx : J = L1 * x := by rw [hx]; field_simp
  have hlogJ : Real.log J = Real.log L1 + Real.log x := by
    rw [hJx, Real.log_mul hL10.ne' (by positivity)]
  have hlx := log_le_small' (show 100000000 ≤ x by nlinarith)
  have hlL1 : Real.log L1 = Real.log 100 + 3 * Real.log Λ := by
    rw [hL1, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hlΛ := log_le_small' hΛ
  have hl100 : Real.log 100 ≤ 4.7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h3 := Real.exp_one_gt_d9
    have e : Real.exp 4.7 = Real.exp 1 ^ 4 * Real.exp 0.7 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h3.le 4
    have h5 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7 by norm_num)
    rw [e]; nlinarith [Real.exp_pos 0.7]
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog01 : Real.log 0.01 ≥ -5 := by
    rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num)]
    have : Real.exp (-5) = (Real.exp 5)⁻¹ := Real.exp_neg 5
    rw [this, inv_le_comm₀ (Real.exp_pos 5) (by norm_num)]
    have h3 := Real.exp_one_gt_d9
    have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h3.le 5
    rw [e]; norm_num at h4 ⊢; linarith
  have hlΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  -- logarithmic comparison
  have hL : Real.log (2 * Real.exp 14 * L1 * J) - (J - Real.log 2) / L1 ≤
      Real.log (0.01 * Λ) - 2 * Λ := by
    rw [Real.log_mul (by positivity) hJ0.ne', Real.log_mul (by positivity) hL10.ne',
      Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (by norm_num) hΛ0.ne', hlogJ]
    have e : (J - Real.log 2) / L1 = x - Real.log 2 / L1 := by rw [hx]; ring
    rw [e]
    have : 0 ≤ Real.log 2 / L1 := div_nonneg hl2' hL10.le
    have hΛ3 : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have : Real.log 2 / L1 ≤ 1 := by rw [div_le_one hL10, hL1]; nlinarith
    linarith
  have hA : 2 * Real.exp 14 * L1 * J * Real.exp (-((J - Real.log 2) / L1)) ≤
      0.01 * Λ * Real.exp (-(2 * Λ)) := by
    rw [← Real.exp_log (show 0 < 2 * Real.exp 14 * L1 * J by positivity),
      ← Real.exp_log (show 0 < 0.01 * Λ by positivity), ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [le_div_iff₀ hJ0]
  have hητ : 0.01 * Λ * Real.exp (-(2 * Λ)) ≤ 0.01 * η * τ := by
    have := mul_le_mul hη hτ hΛ0.le (by linarith [Real.exp_pos (-(2 * Λ))])
    nlinarith
  nlinarith

/-- **The Rankin terms are negligible**: for `s ≥ 3·10⁸`,
`2.2002 e^{14} J²(J+1) e^{-s} ≤ 0.01` whenever `J ≤ s⁴/0.449`. -/
lemma tail_small {s J : ℝ} (hs : 300000000 ≤ s) (hJ0 : 0 ≤ J) (hJ : J ≤ s ^ 4 / 0.449) :
    2.2002 * Real.exp 14 * (J ^ 2 * (J + 1)) * Real.exp (-s) ≤ 0.01 := by
  have hs0 : 0 < s := by linarith
  have h20 := Real.pow_div_factorial_le_exp (x := s) hs0.le 20
  have hJ3 : J ^ 2 * (J + 1) ≤ 23 * s ^ 12 := by
    have hJ' : J ≤ 2.23 * s ^ 4 := by
      refine hJ.trans ?_
      rw [div_le_iff₀ (by norm_num)]; nlinarith [pow_pos hs0 4]
    have h1 : J + 1 ≤ 2.24 * s ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hs 4]
    have h2 : J ^ 2 ≤ (2.23 * s ^ 4) ^ 2 := pow_le_pow_left₀ hJ0 hJ' 2
    calc J ^ 2 * (J + 1) ≤ (2.23 * s ^ 4) ^ 2 * (2.24 * s ^ 4) :=
          mul_le_mul h2 h1 (by linarith) (by positivity)
      _ ≤ 23 * s ^ 12 := by ring_nf; nlinarith [pow_pos hs0 12]
  have he14 : Real.exp 14 ≤ 1300000 := by
    have h1 := Real.exp_one_lt_d9
    have e : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 14
    norm_num at this; linarith
  have hes : Real.exp (-s) ≤ (Nat.factorial 20 : ℝ) / s ^ 20 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h20
    nlinarith
  have hfac : (Nat.factorial 20 : ℝ) ≤ 2500000000000000000 := by
    norm_num [Nat.factorial]
  have hs8 : (300000000 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs 8
  calc 2.2002 * Real.exp 14 * (J ^ 2 * (J + 1)) * Real.exp (-s)
      ≤ 2.2002 * 1300000 * (23 * s ^ 12) * ((Nat.factorial 20 : ℝ) / s ^ 20) := by
        gcongr
    _ = 2.2002 * 1300000 * 23 * (Nat.factorial 20 : ℝ) / s ^ 8 := by
        field_simp
    _ ≤ 0.01 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end BridgeSI

end
