module

public import RequestProject.Beurling.Noise.BSLargeEpsCert

/-!
# Lemma 5.7: `ε(ℓ) ≤ 0.03` (`lemma57Eps`)

`ε` is non-increasing in `τ` (through `U(ℓ)`), so `ε(ℓ) ≤ ε̄(ℓ)`, its value at `τ = 10⁸`
(`epsL_le_epsBar`). On `[10¹⁸, 10³⁰]`, `ε̄ < 0.03` by the interval cover (`epsBar_lt_cert`); for
`ℓ ≥ 10³⁰` an analytic bound in `q = ℓ^{1/8} ≥ 5000` gives `ε̄ ≤ 10⁻⁴ + 30/q + 1/q`
(`epsBar_le_large`).
-/

@[expose] public section

open Real

namespace BSaias.Large

lemma rpow_neg_eighth {ℓ : ℝ} (hℓ : 0 < ℓ) : ℓ ^ (-(1 / 8 : ℝ)) = 1 / √(u0 ℓ) := by
  show ℓ ^ (-(1 / 8 : ℝ)) = 1 / √(√(√ℓ))
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hℓ.le,
    ← Real.rpow_mul hℓ.le, Real.rpow_neg hℓ.le, one_div]
  norm_num

/-- `ε(ℓ) ≤ ε̄(ℓ)` for `τ ≥ 10⁸`, `ℓ ≥ 10⁸`. -/
lemma epsL_le_epsBar {τ ℓ : ℝ} (hτ : 100000000 ≤ τ) (hℓ : 100000000 ≤ ℓ) :
    epsL τ ℓ ≤ epsBar ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hτ0 : 0 < τ := by linarith
  have hu0 : 0 ≤ u0 ℓ := Real.sqrt_nonneg _
  set σ := √(2 * Real.log (ℓ / τ) + 4)
  set σb := √(2 * Real.log (ℓ / 100000000) + 4)
  have hσ : σ ≤ σb := by
    apply Real.sqrt_le_sqrt
    have : Real.log (ℓ / τ) ≤ Real.log (ℓ / 100000000) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hℓ0.le (by norm_num) hτ)
    linarith
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hU : Uf τ ℓ = u0 ℓ + u0 ℓ * σ := rfl
  have hUb : BSCert.Z2.Ubar ℓ = u0 ℓ + u0 ℓ * σb := rfl
  have hUU : Uf τ ℓ ≤ BSCert.Z2.Ubar ℓ := by
    rw [hU, hUb]; nlinarith [mul_le_mul_of_nonneg_left hσ hu0]
  have hU0 : 0 ≤ Uf τ ℓ := by rw [hU]; positivity
  have hlog : Real.log (2 + Uf τ ℓ) ≤ Real.log (2 + BSCert.Z2.Ubar ℓ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (2 + Uf τ ℓ) := Real.log_nonneg (by linarith)
  have t1 : 20000 * Uf τ ℓ ^ 2 * Real.log (2 + Uf τ ℓ) / ℓ ≤
      20000 * BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ * Real.log (2 + BSCert.Z2.Ubar ℓ) / ℓ := by
    apply div_le_div_of_nonneg_right _ hℓ0.le
    have := mul_le_mul (pow_le_pow_left₀ hU0 hUU 2) hlog hlog0 (by positivity)
    nlinarith
  have t2 : 30 * aprime ℓ (Uf τ ℓ) ≤ 30 * BSCert.Z2.UbMu0 ℓ / √ℓ := by
    have hm : u0 ℓ * σ ≤ BSCert.Z2.UbMu0 ℓ := mul_le_mul_of_nonneg_left hσ hu0
    have hd := div_le_div_of_nonneg_right hm (Real.sqrt_nonneg ℓ)
    unfold aprime
    rw [hU, show u0 ℓ + u0 ℓ * σ - u0 ℓ = u0 ℓ * σ by ring, max_eq_left (by positivity)]
    have e : 30 * BSCert.Z2.UbMu0 ℓ / √ℓ = 30 * (BSCert.Z2.UbMu0 ℓ / √ℓ) := mul_div_assoc _ _ _
    rw [e]
    linarith
  unfold epsL epsBar
  rw [rpow_neg_eighth hℓ0]
  linarith

/-- For `ℓ ≥ 10³⁰`: `ε̄(ℓ) < 0.03`. -/
lemma epsBar_le_large {ℓ : ℝ} (hℓ : 1000000000000000000000000000000 ≤ ℓ) :
    epsBar ℓ < 3 / 100 := by
  have hℓ0 : 0 < ℓ := by linarith
  set u := u0 ℓ with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  set q := √u with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqu : q ^ 2 = u := Real.sq_sqrt hu0
  have hus : u ^ 2 = √ℓ := Real.sq_sqrt (Real.sqrt_nonneg ℓ)
  have hsl : √ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hsl4 : √ℓ = q ^ 4 := by rw [← hus, ← hqu]; ring
  have hl8 : ℓ = q ^ 8 := by rw [← hsl, hsl4]; ring
  have hq5 : 5000 ≤ q := by
    by_contra h; push_neg at h
    have : q ^ 8 < 5000 ^ 8 := pow_lt_pow_left₀ h hq0 (by norm_num)
    rw [← hl8] at this; norm_num at this; linarith
  set p := √q with hp
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hpq : p ^ 2 = q := Real.sq_sqrt hq0
  have hp70 : 70 ≤ p := by nlinarith
  have hq0' : 0 < q := by linarith
  -- `log q ≤ 2p`
  have hlq : Real.log q ≤ 2 * p := by
    have h := Real.log_le_sub_one_of_pos (show 0 < p by linarith)
    have e : Real.log q = 2 * Real.log p := by rw [← hpq, Real.log_pow]; norm_num
    linarith
  have hlogℓ : Real.log (ℓ / 100000000) ≤ 16 * p := by
    have h1 : Real.log (ℓ / 100000000) ≤ Real.log ℓ :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log ℓ = 8 * Real.log q := by rw [hl8, Real.log_pow]; norm_num
    linarith
  have hlpos : 0 ≤ 2 * Real.log (ℓ / 100000000) + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ℓ / 100000000 by
      rw [le_div_iff₀ (by norm_num)]; linarith)
    linarith
  set σ := √(2 * Real.log (ℓ / 100000000) + 4) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 ≤ 33 * p := by rw [Real.sq_sqrt hlpos]; linarith
  have hσq : σ ≤ q := by
    have : σ ^ 2 ≤ q ^ 2 := by rw [← hpq]; nlinarith
    exact (pow_le_pow_iff_left₀ hσ0 hq0 (by norm_num)).mp this
  have hUb : BSCert.Z2.Ubar ℓ = u + u * σ := rfl
  have hUm : BSCert.Z2.UbMu0 ℓ = u * σ := rfl
  -- term 1
  have h1σ : (1 + σ) ^ 2 ≤ 67 * p := by nlinarith
  have hUle : 2 + BSCert.Z2.Ubar ℓ ≤ q ^ 4 := by
    rw [hUb, ← hqu]
    nlinarith [mul_le_mul_of_nonneg_left hσq (sq_nonneg q), pow_le_pow_left₀ (by norm_num) hq5 3]
  have hlogU : Real.log (2 + BSCert.Z2.Ubar ℓ) ≤ 8 * p := by
    have h := Real.log_le_log (by rw [hUb]; positivity) hUle
    rw [Real.log_pow] at h; push_cast at h; linarith
  have hlogU0 : 0 ≤ Real.log (2 + BSCert.Z2.Ubar ℓ) := Real.log_nonneg (by rw [hUb]; nlinarith)
  have hT1 : 20000 * BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ * Real.log (2 + BSCert.Z2.Ubar ℓ) / ℓ
      ≤ 1 / 10000 := by
    rw [div_le_div_iff₀ hℓ0 (by norm_num)]
    have hU2 : BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ = q ^ 4 * (1 + σ) ^ 2 := by
      rw [hUb, ← hqu]; ring
    have : 20000 * BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ * Real.log (2 + BSCert.Z2.Ubar ℓ) ≤
        20000 * (q ^ 4 * (67 * p)) * (8 * p) := by
      rw [mul_assoc 20000, hU2]
      apply mul_le_mul _ hlogU hlogU0 (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1σ (by positivity)) (by norm_num)
    have e : 20000 * (q ^ 4 * (67 * p)) * (8 * p) = 10720000 * q ^ 5 := by rw [← hpq]; ring
    rw [e] at this
    have hq3 : (125000000000 : ℝ) ≤ q ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hq5 3; norm_num at this; linarith
    have hq5p : 0 ≤ q ^ 5 := by positivity
    calc 20000 * BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ * Real.log (2 + BSCert.Z2.Ubar ℓ) * 10000
        ≤ 10720000 * q ^ 5 * 10000 := by linarith
      _ ≤ q ^ 3 * q ^ 5 := by
          have := mul_le_mul_of_nonneg_right (by linarith : (107200000000 : ℝ) ≤ q ^ 3) hq5p
          linarith
      _ = 1 * ℓ := by rw [hl8]; ring
  have hT2 : 30 * BSCert.Z2.UbMu0 ℓ / √ℓ ≤ 30 / q := by
    rw [hUm, hsl4, ← hqu, div_le_div_iff₀ (by positivity) hq0']
    have := mul_le_mul_of_nonneg_left hσq (pow_nonneg hq0 3)
    calc 30 * (q ^ 2 * σ) * q = 30 * (q ^ 3 * σ) := by ring
      _ ≤ 30 * (q ^ 3 * q) := by linarith
      _ = 30 * q ^ 4 := by ring
  have hT3 : 1 / √u = 1 / q := rfl
  have hq30 : 30 / q ≤ 30 / 5000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq5
  have hq1 : 1 / q ≤ 1 / 5000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq5
  unfold epsBar
  rw [← hu, hT3]
  linarith

/-- **Lemma 5.7, `ε(ℓ) ≤ 0.03`.** -/
theorem lemma57Eps : Lemma57Eps := by
  intro τ ℓ hτ _ hℓ
  refine (epsL_le_epsBar hτ (by linarith)).trans ?_
  rcases le_or_gt ℓ 1000000000000000000000000000000 with h | h
  · have := epsBar_lt_cert hℓ h; linarith
  · have := epsBar_le_large h.le; linarith

end BSaias.Large

end
