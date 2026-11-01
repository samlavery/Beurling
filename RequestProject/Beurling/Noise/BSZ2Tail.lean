module

public import RequestProject.Beurling.Noise.BSZ2Pointwise
public import RequestProject.Beurling.Noise.BSZ2Integrable

/-!
# The tail of Step 6 in region Z2: `T ≤ exp(κ_max/ℓ + a_V(Ū + 1/2) + E_T)`

Proof of Theorem 5.6, Step 6, as used in Step 7(iii). With `y = log(ℓ/τ) ≥ log 30` and
`r₀ = r(u-1) ≥ 1`:

* `G(ℓ, u) ≥ C₀ e^{-κ_Φ/ℓ} ρ(u-1) e^{a(ℓ,u)}` (`Φ_∞ ≥ C₀`, `Q ≥ a`);
* `ρ(u*)/ρ(u-1) ≤ e^{-r₀(u* - u + 1)}` ((R3), `Dickman.rho_le_exp`), `u* = U(ℓ) + 1/2`;
* so `T ≤ exp(κ_Φ/ℓ + a_V(u*) + y - a(ℓ,u) - r₀(U(ℓ) - u + 3/2))`;
* `κ_Φ ≤ κ_max` and `a_V(u*) ≤ a_V(Ū + 1/2)` (`U(ℓ) ≤ Ū(ℓ)` for `τ ≥ 10⁸`);
* the maximisation over `y`: for `u ≤ U₃₀`, `y - log 30 ≤ r₀ (U(ℓ) - U₃₀)` (as
  `√(2y+4) ≤ u₀`); for `u > U₃₀`, `a(ℓ, U(ℓ)) = y + 2` and `a(ℓ, U) - a(ℓ, u) ≤ r₀ (U - u)`.

Main result: `Tterm_le` : `Tterm τ ℓ u ≤ BSCert.Z2.T Dickman.ratio ℓ u`.
-/

@[expose] public section

open Real Set

namespace BSaias

/-- `U(ℓ; τ) ≤ Ū(ℓ) = U(ℓ; 10⁸)` for `τ ≥ 10⁸`. -/
lemma Uf_le_Ubar {τ ℓ : ℝ} (hτ : 100000000 ≤ τ) (hℓ : 0 < ℓ) : Uf τ ℓ ≤ BSCert.Z2.Ubar ℓ := by
  unfold Uf BSCert.Z2.Ubar BSCert.Z2.UbMu0
  have h1 : Real.log (ℓ / τ) ≤ Real.log (ℓ / 100000000) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hℓ.le (by norm_num) hτ)
  have h2 : √(2 * Real.log (ℓ / τ) + 4) ≤ √(2 * Real.log (ℓ / 100000000) + 4) :=
    Real.sqrt_le_sqrt (by linarith)
  have := mul_le_mul_of_nonneg_left h2 (u0_pos hℓ).le
  simp only [u0] at this ⊢
  linarith

lemma ratio_ge_one {u : ℝ} (hu : 2 ≤ u) : 1 ≤ Dickman.ratio (u - 1) :=
  BSCert.dickmanRatioFacts.one_le (by linarith)

/-- `2 log ℓ + 4 ≤ √ℓ` for `ℓ ≥ 8⁴`, so `√(2 log(ℓ/τ) + 4) ≤ u₀` for `τ ≥ 1`. -/
lemma sqrt_y_le_u0 {τ ℓ : ℝ} (hτ : 1 ≤ τ) (hℓ : 4096 ≤ ℓ) :
    √(2 * Real.log (ℓ / τ) + 4) ≤ u0 ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hu8 : 8 ≤ u0 ℓ := by
    have : u0 4096 = 8 := by
      show √(√4096) = 8
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
        show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact u0_mono hℓ
  have hlog : Real.log ℓ = 4 * Real.log (u0 ℓ) := by
    conv_lhs => rw [← u0_pow_four hℓ0.le]
    rw [Real.log_pow]; norm_num
  have hl1 : Real.log (u0 ℓ) ≤ u0 ℓ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hy : Real.log (ℓ / τ) ≤ Real.log ℓ := by
    rw [Real.log_div hℓ0.ne' (by linarith)]
    have := Real.log_nonneg hτ; linarith
  have hsq : 2 * Real.log (ℓ / τ) + 4 ≤ u0 ℓ ^ 2 := by nlinarith
  calc √(2 * Real.log (ℓ / τ) + 4) ≤ √(u0 ℓ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = u0 ℓ := Real.sqrt_sq (by linarith)

/-- `a(ℓ, U(ℓ)) = log(ℓ/τ) + 2` when `log(ℓ/τ) ≥ -2`. -/
lemma aQ_Uf {τ ℓ : ℝ} (hℓ : 0 < ℓ) (hy : -2 ≤ Real.log (ℓ / τ)) :
    aQ ℓ (Uf τ ℓ) = Real.log (ℓ / τ) + 2 := by
  unfold aQ Uf
  have e : u0 ℓ + u0 ℓ * √(2 * Real.log (ℓ / τ) + 4) - u0 ℓ =
      u0 ℓ * √(2 * Real.log (ℓ / τ) + 4) := by ring
  rw [e, max_eq_left (mul_nonneg (u0_pos hℓ).le (Real.sqrt_nonneg _)), mul_pow, u0_sq,
    Real.sq_sqrt (by linarith)]
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  field_simp
  ring

/-- The exponent bound: `y - a(ℓ,u) - r₀(U(ℓ) - u + 3/2) ≤ E_T`. -/
lemma exponent_le_ET {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓτ : 30 * τ < ℓ) (hℓ : 4096 ≤ ℓ) (hu : 2 ≤ u)
    (huU : u ≤ Uf τ ℓ) :
    Real.log (ℓ / τ) - aQ ℓ u - Dickman.ratio (u - 1) * (Uf τ ℓ - u + 3 / 2) ≤
      BSCert.Z2.ET Dickman.ratio ℓ u := by
  have hℓ0 : 0 < ℓ := by linarith
  have hτ0 : 0 < τ := by linarith
  set r0 := Dickman.ratio (u - 1)
  have hr0 : 1 ≤ r0 := ratio_ge_one hu
  set y := Real.log (ℓ / τ) with hydef
  have hy30 : Real.log 30 ≤ y := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hτ0]; linarith
  have hl30 : 0 < Real.log 30 := Real.log_pos (by norm_num)
  set s1 := √(2 * y + 4) with hs1
  set s0 := √(2 * Real.log 30 + 4) with hs0
  have hs01 : s0 ≤ s1 := Real.sqrt_le_sqrt (by linarith)
  have hs1u : s1 ≤ u0 ℓ := sqrt_y_le_u0 hτ hℓ
  have hs0n : 0 ≤ s0 := Real.sqrt_nonneg _
  have hU : Uf τ ℓ = u0 ℓ + u0 ℓ * s1 := rfl
  unfold BSCert.Z2.ET
  split_ifs with hg
  · -- `u ≤ U₃₀`
    unfold BSCert.Z2.gap at hg ⊢
    rw [max_eq_left hg]
    simp only [← hs0]
    have haQ : (max (u - BSCert.Z2.u0 ℓ) 0) ^ 2 / (2 * √ℓ) = aQ ℓ u := rfl
    rw [haQ]
    -- `y - log 30 ≤ u₀ (s1 - s0) ≤ r₀ (U - U₃₀)`
    have hsq1 : s1 ^ 2 = 2 * y + 4 := Real.sq_sqrt (by linarith)
    have hsq0 : s0 ^ 2 = 2 * Real.log 30 + 4 := Real.sq_sqrt (by linarith)
    have hkey : y - Real.log 30 ≤ u0 ℓ * (s1 - s0) := by
      have : y - Real.log 30 = (s1 - s0) * (s1 + s0) / 2 := by nlinarith
      rw [this]
      have h1 : (s1 + s0) / 2 ≤ u0 ℓ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hs01)]
    have hU0 : 0 ≤ u0 ℓ * (s1 - s0) := mul_nonneg (u0_pos hℓ0).le (by linarith)
    have hk2 : u0 ℓ * (s1 - s0) ≤ r0 * (u0 ℓ * (s1 - s0)) := by nlinarith
    have : Uf τ ℓ - u + 3 / 2 = (u0 ℓ * s0 - (u - BSCert.Z2.u0 ℓ) + 1.5) +
        u0 ℓ * (s1 - s0) := by rw [hU]; simp only [u0]; ring
    rw [this]
    nlinarith
  · -- `u > U₃₀`: use `a(ℓ, U) = y + 2`
    have haU := aQ_Uf (τ := τ) hℓ0 (by linarith)
    rw [← hydef] at haU
    have hdiff := (sq_pos_part_sub (u0 ℓ) u (Uf τ ℓ) huU).1
    have hmax : max (Uf τ ℓ - u0 ℓ) 0 = u0 ℓ * s1 := by
      rw [hU, show u0 ℓ + u0 ℓ * s1 - u0 ℓ = u0 ℓ * s1 by ring]
      exact max_eq_left (mul_nonneg (u0_pos hℓ0).le (Real.sqrt_nonneg _))
    rw [hmax] at hdiff
    have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
    have hsl : √ℓ = u0 ℓ ^ 2 := (u0_sq ℓ).symm
    have hu0 := u0_pos hℓ0
    -- `a(ℓ, U) - a(ℓ, u) ≤ (s1/u₀)(U - u) ≤ U - u`
    have hda : aQ ℓ (Uf τ ℓ) - aQ ℓ u ≤ Uf τ ℓ - u := by
      unfold aQ
      rw [hmax, ← sub_div, div_le_iff₀ (by positivity)]
      have h2 : 2 * (u0 ℓ * s1) * (Uf τ ℓ - u) ≤ (Uf τ ℓ - u) * (2 * √ℓ) := by
        rw [hsl]
        have : u0 ℓ * s1 ≤ u0 ℓ ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.mpr huU)]
      linarith
    have hUu : 0 ≤ Uf τ ℓ - u := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hr0 hUu]

/-- `a_V(u*) ≤ a_V(Ū + 1/2)`. -/
lemma aV_ustar_le {τ ℓ : ℝ} (hτ : 100000000 ≤ τ) (hℓ : 0 < ℓ) :
    aV ℓ (ustar τ ℓ) ≤ BSCert.Z2.aV ℓ := by
  have hU := Uf_le_Ubar hτ hℓ
  have hU0 := Uf_pos (τ := τ) hℓ
  unfold aV BSCert.Z2.aV ustar
  have h1 : (Uf τ ℓ + 1 / 2) ^ 2 ≤ (BSCert.Z2.Ubar ℓ + 1 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : Real.log (Uf τ ℓ + 1 / 2 + 2) ≤ Real.log (BSCert.Z2.Ubar ℓ + 1 / 2 + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (Uf τ ℓ + 1 / 2 + 2) := Real.log_nonneg (by linarith)
  apply div_le_div_of_nonneg_right _ hℓ.le
  have := mul_le_mul h1 h2 h3 (by positivity)
  norm_num
  nlinarith

lemma PhiInf_ge {τ : ℝ} (hτ : 0 < τ) : C0 ≤ PhiInf τ := by
  unfold PhiInf
  have h1 : 1 ≤ Real.exp (kappa τ / τ) := Real.one_le_exp (by unfold kappa; positivity)
  have : 1 ≤ max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ))) :=
    h1.trans (le_max_left _ _)
  unfold C0; nlinarith

/-- **Step 6 in region Z2**: `T ≤ exp(κ_max/ℓ + a_V(Ū + 1/2) + E_T)`. -/
theorem Tterm_le {τ ℓ u : ℝ} (hτ : 100000000 ≤ τ) (hℓτ : 30 * τ < ℓ) (hu : 2 ≤ u)
    (huU : u ≤ Uf τ ℓ) : Tterm τ ℓ u ≤ BSCert.Z2.T Dickman.ratio ℓ u := by
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set r0 := Dickman.ratio (u - 1)
  set X := ustar τ ℓ - (u - 1)
  have hX : ustar τ ℓ - (u - 1) = Uf τ ℓ - u + 3 / 2 := by unfold ustar; ring
  -- lower bound for `G`
  have hA : 0 ≤ BSCert.Z2.A ℓ u := by
    unfold BSCert.Z2.A; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + u); positivity
  have hρ0 := Dickman.rho_pos (u - 1)
  set G' := C0 * Real.exp (-(kappa τ / ℓ)) * Dickman.rho (u - 1) * Real.exp (aQ ℓ u)
  have hC0 : (0 : ℝ) < C0 := by unfold C0; norm_num
  have hG'pos : 0 < G' := by positivity
  have hG : G' ≤ Gf τ ℓ u := by
    unfold Gf Phi Qf
    have h1 := PhiInf_ge hτ0
    have h2 : Real.exp (aQ ℓ u) ≤ Real.exp (BSCert.Z2.A ℓ u + aQ ℓ u) :=
      Real.exp_le_exp.mpr (by linarith)
    have hP : 0 < PhiInf τ := lt_of_lt_of_le hC0 h1
    apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1
      (Real.exp_pos _).le) hρ0.le) h2 (Real.exp_pos _).le (by positivity)
  -- decay of `ρ`
  have hρ : Dickman.rho (ustar τ ℓ) ≤ Dickman.rho (u - 1) * Real.exp (-(r0 * X)) := by
    apply Dickman.rho_le_exp (by linarith)
    unfold ustar; have := Uf_pos (τ := τ) hℓ0; linarith
  have hN : ℓ / τ * C0 * Dickman.rho (ustar τ ℓ) * Real.exp (aV ℓ (ustar τ ℓ)) ≤
      ℓ / τ * C0 * (Dickman.rho (u - 1) * Real.exp (-(r0 * X))) *
        Real.exp (aV ℓ (ustar τ ℓ)) := by
    have hc : 0 ≤ ℓ / τ * C0 := by unfold C0; positivity
    gcongr
  have hstep : Tterm τ ℓ u ≤ ℓ / τ * C0 * (Dickman.rho (u - 1) * Real.exp (-(r0 * X))) *
      Real.exp (aV ℓ (ustar τ ℓ)) / G' := by
    unfold Tterm
    apply div_le_div₀ (by unfold C0; positivity) hN hG'pos hG
  have heq : ℓ / τ * C0 * (Dickman.rho (u - 1) * Real.exp (-(r0 * X))) *
      Real.exp (aV ℓ (ustar τ ℓ)) / G' =
      Real.exp (Real.log (ℓ / τ) + kappa τ / ℓ + aV ℓ (ustar τ ℓ) - aQ ℓ u - r0 * X) := by
    simp only [G']
    rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
      Real.exp_neg, Real.exp_neg]
    unfold C0
    field_simp
  rw [heq] at hstep
  refine hstep.trans (Real.exp_le_exp.mpr ?_)
  have hκ : kappa τ / ℓ ≤ BSCert.Z2.kmax ℓ / ℓ := by
    apply div_le_div_of_nonneg_right _ hℓ0.le
    unfold kappa BSCert.Z2.kmax; linarith
  have haV := aV_ustar_le hτ hℓ0
  have hE := exponent_le_ET (by linarith) hℓτ (by linarith) hu huU
  rw [show X = Uf τ ℓ - u + 3 / 2 from hX]
  linarith

end BSaias

end
