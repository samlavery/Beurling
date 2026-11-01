module

public import RequestProject.Beurling.Noise.BSL57RDefs
public import RequestProject.Beurling.Noise.BSL57
public import RequestProject.Beurling.Noise.BSZ2Tail

/-!
# Lemma 5.7, remainder (f): the tail `T` (`remF`; 04c-saias.tex, lines 478-485)

From Step 6, `T ≤ exp(y + κ_Φ/ℓ + a_V(u*) - a(ℓ,u) - r₀(Ū - u + 3/2))`, `y = log(ℓ/τ)`
(`Tterm_le_exp`), with `κ_Φ/ℓ + a_V(u*) ≤ 0.13336` (`small_exponent`). Write
`Ū - u₀ = u₀ s`, `s = √(2y + 4) ≥ 3.28`, so `α' = s/u₀`.

* If `Ū - u ≤ (Ū - u₀)/2`: `u - 1 ≥ 2.6 u₀`, `r₀ ≥ log(2.6 u₀)`, `y - a(ℓ,u) ≤ α'(Ū-u) - 2`
  (convexity) and `α' ≤ 1 ≤ r₀`, so `T ≤ e^{-3.29} u₀^{-3/2}`; and `s_a ≥ 0.67 a' - 0.54/√ℓ`
  with `a' ≥ α'/2 ≥ 1.64/u₀` (Lemma 5.7, slack), so `0.035 ℓ^{-1/8} s_a ≥ 0.0384 u₀^{-3/2}`.
* Otherwise `Ū - u ≥ 1.64 u₀`, `r₀ ≥ 1`, `a ≥ 0`, `y ≤ log ℓ`, and `ℓT ≤ ℓ² e^{-1.64 u₀} ≤ 1/ℓ`.
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- The Step-6 bound for `T` before the maximisation over `y`. -/
lemma Tterm_le_exp (hτ : 100000000 ≤ τ) (hℓ0 : 0 < ℓ) (hu : 2 ≤ u) (hU : u ≤ Uf τ ℓ) :
    Tterm τ ℓ u ≤ Real.exp (Real.log (ℓ / τ) + kappa τ / ℓ + aV ℓ (ustar τ ℓ) - aQ ℓ u -
      Dickman.ratio (u - 1) * (Uf τ ℓ - u + 3 / 2)) := by
  have hτ0 : 0 < τ := by linarith
  set r0 := Dickman.ratio (u - 1)
  set X := ustar τ ℓ - (u - 1)
  have hX : X = Uf τ ℓ - u + 3 / 2 := by simp only [X]; unfold ustar; ring
  have hA : 0 ≤ BSCert.Z2.A ℓ u := by
    unfold BSCert.Z2.A; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + u); positivity
  have hρ0 := Dickman.rho_pos (u - 1)
  set G' := C0 * Real.exp (-(kappa τ / ℓ)) * Dickman.rho (u - 1) * Real.exp (aQ ℓ u)
  have hC0 : (0 : ℝ) < C0 := by unfold C0; norm_num
  have hG'pos : 0 < G' := by positivity
  have hG : G' ≤ Gf τ ℓ u := by
    unfold Gf Phi Qf
    have h1 := BSaias.PhiInf_ge hτ0
    have h2 : Real.exp (aQ ℓ u) ≤ Real.exp (BSCert.Z2.A ℓ u + aQ ℓ u) :=
      Real.exp_le_exp.mpr (by linarith)
    have hP : 0 < PhiInf τ := lt_of_lt_of_le hC0 h1
    apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1
      (Real.exp_pos _).le) hρ0.le) h2 (Real.exp_pos _).le (by positivity)
  have hρ : Dickman.rho (ustar τ ℓ) ≤ Dickman.rho (u - 1) * Real.exp (-(r0 * X)) := by
    apply Dickman.rho_le_exp (by linarith)
    unfold ustar; linarith
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
  rw [heq, hX] at hstep
  exact hstep

/-! ## Numerical facts -/

lemma exp_338_le : Real.exp 3.38 ≤ 30 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := (0.38 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 3.38 = Real.exp 1 ^ 3 * Real.exp 0.38 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
  have h4 := Real.exp_pos 0.38
  have h5 : 0 ≤ Real.exp 1 ^ 3 := by positivity
  nlinarith

lemma exp_095_le : Real.exp 0.95 ≤ 2.6 := by
  have h2 := Real.exp_bound' (x := (0.95 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  linarith

lemma exp_329_ge : 26.05 ≤ Real.exp 3.29 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (x := (0.29 : ℝ)) (by norm_num)
  have e : Real.exp 3.29 = Real.exp 1 ^ 3 * Real.exp 0.29 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
  have h4 : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by positivity
  nlinarith

/-- `κ_Φ/ℓ + a_V(u*) ≤ 0.13336` on the range of Lemma 5.7. -/
lemma small_exponent (hR : LargeRange τ ℓ u) : kappa τ / ℓ + aV ℓ (ustar τ ℓ) ≤ 0.13336 := by
  obtain ⟨hτ, hτℓ, hℓ, -, -⟩ := hR
  have hℓ0 : 0 < ℓ := by linarith
  have hκ : kappa τ / ℓ ≤ 0.13334 := by
    rw [div_le_iff₀ hℓ0]; unfold kappa; nlinarith
  -- `λ ≤ 1.5·10⁻⁶` from `ε(ℓ) ≤ 0.03`
  have he := lemma57Eps τ ℓ hτ hτℓ hℓ
  rw [epsL_eq] at he
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hℓ0 _
  have hlam : lamL τ ℓ ≤ 0.0000015 := by linarith
  have hu0 := u0_ge hℓ
  set U := Uf τ ℓ
  have hU : u0 ℓ ≤ U := by
    simp only [U]; unfold Uf
    have := Real.sqrt_nonneg (2 * Real.log (ℓ / τ) + 4)
    have : 0 ≤ u0 ℓ := by linarith
    nlinarith
  have hU1 : 31622 ≤ U := by linarith
  have hL1 : 1 ≤ Real.log (2 + U) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlog : Real.log (U + 1 / 2 + 2) ≤ 1.001 * Real.log (2 + U) := by
    have h1 : Real.log (U + 1 / 2 + 2) - Real.log (2 + U) ≤ (U + 1 / 2 + 2) / (2 + U) - 1 := by
      rw [← Real.log_div (by linarith) (by linarith)]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : (U + 1 / 2 + 2) / (2 + U) - 1 ≤ 0.001 := by
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; linarith
    linarith
  have hsq : (U + 1 / 2) ^ 2 ≤ 1.001 * U ^ 2 := by nlinarith
  have haV : aV ℓ (ustar τ ℓ) ≤ 13 * lamL τ ℓ := by
    unfold aV ustar lamL
    rw [div_le_iff₀ hℓ0, mul_div_assoc', div_mul_cancel₀ _ hℓ0.ne']
    have hl0 : 0 ≤ Real.log (U + 1 / 2 + 2) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ U + 1 / 2 + 2); exact this
    calc 4 * 3.2 * (U + 1 / 2) ^ 2 * Real.log (U + 1 / 2 + 2)
        ≤ 4 * 3.2 * (1.001 * U ^ 2) * (1.001 * Real.log (2 + U)) := by gcongr
      _ ≤ 13 * (U ^ 2 * Real.log (2 + U)) := by nlinarith [sq_nonneg U]
  linarith

lemma exp_neg_329_le : Real.exp (-3.29) ≤ 0.0384 := by
  have he := exp_329_ge
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]; linarith

/-- `s_a ≥ 1.0971/u₀` when `u - u₀ ≥ 1.64 u₀` (from the slack bound of Lemma 5.7). -/
lemma sA_lower (hR : LargeRange τ ℓ u) (hv : 1.64 * u0 ℓ ≤ u - u0 ℓ) :
    (192 / 175) / u0 ℓ ≤ sA ℓ u := by
  have hℓ := hR.2.2.1
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hu0 := u0_ge hℓ
  have hu0p : 0 < u0 ℓ := by linarith
  have hsqℓ : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
  obtain ⟨hs1, -⟩ := lemma57Slack τ ℓ u hR
  have hsa := hs1 (by linarith)
  have hap : 1.64 / u0 ℓ ≤ aprime ℓ u := by
    unfold aprime
    rw [max_eq_left (by linarith), ← hsqℓ, div_le_div_iff₀ hu0p (by positivity)]
    have := mul_le_mul_of_nonneg_right hv hu0p.le
    linarith
  have h1 : 0.54 / √ℓ ≤ 0.0001 / u0 ℓ := by
    rw [← hsqℓ, div_le_div_iff₀ (by positivity) hu0p]; nlinarith
  have h2 : 0.67 * (1.64 / u0 ℓ) = 1.0988 / u0 ℓ := by ring
  have h3 : (192 / 175) / u0 ℓ ≤ 1.0988 / u0 ℓ - 0.0001 / u0 ℓ := by
    rw [div_sub_div_same]; exact div_le_div_of_nonneg_right (by norm_num) hu0p.le
  linarith

/-! ## Remainder (f) -/

set_option maxHeartbeats 1000000 in

/-- **Remainder (f)** (lines 478-485). -/
theorem remF : RemF := by
  intro τ ℓ u hR
  obtain ⟨hτ, hτℓ, hℓ, hu, hUu⟩ := id hR
  have hℓ0 : 0 < ℓ := by linarith
  have hτ0 : 0 < τ := by linarith
  have hu0 := u0_ge hℓ
  have hsqℓ : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
  have hsℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  have hT := Tterm_le_exp hτ hℓ0 hu hUu
  have hsmall := small_exponent hR
  set y := Real.log (ℓ / τ) with hy
  set s := √(2 * y + 4) with hs
  set r0 := Dickman.ratio (u - 1)
  have hr0 : 1 ≤ r0 := ratio_ge_one (by linarith)
  have hy338 : 3.38 ≤ y := by
    rw [hy, Real.le_log_iff_exp_le (by positivity)]
    refine exp_338_le.trans ?_
    rw [le_div_iff₀ hτ0]; linarith
  have hs328 : 3.28 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsu0 : s ≤ u0 ℓ := BSaias.sqrt_y_le_u0 (by linarith) (by linarith)
  have hUdef : Uf τ ℓ = u0 ℓ + u0 ℓ * s := rfl
  have hα : alphaL τ ℓ = s / u0 ℓ := by
    unfold alphaL aprime
    rw [hUdef, show u0 ℓ + u0 ℓ * s - u0 ℓ = u0 ℓ * s by ring,
      max_eq_left (by positivity), ← hsqℓ]
    field_simp
  have hαle : alphaL τ ℓ ≤ 1 := by rw [hα, div_le_one (by linarith)]; exact hsu0
  have haQ0 : 0 ≤ aQ ℓ u := by unfold aQ; positivity
  constructor
  · intro hc
    rw [hUdef, show u0 ℓ + u0 ℓ * s - u0 ℓ = u0 ℓ * s by ring] at hc
    have hv : 1.64 * u0 ℓ ≤ u - u0 ℓ := by nlinarith
    -- convexity of `a(ℓ, ·)`
    have haU : aQ ℓ (Uf τ ℓ) = y + 2 := BSaias.aQ_Uf hℓ0 (by linarith)
    have hconv : aQ ℓ (Uf τ ℓ) - aQ ℓ u ≤ alphaL τ ℓ * (Uf τ ℓ - u) := by
      rw [hα]
      unfold aQ
      rw [max_eq_left (by rw [hUdef]; nlinarith), max_eq_left (by linarith)]
      rw [hUdef, ← hsqℓ]
      rw [div_sub_div_same, div_le_iff₀ (by positivity)]
      have hu0p : 0 < u0 ℓ := by linarith
      field_simp
      nlinarith [mul_pos hu0p hu0p]
    have hUu' : 0 ≤ Uf τ ℓ - u := by linarith
    -- the exponent
    have hlog : Real.log (2.6 * u0 ℓ) ≤ r0 := by
      have := ratio_ge_log (x := u - 1) (by linarith)
      exact (Real.log_le_log (by positivity) (by linarith)).trans this
    have hl26 : 0.95 ≤ Real.log 2.6 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact exp_095_le
    have hlu : Real.log (2.6 * u0 ℓ) = Real.log 2.6 + Real.log (u0 ℓ) :=
      Real.log_mul (by norm_num) (by linarith)
    have hE : Real.log (ℓ / τ) + kappa τ / ℓ + aV ℓ (ustar τ ℓ) - aQ ℓ u -
        r0 * (Uf τ ℓ - u + 3 / 2) ≤ -3.29 - 3 / 2 * Real.log (u0 ℓ) := by
      have h1 : (alphaL τ ℓ - r0) * (Uf τ ℓ - u) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hUu'
      nlinarith
    have hT2 := hT.trans (Real.exp_le_exp.mpr hE)
    -- `e^{-3/2 log u₀} = 1/(u₀ √u₀)`
    have hu0p : 0 < u0 ℓ := by linarith
    have hsu : 0 < √(u0 ℓ) := Real.sqrt_pos.mpr hu0p
    have hexp15 : Real.exp (-3.29 - 3 / 2 * Real.log (u0 ℓ)) =
        Real.exp (-3.29) / (u0 ℓ * √(u0 ℓ)) := by
      have h32 : Real.exp (3 / 2 * Real.log (u0 ℓ)) = u0 ℓ * √(u0 ℓ) := by
        rw [show 3 / 2 * Real.log (u0 ℓ) = Real.log (u0 ℓ) + Real.log (√(u0 ℓ)) by
          rw [Real.log_sqrt hu0p.le]; ring, Real.exp_add, Real.exp_log hu0p, Real.exp_log hsu]
      rw [Real.exp_sub, h32]
    rw [hexp15] at hT2
    have hsA := sA_lower hR hv
    rw [rpow_neg_eighth hℓ0]
    have hem := exp_neg_329_le
    refine hT2.trans ?_
    calc Real.exp (-3.29) / (u0 ℓ * √(u0 ℓ)) ≤ 0.0384 / (u0 ℓ * √(u0 ℓ)) :=
          div_le_div_of_nonneg_right hem (by positivity)
      _ = 0.035 * (1 / √(u0 ℓ)) * ((192 / 175) / u0 ℓ) := by field_simp; norm_num
      _ ≤ 0.035 * (1 / √(u0 ℓ)) * sA ℓ u := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hsA
  · intro hc
    rw [hUdef, show u0 ℓ + u0 ℓ * s - u0 ℓ = u0 ℓ * s by ring] at hc
    push_neg at hc
    have hUu2 : 1.64 * u0 ℓ ≤ Uf τ ℓ - u := by rw [hUdef]; nlinarith
    have hyℓ : y ≤ Real.log ℓ := by
      rw [hy]; exact Real.log_le_log (by positivity) (div_le_self hℓ0.le (by linarith))
    have hE : Real.log (ℓ / τ) + kappa τ / ℓ + aV ℓ (ustar τ ℓ) - aQ ℓ u -
        r0 * (Uf τ ℓ - u + 3 / 2) ≤ Real.log ℓ - 1.64 * u0 ℓ := by
      have : Uf τ ℓ - u + 3 / 2 ≤ r0 * (Uf τ ℓ - u + 3 / 2) := by
        have : 0 ≤ Uf τ ℓ - u + 3 / 2 := by linarith
        nlinarith
      linarith
    have hT2 := hT.trans (Real.exp_le_exp.mpr hE)
    rw [Real.exp_sub, Real.exp_log hℓ0] at hT2
    -- `ℓ³ ≤ e^{1.64 u₀}`
    have h4 : u0 ℓ ^ 4 = ℓ := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsqℓ, Real.sq_sqrt hℓ0.le]
    set x := 1.64 * u0 ℓ
    have hx : 0 ≤ x := by simp only [x]; linarith
    have h20 := Real.pow_div_factorial_le_exp (x := x) hx 20
    have hfac : ((20 : ℕ).factorial : ℝ) ≤ (1.64 : ℝ) ^ 20 * 31622 ^ 8 := by
      norm_num [Nat.factorial]
    have hu8 : (31622 : ℝ) ^ 8 ≤ u0 ℓ ^ 8 := pow_le_pow_left₀ (by norm_num) hu0 8
    have hℓ3 : ℓ ^ 3 ≤ Real.exp x := by
      refine le_trans ?_ h20
      rw [le_div_iff₀ (by positivity), ← h4]
      have : x ^ 20 = (1.64 : ℝ) ^ 20 * u0 ℓ ^ 8 * u0 ℓ ^ 12 := by simp only [x]; ring
      rw [this]
      have h12 : 0 ≤ u0 ℓ ^ 12 := by positivity
      have : ((20 : ℕ).factorial : ℝ) ≤ (1.64 : ℝ) ^ 20 * u0 ℓ ^ 8 :=
        hfac.trans (mul_le_mul_of_nonneg_left hu8 (by positivity))
      calc (u0 ℓ ^ 4) ^ 3 * ((20 : ℕ).factorial : ℝ) = u0 ℓ ^ 12 * ((20 : ℕ).factorial : ℝ) := by
            ring
        _ ≤ u0 ℓ ^ 12 * ((1.64 : ℝ) ^ 20 * u0 ℓ ^ 8) := mul_le_mul_of_nonneg_left this h12
        _ = (1.64 : ℝ) ^ 20 * u0 ℓ ^ 8 * u0 ℓ ^ 12 := by ring
    have hex := Real.exp_pos x
    calc ℓ * Tterm τ ℓ u ≤ ℓ * (ℓ / Real.exp x) := mul_le_mul_of_nonneg_left hT2 hℓ0.le
      _ ≤ 1 / ℓ := by
          rw [mul_div_assoc', div_le_div_iff₀ hex hℓ0]
          nlinarith

end BSaias.Large

end
