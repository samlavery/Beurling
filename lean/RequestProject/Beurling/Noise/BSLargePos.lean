module

public import RequestProject.Beurling.Noise.BSLargePi
public import RequestProject.BSCert.DickmanCert
meta import RequestProject.BSCert.AuxCert

/-!
# Positivity of `c(u)` (Theorem 5.6, Step 7(ii); 04c-saias.tex, lines 505-536)

* `c0_ge_margin`: for `u ≥ 27`, `c₀(u) ≥ K' u² (m(u) + log(1+u))`, where `m = BSCert.cAMargin r`
  is the margin of check (1) of `aux_cert_arb.py`. This is the paper's bound
  `c₀/(K'u²) ≥ 5 log(1+u)[3(1 - 1/r(u)) - …] - 2r(u-1) - (u+1)/u²`, from
  `j_A ≤ (1+u)³ log(2+u)/u - 3u² log(1+u)(1 - 1/r(u)) + 144Λ(u)/(u r(u-1)²)`, `e₁ = u² r(u-1)`,
  `e₂ ≤ u + 1` and `B = 5K'`.
* `cAMargin_pos_large`: `m(u) > 0` for `u ≥ 4·10⁵` (the analytic range; `r_low ≥ 15.3` there).
  With `BSCert.cA_certificate_dickman` on `[27, 4·10⁵]`: `c0_ge` (`c₀(u) ≥ K' u² log(1+u)` for
  every `u ≥ 27`).
* `cfun_ge_small`: `Φ`-dominance for `2 ≤ u < 27`: `c(u) ≥ 10⁶`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

lemma ratio_ge_table {x : ℚ} (hx : 1 ≤ x) {v : ℝ} (hv : (x : ℝ) ≤ v) :
    ((BSCert.rLow BSCert.auxTable x : ℚ) : ℝ) ≤ Dickman.ratio v :=
  BSCert.rLow_le BSCert.dickmanRatioFacts (BSCert.rlowTable_ok BSCert.dickmanRatioFacts 400000)
    hx hv

lemma rLow_26 : (2 : ℚ) ≤ BSCert.rLow BSCert.auxTable 26 := by native_decide

lemma rLow_399999 : (153 / 10 : ℚ) ≤ BSCert.rLow BSCert.auxTable 399999 := by native_decide

/-- `r(v) ≥ 2` for `v ≥ 26`. -/
lemma ratio_ge_two {v : ℝ} (hv : 26 ≤ v) : 2 ≤ Dickman.ratio v := by
  have h := ratio_ge_table (x := 26) (by norm_num) (by exact_mod_cast hv)
  have h2 : ((2 : ℚ) : ℝ) ≤ ((BSCert.rLow BSCert.auxTable 26 : ℚ) : ℝ) := by exact_mod_cast rLow_26
  push_cast at h2; linarith

/-- `r(v) ≥ 15.3` for `v ≥ 399999`. -/
lemma ratio_ge_153 {v : ℝ} (hv : 399999 ≤ v) : 15.3 ≤ Dickman.ratio v := by
  have h := ratio_ge_table (x := 399999) (by norm_num) (by exact_mod_cast hv)
  have h2 : ((153 / 10 : ℚ) : ℝ) ≤ ((BSCert.rLow BSCert.auxTable 399999 : ℚ) : ℝ) := by
    exact_mod_cast rLow_399999
  push_cast at h2; linarith

/-- (R4) with `δ = 1/2`: `r(u-1) ≤ 2 log(2u)` for `u ≥ 2`. -/
lemma ratio_le_two_log {u : ℝ} (hu : 2 ≤ u) : Dickman.ratio (u - 1) ≤ 2 * Real.log (2 * u) := by
  have h := Dickman.ratio_upper (x := u - 1) (δ := 1 / 2) (by linarith) (by norm_num) (by norm_num)
  have e : (u - 1 + 1) / (1 / 2) = 2 * u := by ring
  rw [e] at h
  norm_num at h
  linarith

lemma momM_le {r : ℝ} (hr : 2 ≤ r) : 8 * momM r ≤ 144 / r ^ 2 := by
  unfold momM
  have hr0 : 0 < r := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity)
    (by positivity), div_add_div _ _ (by positivity) (by positivity), mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ r - 2 := by linarith
  nlinarith [pow_pos hr0 5, pow_pos hr0 6, pow_pos hr0 7, pow_pos hr0 8, pow_pos hr0 9,
    pow_pos hr0 10, pow_pos hr0 11, pow_pos hr0 12, pow_pos hr0 13, pow_pos hr0 14,
    mul_nonneg h1 (pow_pos hr0 13).le, mul_nonneg h1 (pow_pos hr0 12).le,
    mul_nonneg h1 (pow_pos hr0 11).le, mul_nonneg h1 (pow_pos hr0 10).le]

lemma momM_le_49 {r : ℝ} (hr : 1 ≤ r) : momM r ≤ 49 := by
  unfold momM
  have h2 : 1 / r ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have h3 : 6 / r ^ 3 ≤ 6 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [one_le_pow₀ (n := 3) hr]
  have h4 : 18 / r ^ 4 ≤ 18 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [one_le_pow₀ (n := 4) hr]
  have h5 : 24 / r ^ 5 ≤ 24 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [one_le_pow₀ (n := 5) hr]
  linarith

/-- The chord coefficient: `u³(3u-4) log(1+u)/(u-1)² ≥ 3u² log(1+u)` for `u ≥ 2`. -/
lemma kc_ge {u : ℝ} (hu : 2 ≤ u) :
    3 * u ^ 2 * Real.log (1 + u) ≤ u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u)
  rw [le_div_iff₀ (by nlinarith)]
  have : 3 * u ^ 2 * (u - 1) ^ 2 ≤ u ^ 3 * (3 * u - 4) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hL]

/-- **`c₀` in terms of the certified margin** (u ≥ 27). -/
lemma c0_ge_margin {u : ℝ} (hu : 27 ≤ u) :
    Kp * u ^ 2 * (BSCert.cAMargin Dickman.ratio u + Real.log (1 + u)) ≤ c0fun u := by
  have hu2 : 2 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  set r := Dickman.ratio u
  set r0 := Dickman.ratio (u - 1)
  set L := Real.log (1 + u)
  have hL : 0 < L := Real.log_pos (by linarith)
  have hr : 1 ≤ r := ratio_ge_one (by linarith)
  have hr0 : 2 ≤ r0 := ratio_ge_two (by linarith)
  have hjA := jA_le hu2
  have he2 := e2_le hu2
  have hk := kc_ge hu2
  have hM := momM_le hr0
  have h1r : 0 ≤ 1 - 1 / r := by
    have : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; exact hr
    linarith
  have hLam0 : 0 ≤ Lam u := by
    unfold Lam; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + u); positivity
  -- the `j_A` bound in the paper's form
  have hjA' : jA u ≤ (1 + u) ^ 3 * Real.log (2 + u) / u - 3 * u ^ 2 * L * (1 - 1 / r)
      + 144 * Lam u / (u * r0 ^ 2) := by
    have a1 : u ^ 3 * (3 * u - 4) * L / (u - 1) ^ 2 * (1 - 1 / r) ≥ 3 * u ^ 2 * L * (1 - 1 / r) :=
      mul_le_mul_of_nonneg_right hk h1r
    have a2 : 8 * Lam u * momM r0 / u ≤ 144 * Lam u / (u * r0 ^ 2) := by
      rw [div_le_div_iff₀ hu0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hM hLam0
      have e : Lam u * (144 / r0 ^ 2) * r0 ^ 2 = 144 * Lam u := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ u * r0 ^ 2)]
    linarith
  have he1 := e1_eq u
  -- the identity
  -- `K' u² (m + L) = 33 u² L (1 - 1/r) - 11 c/u - 1584 Λ/(u r₀²) - 4.4 u² r₀ - 2.2(u+1)`
  have hid : Kp * u ^ 2 * (BSCert.cAMargin Dickman.ratio u + L) =
      33 * u ^ 2 * L * (1 - 1 / r) - 11 * ((1 + u) ^ 3 * Real.log (2 + u) / u)
        - 11 * (144 * Lam u / (u * r0 ^ 2)) - 2 * Kp * (u ^ 2 * r0) - Kp * (u + 1) := by
    unfold BSCert.cAMargin Lam Kp
    have hr0' : 0 < r0 := by linarith
    simp only [r, r0, L] at *
    field_simp
    ring
  unfold c0fun
  rw [hid, he1]
  have hKp : Kp = 2.2 := rfl
  rw [hKp] at *
  nlinarith

/-- The analytic range of check (1): `m(u) > 0` for `u ≥ 4·10⁵`. -/
lemma cAMargin_pos_large {u : ℝ} (hu : 400000 ≤ u) : 0 < BSCert.cAMargin Dickman.ratio u := by
  have hu0 : 0 < u := by linarith
  set r := Dickman.ratio u
  set r0 := Dickman.ratio (u - 1)
  set L := Real.log (1 + u)
  have hr : 15.3 ≤ r := ratio_ge_153 (by linarith)
  have hr0 : 15.3 ≤ r0 := ratio_ge_153 (by linarith)
  have hr0u : r0 ≤ 2 * Real.log (2 * u) := ratio_le_two_log (by linarith)
  -- `L ≥ 12`
  have hL12 : 12 ≤ L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have e : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 12 ≤ (2.7182818286 : ℝ) ^ 12 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h.le 12
    norm_num at this ⊢; linarith
  have hL0 : 0 < L := by linarith
  -- `log(2+u) ≤ L + 1/(1+u)`
  have hl2 : Real.log (2 + u) ≤ L + 1 / (1 + u) := by
    have e : 2 + u = (1 + u) * (1 + 1 / (1 + u)) := by field_simp; ring
    rw [e, Real.log_mul (by linarith) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (1 + u) by positivity)
    linarith
  have hl2' : Real.log (2 + u) ≤ 1.00001 * L := by
    have : 1 / (1 + u) ≤ 0.00001 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlu : Real.log (2 * u) ≤ Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) hu0.ne']
    have := Real.log_le_log hu0 (by linarith : u ≤ 1 + u); linarith
  have hlog2 := Real.log_two_lt_d9
  -- the bracket
  have hcube : (1 + u) ^ 3 ≤ 1.0001 * u ^ 3 := by
    have h1 : 3 * u ^ 2 + 3 * u + 1 ≤ 4 * u ^ 2 := by nlinarith
    have h2 : 4 * u ^ 2 ≤ 0.0001 * u ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg u)]
    nlinarith
  have hX1 : (1 + u) ^ 3 * Real.log (2 + u) / (u ^ 3 * L) ≤ 1.0002 := by
    rw [div_le_iff₀ (by positivity)]
    have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    calc (1 + u) ^ 3 * Real.log (2 + u) ≤ (1.0001 * u ^ 3) * (1.00001 * L) :=
          mul_le_mul hcube hl2' hl0 (by positivity)
      _ ≤ 1.0002 * (u ^ 3 * L) := by nlinarith [pow_pos hu0 3]
  have hX2 : 144 * (1 + u) ^ 2 * Real.log (2 + u) / (u ^ 3 * r0 ^ 2 * L) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    have hsq : (1 + u) ^ 2 ≤ 2 * u ^ 2 := by nlinarith
    have hr2 : 234 ≤ r0 ^ 2 := by nlinarith
    calc 144 * (1 + u) ^ 2 * Real.log (2 + u) ≤ 144 * (2 * u ^ 2) * (1.00001 * L) := by
          apply mul_le_mul (by nlinarith) hl2' hl0 (by positivity)
      _ ≤ 0.001 * (u ^ 3 * r0 ^ 2 * L) := by
          have : 0 ≤ u ^ 2 * L := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hr2 this,
            mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ u ^ 2 * r0 ^ 2 * L)]
  have h1r : 3 * (1 - 1 / r) ≥ 2.8 := by
    have : 1 / r ≤ 1 / 15.3 := one_div_le_one_div_of_le (by norm_num) hr
    have : (1 : ℝ) / 15.3 ≤ 0.0654 := by norm_num
    linarith
  have hbr : 1.79 ≤ 3 * (1 - 1 / r) - (1 + u) ^ 3 * Real.log (2 + u) / (u ^ 3 * L)
      - 144 * (1 + u) ^ 2 * Real.log (2 + u) / (u ^ 3 * r0 ^ 2 * L) := by linarith
  have hlast : (u + 1) / u ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have key : BSCert.cAMargin Dickman.ratio u = 5 * L * (3 * (1 - 1 / r)
      - (1 + u) ^ 3 * Real.log (2 + u) / (u ^ 3 * L)
      - 144 * (1 + u) ^ 2 * Real.log (2 + u) / (u ^ 3 * r0 ^ 2 * L)) - 2 * r0 - (u + 1) / u ^ 2
      - L := rfl
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ 5 * L)]

/-- **`c₀(u) ≥ K' u² log(1+u)` for every `u ≥ 27`** (certificate on `[27, 4·10⁵]`, analytic
beyond). -/
lemma c0_ge {u : ℝ} (hu : 27 ≤ u) : Kp * u ^ 2 * Real.log (1 + u) ≤ c0fun u := by
  have hm : 0 ≤ BSCert.cAMargin Dickman.ratio u := by
    rcases le_or_gt u 400000 with h | h
    · exact (BSCert.cA_certificate_dickman u hu h).le
    · exact (cAMargin_pos_large h.le).le
  have := c0_ge_margin hu
  have hK : 0 ≤ Kp * u ^ 2 := by unfold Kp; positivity
  nlinarith [mul_le_mul_of_nonneg_left hm hK]


lemma log_le_four {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 54) : Real.log x ≤ 4 := by
  rw [Real.log_le_iff_le_exp hx0]
  have h := Real.exp_one_gt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h.le 4
  norm_num at this ⊢; linarith

/-- `c₀(u) ≥ -6·10⁵` for `2 ≤ u ≤ 27`. -/
lemma c0_ge_small {u : ℝ} (hu : 2 ≤ u) (hu27 : u ≤ 27) : -600000 ≤ c0fun u := by
  have hu0 : 0 < u := by linarith
  set r := Dickman.ratio u
  set r0 := Dickman.ratio (u - 1)
  have hr : 1 ≤ r := ratio_ge_one (by linarith)
  have hr0 : 1 ≤ r0 := ratio_ge_one (by linarith)
  have hjA := jA_le hu
  have he2 := e2_le hu
  have hk := kc_ge hu
  have hM := momM_le_49 hr0
  have h1r : 0 ≤ 1 - 1 / r := by
    have : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; exact hr
    linarith
  have hL1 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hk0 : 0 ≤ u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 * (1 - 1 / r) := by
    apply mul_nonneg _ h1r
    exact le_trans (by positivity) hk
  have hl4 : Real.log (2 + u) ≤ 4 := log_le_four (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hq2 : (1 + u) ^ 2 ≤ 30 * u := by nlinarith
  have hq3 : (1 + u) ^ 3 ≤ 840 * u := by nlinarith
  have hA1 : (1 + u) ^ 3 * Real.log (2 + u) / u ≤ 3360 := by
    rw [div_le_iff₀ hu0]; nlinarith [mul_le_mul hq3 hl4 hl0 (by positivity)]
  have hLam0 : 0 ≤ Lam u := by unfold Lam; positivity
  have hA2 : 8 * Lam u * momM r0 / u ≤ 47040 := by
    rw [div_le_iff₀ hu0]
    have hLam : Lam u ≤ 120 * u := by
      unfold Lam; nlinarith [mul_le_mul hq2 hl4 hl0 (by positivity)]
    have hM0 : 0 ≤ momM r0 := by
      unfold momM; have : 0 < r0 := by linarith
      positivity
    nlinarith [mul_le_mul hLam hM hM0 (by positivity)]
  have hjA' : jA u ≤ 3360 + 47040 := by linarith
  have hr0u : r0 ≤ 8 := by
    have h := ratio_le_two_log hu
    have := log_le_four (x := 2 * u) (by linarith) (by linarith)
    linarith
  have he1 : e1 u ≤ 729 * 8 := by
    rw [e1_eq]
    have : u ^ 2 ≤ 729 := by nlinarith
    nlinarith
  unfold c0fun
  have hKp : Kp = 2.2 := rfl
  rw [hKp]
  linarith

/-- **`Φ`-dominance for `2 ≤ u < 27`**: `c(u) ≥ 10⁶` (`τ ≥ 10⁸`, `30τ < ℓ`, `ℓ ≥ 10¹⁸`). -/
lemma cfun_ge_small {τ ℓ u : ℝ} (hτ : 100000000 ≤ τ) (hτℓ : 30 * τ < ℓ)
    (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) (hu27 : u ≤ 27) : 1000000 ≤ cfun τ ℓ u := by
  have hu0 : 0 < u := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hκ : 400000000 ≤ kappa τ := by unfold kappa; linarith
  have hκ0 : 0 ≤ kappa τ := by linarith
  have hκu : kappa τ ≤ 4 * ℓ / 30 + 1500 := by unfold kappa; linarith
  set y := kappa τ / (u * ℓ)
  have hy0 : 0 ≤ y := div_nonneg hκ0 (by positivity)
  have hy1 : y ≤ 0.07 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hr : 1 ≤ Dickman.ratio u := ratio_ge_one (by linarith)
  have hmass : 1 / 2 ≤ 1 - 1 / (u * Dickman.ratio u) := by
    have : 2 ≤ u * Dickman.ratio u := by nlinarith
    have : 1 / (u * Dickman.ratio u) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hexp : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have h1 := Real.add_one_le_exp y
    rw [Real.exp_neg]
    have : (Real.exp y)⁻¹ ≤ 1 / (1 + y) := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have e : y / (1 + y) = 1 - 1 / (1 + y) := by field_simp; ring
    linarith
  have hPB := PhiBen_ge (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0
  have hE1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hPB' : y / (1 + y) * (1 / 2) ≤ PhiBen τ ℓ u :=
    le_trans (mul_le_mul hexp hmass (by norm_num) (by linarith)) hPB
  have hℓy : ℓ * y = kappa τ / u := by simp only [y]; field_simp
  have hmain : 6900000 ≤ ℓ * PhiBen τ ℓ u := by
    have h1 : ℓ * (y / (1 + y) * (1 / 2)) = kappa τ / u / (1 + y) / 2 := by
      rw [← hℓy]; ring
    have h2 : 400000000 / 27 ≤ kappa τ / u := by
      rw [div_le_div_iff₀ (by norm_num) hu0]; nlinarith
    have h3 : 400000000 / 27 / 1.07 / 2 ≤ kappa τ / u / (1 + y) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact div_le_div₀ (by positivity) h2 (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left hPB' hℓ0.le
    norm_num at h3
    linarith
  have hc0 := c0_ge_small hu hu27
  unfold cfun
  linarith

end BSaias.Large

end
