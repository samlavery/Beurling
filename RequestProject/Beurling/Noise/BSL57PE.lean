module

public import RequestProject.Beurling.Noise.BSL57PB

/-!
# Lemma 5.7, remainder (e) (04c-saias.tex, lines 461-477): `remE : RemE`

`ℓE₃ ≤ (2K'/ρ(u-1)) ∫ ℓη_f e^{D'₊} ρ(w-1) dw/w` (`E3_le`), and pointwise, for `1 ≤ w ≤ Ū`,
`ℓη_f ≤ 4κ_Φ/ℓ + 110 (1+w)² Λ(w)/ℓ + 1.0091 α'(1+w)² 1[w ≥ u₀ - 0.26]` (`ell_etaF_le`: the
`Φ`-, `A`- and `a`-parts of the paper). The moments then give the three bounds of (e).
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

variable {τ ℓ u : ℝ}

lemma mOf_ge_half (hℓ : 0 < ℓ) {w : ℝ} (hw : 1 ≤ w) : ℓ / 2 ≤ mOf ℓ w := by
  unfold mOf; rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith

lemma mOf_ge_fine (hℓ : 0 < ℓ) {w : ℝ} (hw : 31621 ≤ w) : 0.99996 * ℓ ≤ mOf ℓ w := by
  unfold mOf; rw [le_div_iff₀ (by linarith)]; nlinarith

/-- The `Φ`- and `A`-parts of `ℓη_f`. -/
lemma ell_etaF_PhiA (hℓ : 0 < ℓ) {w : ℝ} (hw : 1 ≤ w) (hκ : 0 ≤ kappa τ) :
    ℓ * (kappa τ / mOf ℓ w ^ 2) ≤ 4 * kappa τ / ℓ ∧
    ℓ * (BSCert.Z2.A (mOf ℓ w) w / mOf ℓ w + (1 + w) ^ 2 / ℓ *
      (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / mOf ℓ w)) ≤
      110 * (1 + w) ^ 2 * Lam w / ℓ := by
  have hm := mOf_ge_half hℓ hw
  have hm0 : 0 < mOf ℓ w := by linarith
  have hinv : 1 / mOf ℓ w ≤ 2 / ℓ := by
    rw [div_le_div_iff₀ hm0 hℓ]; linarith
  have hinv0 : 0 ≤ 1 / mOf ℓ w := by positivity
  constructor
  · have h2 : (1 / mOf ℓ w) ^ 2 ≤ (2 / ℓ) ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
    have e1 : ℓ * (kappa τ / mOf ℓ w ^ 2) = ℓ * kappa τ * (1 / mOf ℓ w) ^ 2 := by
      field_simp
    have e2 : 4 * kappa τ / ℓ = ℓ * kappa τ * (2 / ℓ) ^ 2 := by field_simp; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hℓ.le hκ)
  · set L := Real.log (2 + w)
    have hL : 1.098 ≤ L := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 3) (by linarith : (3:ℝ) ≤ 2 + w)
      have h3 : (1.098 : ℝ) ≤ Real.log 3 := by
        have := Real.log_two_gt_d9
        have h3 : Real.log 3 = Real.log 2 + Real.log 1.5 := by
          rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
        have h15 : (0.4054 : ℝ) ≤ Real.log 1.5 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          have := Real.exp_bound' (x := (0.4054 : ℝ)) (by norm_num) (by norm_num) (n := 5)
            (by norm_num)
          norm_num [Finset.sum_range_succ, Nat.factorial] at this
          linarith
        linarith
      linarith
    have hw1 : 2 ≤ 1 + w := by linarith
    have hfrac : (1 + w) ^ 3 / (2 + w) ≤ (1 + w) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (1 + w)]
    unfold BSCert.Z2.A Lam
    have hp3 : 0 ≤ (1 + w) ^ 3 := by positivity
    -- `ℓ (A/m + …) ≤ (2/ℓ)(22 (1+w)³ L · 2/ ... )`
    have e : ℓ * (11 * (1 + w) ^ 3 * L / mOf ℓ w / mOf ℓ w + (1 + w) ^ 2 / ℓ *
        (11 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w)) / mOf ℓ w)) =
        ℓ * (11 * (1 + w) ^ 3 * L) * (1 / mOf ℓ w) ^ 2 +
          (1 + w) ^ 2 * (11 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w))) *
            (1 / mOf ℓ w) := by
      field_simp
    rw [e]
    have h2 : (1 / mOf ℓ w) ^ 2 ≤ (2 / ℓ) ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
    have hL0 : 0 ≤ L := by linarith
    have hA0 : 0 ≤ ℓ * (11 * (1 + w) ^ 3 * L) := by positivity
    have hB0 : 0 ≤ (1 + w) ^ 2 * (11 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w))) := by
      positivity
    have t1 := mul_le_mul_of_nonneg_left h2 hA0
    have t2 := mul_le_mul_of_nonneg_left hinv hB0
    have e2 : ℓ * (11 * (1 + w) ^ 3 * L) * (2 / ℓ) ^ 2 = 44 * (1 + w) ^ 3 * L / ℓ := by
      field_simp; ring
    have e3 : (1 + w) ^ 2 * (11 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w))) * (2 / ℓ) =
        22 * (1 + w) ^ 2 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w)) / ℓ := by ring
    rw [e2] at t1; rw [e3] at t2
    have key : 44 * (1 + w) ^ 3 * L + 22 * (1 + w) ^ 2 * (3 * (1 + w) ^ 2 * L +
        (1 + w) ^ 3 / (2 + w)) ≤ 110 * (1 + w) ^ 2 * ((1 + w) ^ 2 * L) := by
      have h4 : 44 * (1 + w) ^ 3 * L ≤ 22 * ((1 + w) ^ 4 * L) := by
        have : (1 + w) ^ 3 * 2 ≤ (1 + w) ^ 4 := by nlinarith
        have := mul_le_mul_of_nonneg_right this hL0
        nlinarith
      have hone : 1 ≤ L / 1.098 := by rw [le_div_iff₀ (by norm_num)]; linarith
      have h5a : (1 + w) ^ 3 / (2 + w) ≤ (1 + w) ^ 2 * (L / 1.098) :=
        hfrac.trans (le_mul_of_one_le_right (by positivity) hone)
      have h5 := mul_le_mul_of_nonneg_left h5a (by positivity : 0 ≤ 22 * (1 + w) ^ 2)
      have e5 : 22 * (1 + w) ^ 2 * ((1 + w) ^ 2 * (L / 1.098)) = 22 / 1.098 * ((1 + w) ^ 4 * L) :=
        by ring
      have e6 : 22 * (1 + w) ^ 2 * (3 * (1 + w) ^ 2 * L + (1 + w) ^ 3 / (2 + w)) =
          66 * ((1 + w) ^ 4 * L) + 22 * (1 + w) ^ 2 * ((1 + w) ^ 3 / (2 + w)) := by ring
      have e7 : 110 * (1 + w) ^ 2 * ((1 + w) ^ 2 * L) = 110 * ((1 + w) ^ 4 * L) := by ring
      have h7 : 0 ≤ (1 + w) ^ 4 * L := by positivity
      rw [e6, e7]; rw [e5] at h5
      have : 22 / 1.098 ≤ (20.04 : ℝ) := by norm_num
      nlinarith
    calc _ ≤ 44 * (1 + w) ^ 3 * L / ℓ + 22 * (1 + w) ^ 2 * (3 * (1 + w) ^ 2 * L +
          (1 + w) ^ 3 / (2 + w)) / ℓ := add_le_add t1 t2
      _ = (44 * (1 + w) ^ 3 * L + 22 * (1 + w) ^ 2 * (3 * (1 + w) ^ 2 * L +
          (1 + w) ^ 3 / (2 + w))) / ℓ := by ring
      _ ≤ 110 * (1 + w) ^ 2 * ((1 + w) ^ 2 * L) / ℓ := div_le_div_of_nonneg_right key hℓ.le

lemma dpos_eq_zero_of_aQ {m w : ℝ} (hm : 0 < m) (h : aQ m w = 0) : dpos m w = 0 := by
  unfold aQ at h; unfold dpos
  have hs : 0 < 2 * √m := by have := Real.sqrt_pos.mpr hm; positivity
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · linarith

lemma T1_le {ℓ d m um u0 α : ℝ} (hℓ : 0 < ℓ) (hm : 0.99996 * ℓ ≤ m)
    (hum : 0.99999 * u0 ≤ um) (hu0 : 0 < u0) (hα : 0 ≤ α) (_hd0 : 0 ≤ d)
    (hd : d ≤ 1.00001 * (α * u0 ^ 2)) :
    ℓ * (d / (4 * (m * um))) ≤ 0.25002 * α * u0 := by
  have hm0 : 0 < m := by linarith
  have hum0 : 0 < um := by linarith
  have hden : 3.9998 * (ℓ * u0) ≤ 4 * (m * um) := by
    have := mul_le_mul hm hum (by positivity) hm0.le; nlinarith
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  calc ℓ * d ≤ ℓ * (1.00001 * (α * u0 ^ 2)) := mul_le_mul_of_nonneg_left hd hℓ.le
    _ = 1.00001 / 3.9998 * (α * u0) * (3.9998 * (ℓ * u0)) := by ring
    _ ≤ 0.25002 * α * u0 * (3.9998 * (ℓ * u0)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (1.00001 / 3.9998 : ℝ) ≤ 0.25002 := by norm_num
        nlinarith [mul_nonneg hα hu0.le]
    _ ≤ 0.25002 * α * u0 * (4 * (m * um)) := mul_le_mul_of_nonneg_left hden (by positivity)

lemma T2_le {ℓ d m sm sl α D : ℝ} (hℓ : 0 < ℓ) (hm : 0.99996 * ℓ ≤ m)
    (hsm : 0.99997 * sl ≤ sm) (hsl : 0 < sl) (hα : 0 ≤ α) (hd0 : 0 ≤ d)
    (hd : d ≤ 1.00001 * D) (hD : D = α * sl) (hD0 : 0 ≤ D) :
    ℓ * (d ^ 2 / (4 * (m * sm))) ≤ 0.25003 * α * D := by
  have hm0 : 0 < m := by linarith
  have hsm0 : 0 < sm := by linarith
  have hden : 3.9997 * (ℓ * sl) ≤ 4 * (m * sm) := by
    have := mul_le_mul hm hsm (by positivity) hm0.le; nlinarith
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have hd2 : d ^ 2 ≤ (1.00001 * D) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  calc ℓ * d ^ 2 ≤ ℓ * (1.00001 * D) ^ 2 := mul_le_mul_of_nonneg_left hd2 hℓ.le
    _ = 1.00001 ^ 2 / 3.9997 * α * D * (3.9997 * (ℓ * sl)) := by rw [hD]; ring
    _ ≤ 0.25003 * α * D * (3.9997 * (ℓ * sl)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (1.00001 ^ 2 / 3.9997 : ℝ) ≤ 0.25003 := by norm_num
        have := mul_nonneg hα hD0
        nlinarith
    _ ≤ 0.25003 * α * D * (4 * (m * sm)) := mul_le_mul_of_nonneg_left hden (by positivity)

lemma T3_le {ℓ d sm sl α p : ℝ} (hℓ : 0 < ℓ) (hsm : 0.99997 * sl ≤ sm) (hsl : 0 < sl)
    (hα : 0 ≤ α) (hp : 0 ≤ p) (hd : d ≤ 1.00001 * (α * sl)) :
    ℓ * (p / ℓ * (d / sm)) ≤ 1.00005 * α * p := by
  have hsm0 : 0 < sm := by linarith
  have e : ℓ * (p / ℓ * (d / sm)) = p * d / sm := by field_simp
  rw [e, div_le_iff₀ hsm0]
  calc p * d ≤ p * (1.00001 * (α * sl)) := mul_le_mul_of_nonneg_left hd hp
    _ = 1.00001 / 0.99997 * α * p * (0.99997 * sl) := by ring
    _ ≤ 1.00005 * α * p * (0.99997 * sl) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (1.00001 / 0.99997 : ℝ) ≤ 1.00005 := by norm_num
        have := mul_nonneg hα hp
        nlinarith
    _ ≤ 1.00005 * α * p * sm := mul_le_mul_of_nonneg_left hsm (by positivity)

/-- The `a`-part of `ℓη_f` (lines 471-476). -/
lemma LargeRange.ell_etaF_a (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : 1 ≤ w)
    (hwU : w ≤ Uf τ ℓ) :
    ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w))) +
      dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w))) +
        (1 + w) ^ 2 / ℓ * (dpos (mOf ℓ w) w / √(mOf ℓ w))) ≤
      if u0 ℓ - 0.26 ≤ w then 1.0091 * alphaL τ ℓ * (1 + w) ^ 2 else 0 := by
  have hℓ0 := hR.ℓ_pos
  have hℓ := hR.2.2.1
  have hu0 := hR.u0_ge
  have hm0 : 0 < mOf ℓ w := BSaias.mOf_pos hℓ0 (by linarith)
  split_ifs with hw
  · have hsq := hR.sqrt_pos
    have hsq2 : u0 ℓ ^ 2 = √ℓ := u0_sq hℓ0.le
    have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
    have hD : alphaL τ ℓ * √ℓ = Uf τ ℓ - u0 ℓ := by rw [hR.alpha_eq]; field_simp
    have hU3 := hR.U_ge
    have hsh2 : u0 ℓ - u0 (mOf ℓ w) ≤ 0.25013 := by
      have h := shift_le hℓ (w := w) (by linarith); linarith [h.1, h.2]
    have hd0 : 0 ≤ dpos (mOf ℓ w) w := le_max_right _ _
    have hd : dpos (mOf ℓ w) w ≤ 1.00001 * (alphaL τ ℓ * √ℓ) := by
      apply max_le _ (by positivity)
      rw [hD]; linarith
    have hm1 : 0.99996 * ℓ ≤ mOf ℓ w := mOf_ge_fine hℓ0 (by linarith)
    have hum1 : 0.99999 * u0 ℓ ≤ u0 (mOf ℓ w) := by linarith
    have hsm1 : 0.99997 * √ℓ ≤ √(mOf ℓ w) := by
      have h0 : √(0.99996 * ℓ) ≤ √(mOf ℓ w) := Real.sqrt_le_sqrt hm1
      rw [Real.sqrt_mul (by norm_num)] at h0
      have h1 : (0.99997 : ℝ) ≤ √0.99996 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      exact le_trans (mul_le_mul_of_nonneg_right h1 hsq.le) h0
    have t1 := T1_le hℓ0 hm1 hum1 (by linarith) hα0 hd0 (by rw [hsq2]; exact hd)
    have t2 := T2_le hℓ0 hm1 hsm1 hsq hα0 hd0 hd rfl (by positivity)
    have t3 := T3_le hℓ0 hsm1 hsq hα0 (by positivity : (0 : ℝ) ≤ (1 + w) ^ 2) hd
    obtain ⟨-, hUs⟩ := Z1.U_size_both (τ := τ) (ℓ := ℓ) hR.1 hR.2.1
    have hw2 : u0 ℓ ≤ 1 + w := by linarith
    have hw3 : u0 ℓ ^ 2 ≤ (1 + w) ^ 2 := pow_le_pow_left₀ (by linarith) hw2 2
    have hU2 : Uf τ ℓ ≤ 0.036 * (1 + w) ^ 2 := by rw [← hsq2] at hUs; linarith
    have hu1 : u0 ℓ ≤ (1 + w) ^ 2 / 31622 := by
      rw [le_div_iff₀ (by norm_num)]
      have : u0 ℓ * 31622 ≤ u0 ℓ * u0 ℓ := mul_le_mul_of_nonneg_left hu0 (by linarith)
      nlinarith
    have hDU : alphaL τ ℓ * √ℓ ≤ Uf τ ℓ := by rw [hD]; linarith
    have s1 := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ 0.25002 * alphaL τ ℓ)
    have s2 := mul_le_mul_of_nonneg_left (hDU.trans hU2)
      (by positivity : 0 ≤ 0.25003 * alphaL τ ℓ)
    have hp : 0 ≤ alphaL τ ℓ * (1 + w) ^ 2 := by positivity
    have e : ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w))) +
        dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w))) +
          (1 + w) ^ 2 / ℓ * (dpos (mOf ℓ w) w / √(mOf ℓ w))) =
        ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w)))) +
          ℓ * (dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w)))) +
          ℓ * ((1 + w) ^ 2 / ℓ * (dpos (mOf ℓ w) w / √(mOf ℓ w))) := by ring
    rw [e]
    have e1 : 0.25002 * alphaL τ ℓ * ((1 + w) ^ 2 / 31622) =
        0.25002 / 31622 * (alphaL τ ℓ * (1 + w) ^ 2) := by ring
    have e2 : 0.25003 * alphaL τ ℓ * (0.036 * (1 + w) ^ 2) =
        0.25003 * 0.036 * (alphaL τ ℓ * (1 + w) ^ 2) := by ring
    have e3 : 1.00005 * alphaL τ ℓ * (1 + w) ^ 2 = 1.00005 * (alphaL τ ℓ * (1 + w) ^ 2) := by
      ring
    have e4 : 1.0091 * alphaL τ ℓ * (1 + w) ^ 2 = 1.0091 * (alphaL τ ℓ * (1 + w) ^ 2) := by ring
    have e5 : 0.25002 * alphaL τ ℓ * u0 ℓ = 0.25002 * alphaL τ ℓ * u0 ℓ := rfl
    rw [e1] at s1; rw [e2] at s2; rw [e3] at t3; rw [e4]
    have e6 : 0.25003 * alphaL τ ℓ * (alphaL τ ℓ * √ℓ) ≤ 0.25003 * alphaL τ ℓ * Uf τ ℓ :=
      mul_le_mul_of_nonneg_left hDU (by positivity)
    linarith
  · push_neg at hw
    have hz : aQ (mOf ℓ w) w = 0 := by
      rcases le_or_gt w (u0 ℓ - 3) with h3 | h3
      · exact aQ_mOf_eq_zero_low hℓ0 hw1 h3
      · exact aQ_mOf_eq_zero_mid hℓ h3.le hw.le
    rw [dpos_eq_zero_of_aQ hm0 hz]
    simp

/-- **The pointwise bound for `ℓη_f`.** -/
lemma LargeRange.ell_etaF_le (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : 1 ≤ w)
    (hwU : w ≤ Uf τ ℓ) :
    ℓ * etaF τ ℓ w ≤ 4 * kappa τ / ℓ + 110 * (1 + w) ^ 2 * Lam w / ℓ +
      (if u0 ℓ - 0.26 ≤ w then 1.0091 * alphaL τ ℓ * (1 + w) ^ 2 else 0) := by
  have hℓ0 := hR.ℓ_pos
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  obtain ⟨h1, h2⟩ := ell_etaF_PhiA (τ := τ) hℓ0 hw1 hκ
  have h3 := hR.ell_etaF_a hw1 hwU
  have e : ℓ * etaF τ ℓ w = ℓ * (kappa τ / mOf ℓ w ^ 2) +
      ℓ * (BSCert.Z2.A (mOf ℓ w) w / mOf ℓ w + (1 + w) ^ 2 / ℓ *
        (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / mOf ℓ w)) +
      ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w))) +
        dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w))) +
          (1 + w) ^ 2 / ℓ * (dpos (mOf ℓ w) w / √(mOf ℓ w))) := by
    unfold etaF; ring
  rw [e]; linarith

/-- `Λ(w)(1+w)² ≤ Λ(u)(1+u)²(1+s)⁵` for `w ≥ u`. -/
lemma Lam_sq_shift {u w : ℝ} (hu : 2 ≤ u) (huw : u ≤ w) :
    (1 + w) ^ 2 * Lam w ≤ (1 + u) ^ 2 * Lam u * (1 + (w - u)) ^ 5 := by
  have h1 := Lam_shift_le hu huw
  have h2 : 1 + w ≤ (1 + u) * (1 + (w - u)) := by nlinarith
  have h3 : (1 + w) ^ 2 ≤ ((1 + u) * (1 + (w - u))) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  have hΛw : Lam w = (1 + w) ^ 2 * Real.log (2 + w) := rfl
  rw [hΛw]
  have hl : 0 ≤ (1 + w) ^ 2 * Real.log (2 + w) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + w); positivity
  have h4 := mul_le_mul h3 h1 hl (by positivity)
  calc (1 + w) ^ 2 * ((1 + w) ^ 2 * Real.log (2 + w)) ≤
      ((1 + u) * (1 + (w - u))) ^ 2 * (Lam u * (1 + (w - u)) ^ 3) := h4
    _ = (1 + u) ^ 2 * Lam u * (1 + (w - u)) ^ 5 := by ring

/-- `M₅(r) = ∑_k C(5,k) k!/r^{k+1}`. -/
noncomputable def M5 (r : ℝ) : ℝ :=
  1 / r + 5 / r ^ 2 + 2 * 10 / r ^ 3 + 6 * 10 / r ^ 4 + 24 * 5 / r ^ 5 + 120 / r ^ 6

/-- The `a`-term of `ℓη_f`. -/
noncomputable def aTerm (τ ℓ w : ℝ) : ℝ :=
  if u0 ℓ - 0.26 ≤ w then 1.0091 * alphaL τ ℓ * (1 + w) ^ 2 else 0

set_option maxHeartbeats 800000 in
/-- **The general bound for `E₃`.** -/
lemma LargeRange.E3_gen (hR : LargeRange τ ℓ u) {rmin Ah b0 b1 b2 b3 b4 b5 b6 : ℝ}
    (hrmin : 0 < rmin) (hr : rmin ≤ Dickman.ratio (u - 1) - 0.0012) (hAh : 0 ≤ Ah)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4)
    (hb5 : 0 ≤ b5) (hb6 : 0 ≤ b6)
    (hhead : ∀ w, u - 1 < w → w ≤ u → aTerm τ ℓ w ≤ Ah)
    (htail : ∀ w, u < w → w ≤ Uf τ ℓ → aTerm τ ℓ w ≤ b0 + b1 * (w - u) + b2 * (w - u) ^ 2 +
      b3 * (w - u) ^ 3 + b4 * (w - u) ^ 4 + b5 * (w - u) ^ 5 + b6 * (w - u) ^ 6) :
    ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤ 2 * Kp * (1.0004 * (4 * kappa τ / ℓ *
      (1 + 1 / (u * rmin)) + 110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 rmin / u) + Ah +
      (b0 / rmin + b1 / rmin ^ 2 + 2 * b2 / rmin ^ 3 + 6 * b3 / rmin ^ 4 + 24 * b4 / rmin ^ 5 +
        120 * b5 / rmin ^ 6 + 720 * b6 / rmin ^ 7) / u)) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  set Φc := 4 * kappa τ / ℓ
  set Ac := 110 * (1 + u) ^ 2 * Lam u / ℓ
  have hΦc : 0 ≤ Φc := by positivity
  have hAc : 0 ≤ Ac := by have := Lam_nonneg (x := u) (by linarith); positivity
  set K : ℝ := 1.0004
  have hm := master9 (u := u) (γ := 0.0012) (A := K * (Φc + Ac + Ah)) (rmin := rmin) hu hrmin hr
    (by positivity) (a0 := K * (Φc + Ac + b0)) (a1 := K * (5 * Ac + b1))
    (a2 := K * (10 * Ac + b2)) (a3 := K * (10 * Ac + b3)) (a4 := K * (5 * Ac + b4))
    (a5 := K * (Ac + b5)) (a6 := K * b6) (a7 := 0) (a8 := 0)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) le_rfl le_rfl
    (S := Ioc (u - 1) (Uf τ ℓ)) Ioc_subset_Ioi_self measurableSet_Ioc
    (f := fun w => ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0))
    (by
      apply integrableOn_Ioc_of_continuousAt (by linarith)
      intro w hw
      have hD := continuousAt_Dp (u := u) hℓ0 hw
      exact (((continuousAt_const.mul (etaF_continuousAt τ ℓ hℓ0 hw)).mul
        (hD.max continuousAt_const).rexp).mul ((Dickman.continuous_rho.comp
          (continuous_id.sub continuous_const)).continuousAt)).div continuousAt_id hw.ne')
    (fun w hw => by
      have := etaF_nonneg_large (τ := τ) (ℓ := ℓ) hR.τ_pos.le hℓ0 (by linarith [hw.1] : 0 < w)
      positivity)
    (by
      intro w hw hwu
      beta_reduce
      have hw1 : u - 1 ≤ w := hw.1.le
      have he := hR.exp_Dp_le hw1 hw.2
      rw [max_eq_right (by linarith : w - u ≤ 0), mul_zero, Real.exp_zero, mul_one] at he
      have h1 := hR.ell_etaF_le (w := w) (by linarith) hw.2
      have h2 := hhead w hw.1 hwu
      have hΛ : (1 + w) ^ 2 * Lam w ≤ (1 + u) ^ 2 * Lam u := by
        have := Lam_mono (by linarith : (0 : ℝ) ≤ w) hwu
        have h3 : (1 + w) ^ 2 ≤ (1 + u) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        exact mul_le_mul h3 this (Lam_nonneg (by linarith)) (by positivity)
      have h4 : ℓ * etaF τ ℓ w ≤ Φc + Ac + Ah := by
        have : 110 * (1 + w) ^ 2 * Lam w / ℓ ≤ Ac := by
          simp only [Ac]; apply div_le_div_of_nonneg_right _ hℓ0.le; nlinarith
        unfold aTerm at h2; simp only [Φc]; linarith
      have h0 : 0 ≤ ℓ * etaF τ ℓ w :=
        mul_nonneg hℓ0.le (etaF_nonneg_large hR.τ_pos.le hℓ0 (by linarith))
      calc ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0) ≤ (Φc + Ac + Ah) * K :=
            mul_le_mul h4 he (Real.exp_pos _).le (by positivity)
        _ = K * (Φc + Ac + Ah) := by ring)
    (by
      intro w hw huw
      beta_reduce
      have he := hR.exp_Dp_le hw.1.le hw.2
      rw [max_eq_left (by linarith : 0 ≤ w - u)] at he
      have h1 := hR.ell_etaF_le (w := w) (by linarith) hw.2
      have h2 := htail w huw hw.2
      have hΛ := Lam_sq_shift hu huw.le
      have hs : 0 ≤ w - u := by linarith
      have h4 : ℓ * etaF τ ℓ w ≤ Φc + Ac * (1 + (w - u)) ^ 5 + (b0 + b1 * (w - u) +
          b2 * (w - u) ^ 2 + b3 * (w - u) ^ 3 + b4 * (w - u) ^ 4 + b5 * (w - u) ^ 5 +
          b6 * (w - u) ^ 6) := by
        have : 110 * (1 + w) ^ 2 * Lam w / ℓ ≤ Ac * (1 + (w - u)) ^ 5 := by
          simp only [Ac]; rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ hℓ0.le; nlinarith
        unfold aTerm at h2; simp only [Φc]; linarith
      have h0 : 0 ≤ ℓ * etaF τ ℓ w :=
        mul_nonneg hℓ0.le (etaF_nonneg_large hR.τ_pos.le hℓ0 (by linarith))
      calc ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0)
          ≤ (Φc + Ac * (1 + (w - u)) ^ 5 + (b0 + b1 * (w - u) + b2 * (w - u) ^ 2 +
              b3 * (w - u) ^ 3 + b4 * (w - u) ^ 4 + b5 * (w - u) ^ 5 + b6 * (w - u) ^ 6)) *
              (K * Real.exp (0.0012 * (w - u))) :=
            mul_le_mul h4 he (Real.exp_pos _).le (by linarith)
        _ = _ := by simp only [K]; ring)
  have hE3 := hR.E3_le
  have hKp : 0 ≤ 2 * Kp := by unfold Kp; norm_num
  refine hE3.trans ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hKp
  refine hm.trans (le_of_eq ?_)
  simp only [K, Φc, Ac]; unfold M5; field_simp; ring

lemma M5_4588 : M5 4.5888 ≤ 0.87 := by unfold M5; norm_num
lemma M5_09988 : M5 0.9988 ≤ 328 := by unfold M5; norm_num

lemma LargeRange.kappa_le (hR : LargeRange τ ℓ u) : kappa τ / ℓ ≤ 0.13334 := by
  have hℓ0 := hR.ℓ_pos
  rw [div_le_iff₀ hℓ0]; unfold kappa; linarith [hR.2.1, hR.2.2.1]

/-- `ℓΦ_ben ≥ c κ_Φ/u` with `c = 0.5105` (`u ≥ 2`) or `c = 0.958` (`u ≥ 27`). -/
lemma LargeRange.ellPhiBen_ge (hR : LargeRange τ ℓ u) {c m0 y0 : ℝ}
    (hm0 : m0 ≤ 1 - 1 / (u * Dickman.ratio u)) (hm00 : 0 ≤ m0) (hy0 : kappa τ / (u * ℓ) ≤ y0)
    (hc : c * (1 + y0) ≤ m0) : c * (kappa τ / u) ≤ ℓ * PhiBen τ ℓ u := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hPB := PhiBen_ge (τ := τ) (ℓ := ℓ) hu hκ hℓ0
  set y := kappa τ / (u * ℓ)
  have hy : 0 ≤ y := by positivity
  have hexp : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have h1 := Real.add_one_le_exp y
    rw [Real.exp_neg]
    have : (Real.exp y)⁻¹ ≤ 1 / (1 + y) := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have e : y / (1 + y) = 1 - 1 / (1 + y) := by field_simp; ring
    linarith
  have hℓy : ℓ * y = kappa τ / u := by simp only [y]; field_simp
  have h1 : ℓ * (y / (1 + y) * m0) ≤ ℓ * PhiBen τ ℓ u := by
    apply mul_le_mul_of_nonneg_left _ hℓ0.le
    refine le_trans ?_ hPB
    exact mul_le_mul hexp hm0 hm00 (by linarith [Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)])
  have h2 : c * (kappa τ / u) ≤ ℓ * (y / (1 + y) * m0) := by
    have e : ℓ * (y / (1 + y) * m0) = kappa τ / u * (m0 / (1 + y)) := by
      rw [← hℓy]; field_simp
    rw [e]
    have hc' : c ≤ m0 / (1 + y) := by
      rw [le_div_iff₀ (by linarith)]
      have : c * (1 + y) ≤ c * (1 + y0) ∨ c < 0 := by
        rcases le_or_gt 0 c with h | h
        · left; exact mul_le_mul_of_nonneg_left (by linarith) h
        · right; exact h
      rcases this with h | h
      · linarith
      · nlinarith
    calc c * (kappa τ / u) ≤ m0 / (1 + y) * (kappa τ / u) :=
          mul_le_mul_of_nonneg_right hc' (div_nonneg hκ hu0.le)
      _ = kappa τ / u * (m0 / (1 + y)) := by ring
  linarith

/-- `λ ℓ = Ū² log(2 + Ū) ≥ 10⁵ u`. -/
lemma LargeRange.lam_ell_ge (hR : LargeRange τ ℓ u) : 100000 * u ≤ lamL τ ℓ * ℓ := by
  have hℓ0 := hR.ℓ_pos
  have hU := hR.U_ge
  have hu0 := hR.u0_ge
  have hu := hR.u_le
  unfold lamL
  rw [div_mul_cancel₀ _ hℓ0.ne']
  have hlog : 10 ≤ Real.log (2 + Uf τ ℓ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [exp_ten_le]
  have : 10000 ≤ Uf τ ℓ := by linarith
  have h2 : u * 10000 ≤ Uf τ ℓ ^ 2 := by nlinarith [hR.2.2.2.1]
  nlinarith

lemma exp_103_le : Real.exp 10.3 ≤ 31621 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 10.3 = Real.exp 1 ^ 10 * Real.exp 0.3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h1 : Real.exp 1 ^ 10 ≤ (2.7182818286 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h.le 10
  have h2 : Real.exp 0.3 ≤ 1 / (1 - 0.3) := by
    have := Real.add_one_le_exp (-0.3)
    have hp := Real.exp_pos 0.3
    have e2 : Real.exp (-0.3) * Real.exp 0.3 = 1 := by rw [← Real.exp_add]; simp
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  rw [e]
  have h3 : (0 : ℝ) ≤ Real.exp 1 ^ 10 := by positivity
  calc Real.exp 1 ^ 10 * Real.exp 0.3 ≤ (2.7182818286 : ℝ) ^ 10 * (1 / (1 - 0.3)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ ≤ 31621 := by norm_num

lemma log_ge_103 {x : ℝ} (hx : 31621 ≤ x) : 10.3 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]; linarith [exp_103_le]

/-- The `Φ`-part of (e): `C κ_Φ/ℓ ≤ λ ℓΦ_ben` once `C u ≤ 10⁵ c u`. -/
lemma LargeRange.phi_part (hR : LargeRange τ ℓ u) {C c : ℝ} (hC : 0 ≤ C)
    (hcPhi : c * (kappa τ / u) ≤ ℓ * PhiBen τ ℓ u) (hCc : C ≤ 100000 * c) :
    C * (kappa τ / ℓ) ≤ lamL τ ℓ * (ℓ * PhiBen τ ℓ u) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hl := hR.lam_ell_ge
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have h1 : lamL τ ℓ * (c * (kappa τ / u)) ≤ lamL τ ℓ * (ℓ * PhiBen τ ℓ u) :=
    mul_le_mul_of_nonneg_left hcPhi hlam0
  have h2 : C * (kappa τ / ℓ) ≤ lamL τ ℓ * (c * (kappa τ / u)) := by
    have e1 : C * (kappa τ / ℓ) = C * kappa τ * u / (ℓ * u) := by field_simp
    have e2 : lamL τ ℓ * (c * (kappa τ / u)) = c * kappa τ * (lamL τ ℓ * ℓ) / (ℓ * u) := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : C * u ≤ c * (lamL τ ℓ * ℓ) := by nlinarith
    nlinarith
  linarith

set_option maxHeartbeats 800000 in
/-- **(e)**, `u ≥ 27`, `u ≥ u₀ - 2`. -/
lemma LargeRange.remE_big (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) (hbig : u0 ℓ - 2 ≤ u) :
    ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤ lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 260 * lamL τ ℓ * Xu u +
      0.2 * alphaL τ ℓ * Xu u := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  set Ah := 1.0091 * alphaL τ ℓ * (1 + u) ^ 2
  have hAh : 0 ≤ Ah := by positivity
  have hr : 4.5888 ≤ Dickman.ratio (u - 1) - 0.0012 := by
    have := ratio_ge_459 (v := u - 1) (by linarith); linarith
  have hE := hR.E3_gen (rmin := 4.5888) (Ah := Ah) (b0 := Ah) (b1 := 2 * Ah) (b2 := Ah)
    (b3 := 0) (b4 := 0) (b5 := 0) (b6 := 0) (by norm_num) hr hAh hAh (by positivity) hAh le_rfl
    le_rfl le_rfl le_rfl
    (by
      intro w hw hwu
      unfold aTerm; split_ifs
      · simp only [Ah]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      · positivity)
    (by
      intro w huw hwU
      unfold aTerm; split_ifs
      · have hs : 0 ≤ w - u := by linarith
        have h3 : 1 + w ≤ (1 + u) * (1 + (w - u)) := by nlinarith
        have h2 : (1 + w) ^ 2 ≤ (1 + u) ^ 2 * (1 + 2 * (w - u) + (w - u) ^ 2) := by
          have := pow_le_pow_left₀ (by linarith) h3 2
          have e : ((1 + u) * (1 + (w - u))) ^ 2 = (1 + u) ^ 2 * (1 + 2 * (w - u) + (w - u) ^ 2)
            := by ring
          linarith
        have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1.0091 * alphaL τ ℓ)
        simp only [Ah]; nlinarith
      · have hs : 0 ≤ w - u := by linarith
        positivity)
  refine hE.trans ?_
  -- numerics
  have hM5 := M5_4588
  have hM50 : 0 ≤ M5 4.5888 := by unfold M5; norm_num
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hΛ := hR.Lam_le
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hKp : Kp = 2.2 := rfl
  -- the `Φ` part
  have hPhi : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) := by
    have hy : kappa τ / (u * ℓ) ≤ 0.005 := by
      have := hR.kappa_le
      rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ hℓ0] at this; nlinarith
    have hr1 := ratio_ge_one (v := u) (by linarith)
    have hm : (26 / 27 : ℝ) ≤ 1 - 1 / (u * Dickman.ratio u) := by
      have : 1 / (u * Dickman.ratio u) ≤ 1 / 27 := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
      linarith
    have hc := hR.ellPhiBen_ge (c := 0.958) hm (by norm_num) hy (by norm_num)
    have h1 : 1 + 1 / (u * 4.5888) ≤ 1.01 := by
      have : 1 / (u * 4.5888) ≤ 1 / (27 * 4.5888) := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
      norm_num at this ⊢; linarith
    have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) =
        (2 * Kp * 1.0004 * 4 * (1 + 1 / (u * 4.5888))) * (kappa τ / ℓ) := by ring
    rw [e]
    apply hR.phi_part (by rw [hKp]; positivity) hc
    rw [hKp]; nlinarith
  -- the `A` part
  have hA : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) ≤
      260 * lamL τ ℓ * Xu u := by
    have h1 : 1 + M5 4.5888 / u ≤ 1.0323 := by
      have : M5 4.5888 / u ≤ 0.87 / 27 :=
        div_le_div₀ (by norm_num) hM5 (by norm_num) h27
      linarith
    have h2 : Lam u / ℓ ≤ 1.001 * lamL τ ℓ := by rw [div_le_iff₀ hℓ0]; linarith
    have h3 : (1 + u) ^ 2 ≤ 1.0755 * u ^ 2 := by nlinarith
    have hlog := log_ge_329 (x := 1 + u) (by linarith)
    have hX : Kp * u ^ 2 * 3.29 ≤ Xu u := by
      unfold Xu; exact mul_le_mul_of_nonneg_left hlog (by rw [hKp]; positivity)
    have e : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) =
        2 * Kp * 1.0004 * 110 * ((1 + u) ^ 2 * (Lam u / ℓ) * (1 + M5 4.5888 / u)) := by ring
    rw [e]
    have h4 : (1 + u) ^ 2 * (Lam u / ℓ) * (1 + M5 4.5888 / u) ≤
        1.0755 * u ^ 2 * (1.001 * lamL τ ℓ) * 1.0323 := by
      apply mul_le_mul (mul_le_mul h3 h2 (by positivity) (by positivity)) h1 (by positivity)
        (by positivity)
    have h5 : 260 * lamL τ ℓ * (Kp * u ^ 2 * 3.29) ≤ 260 * lamL τ ℓ * Xu u :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    rw [hKp] at h5 ⊢
    nlinarith [mul_nonneg hlam0 (sq_nonneg u)]
  -- the `a` part
  have ha : 2 * Kp * (1.0004 * (Ah + (Ah / 4.5888 + 2 * Ah / 4.5888 ^ 2 + 2 * Ah / 4.5888 ^ 3 +
      6 * 0 / 4.5888 ^ 4 + 24 * 0 / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) / u))
      ≤ 0.2 * alphaL τ ℓ * Xu u := by
    have hu3 : 31620 ≤ u := by linarith
    have h1 : (Ah / 4.5888 + 2 * Ah / 4.5888 ^ 2 + 2 * Ah / 4.5888 ^ 3 + 6 * 0 / 4.5888 ^ 4 +
        24 * 0 / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) / u ≤
        0.00002 * Ah := by
      rw [div_le_iff₀ hu0]; norm_num; nlinarith
    have h2 : (1 + u) ^ 2 ≤ 1.0001 * u ^ 2 := by nlinarith
    have hlog := log_ge_103 (x := 1 + u) (by linarith)
    have hX : Kp * u ^ 2 * 10.3 ≤ Xu u := by
      unfold Xu; exact mul_le_mul_of_nonneg_left hlog (by rw [hKp]; positivity)
    have h3 : Ah ≤ 1.0091 * alphaL τ ℓ * (1.0001 * u ^ 2) := by
      simp only [Ah]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 0.2 * alphaL τ ℓ * (Kp * u ^ 2 * 10.3) ≤ 0.2 * alphaL τ ℓ * Xu u :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    rw [hKp] at h5 ⊢
    nlinarith [mul_nonneg hα0 (sq_nonneg u)]
  have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)) +
      110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u) + Ah + (Ah / 4.5888 +
        2 * Ah / 4.5888 ^ 2 + 2 * Ah / 4.5888 ^ 3 + 6 * 0 / 4.5888 ^ 4 + 24 * 0 / 4.5888 ^ 5 +
          120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) / u)) =
      2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) +
      2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) +
      2 * Kp * (1.0004 * (Ah + (Ah / 4.5888 + 2 * Ah / 4.5888 ^ 2 + 2 * Ah / 4.5888 ^ 3 +
      6 * 0 / 4.5888 ^ 4 + 24 * 0 / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) / u))
      := by ring
  rw [e]
  linarith

/-- The cut-off `1[w ≥ u₀ - 0.26] ≤ (s/dd)^k` behind (e) for `u < u₀ - 2`. -/
lemma LargeRange.aTerm_tail_small (hR : LargeRange τ ℓ u) (hsm : u < u0 ℓ - 2) (k : ℕ) {w : ℝ}
    (huw : u < w) :
    aTerm τ ℓ w ≤ 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / (u0 ℓ - 0.26 - u) ^ k *
      ((1 + (w - u)) ^ 2 * (w - u) ^ k) := by
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hu := hR.2.2.2.1
  have hdd : 0 < u0 ℓ - 0.26 - u := by linarith
  have hs : 0 ≤ w - u := by linarith
  unfold aTerm; split_ifs with hw
  · have hsd : u0 ℓ - 0.26 - u ≤ w - u := by linarith
    have h1 : 1 ≤ (w - u) ^ k / (u0 ℓ - 0.26 - u) ^ k := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hdd.le hsd k
    have h3 : 1 + w ≤ (1 + u) * (1 + (w - u)) := by nlinarith
    have h2 : (1 + w) ^ 2 ≤ (1 + u) ^ 2 * (1 + (w - u)) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) h3 2; rw [mul_pow] at this; exact this
    have e : 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / (u0 ℓ - 0.26 - u) ^ k *
        ((1 + (w - u)) ^ 2 * (w - u) ^ k) = 1.0091 * alphaL τ ℓ * ((1 + u) ^ 2 *
          (1 + (w - u)) ^ 2) * ((w - u) ^ k / (u0 ℓ - 0.26 - u) ^ k) := by ring
    rw [e]
    have h4 : 1.0091 * alphaL τ ℓ * (1 + w) ^ 2 ≤ 1.0091 * alphaL τ ℓ * ((1 + u) ^ 2 *
        (1 + (w - u)) ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 0 ≤ 1.0091 * alphaL τ ℓ * ((1 + u) ^ 2 * (1 + (w - u)) ^ 2) := by positivity
    nlinarith
  · positivity

lemma LargeRange.aTerm_head_small (_hR : LargeRange τ ℓ u) (hsm : u < u0 ℓ - 2) {w : ℝ}
    (hwu : w ≤ u) : aTerm τ ℓ w ≤ 0 := by
  unfold aTerm; rw [if_neg (by linarith)]

set_option maxHeartbeats 800000 in
/-- **(e)**, `27 ≤ u < u₀ - 2`. -/
lemma LargeRange.remE_mid (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) (hsm : u < u0 ℓ - 2) :
    ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤ lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 260 * lamL τ ℓ * Xu u +
      0.001 * (lamL τ ℓ + alphaL τ ℓ) * Xu u := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  set dd := u0 ℓ - 0.26 - u
  have hdd : 1.74 ≤ dd := by simp only [dd]; linarith
  set C := 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / dd ^ 2
  have hC : 0 ≤ C := by positivity
  have hr : 4.5888 ≤ Dickman.ratio (u - 1) - 0.0012 := by
    have := ratio_ge_459 (v := u - 1) (by linarith); linarith
  have hE := hR.E3_gen (rmin := 4.5888) (Ah := 0) (b0 := 0) (b1 := 0) (b2 := C) (b3 := 2 * C)
    (b4 := C) (b5 := 0) (b6 := 0) (by norm_num) hr le_rfl le_rfl le_rfl hC (by positivity) hC
    le_rfl le_rfl
    (fun w _ hwu => hR.aTerm_head_small hsm hwu)
    (by
      intro w huw _
      have := hR.aTerm_tail_small hsm 2 huw
      have e : 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / (u0 ℓ - 0.26 - u) ^ 2 *
          ((1 + (w - u)) ^ 2 * (w - u) ^ 2) = 0 + 0 * (w - u) + C * (w - u) ^ 2 +
          2 * C * (w - u) ^ 3 + C * (w - u) ^ 4 + 0 * (w - u) ^ 5 + 0 * (w - u) ^ 6 := by
        simp only [C, dd]; ring
      linarith)
  refine hE.trans ?_
  have hM5 := M5_4588
  have hM50 : 0 ≤ M5 4.5888 := by unfold M5; norm_num
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hΛ := hR.Lam_le
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hKp : Kp = 2.2 := rfl
  have hlog := log_ge_329 (x := 1 + u) (by linarith)
  have hX : Kp * u ^ 2 * 3.29 ≤ Xu u := by
    unfold Xu; exact mul_le_mul_of_nonneg_left hlog (by rw [hKp]; positivity)
  have hX0 : 0 ≤ Xu u := le_trans (by rw [hKp]; positivity) hX
  have hPhi : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) := by
    have hy : kappa τ / (u * ℓ) ≤ 0.005 := by
      have := hR.kappa_le
      rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ hℓ0] at this; nlinarith
    have hr1 := ratio_ge_one (v := u) (by linarith)
    have hm : (26 / 27 : ℝ) ≤ 1 - 1 / (u * Dickman.ratio u) := by
      have : 1 / (u * Dickman.ratio u) ≤ 1 / 27 := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
      linarith
    have hc := hR.ellPhiBen_ge (c := 0.958) hm (by norm_num) hy (by norm_num)
    have h1 : 1 + 1 / (u * 4.5888) ≤ 1.01 := by
      have : 1 / (u * 4.5888) ≤ 1 / (27 * 4.5888) := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
      norm_num at this ⊢; linarith
    have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) =
        (2 * Kp * 1.0004 * 4 * (1 + 1 / (u * 4.5888))) * (kappa τ / ℓ) := by ring
    rw [e]
    apply hR.phi_part (by rw [hKp]; positivity) hc
    rw [hKp]; nlinarith
  have hA : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) ≤
      260 * lamL τ ℓ * Xu u := by
    have h1 : 1 + M5 4.5888 / u ≤ 1.0323 := by
      have : M5 4.5888 / u ≤ 0.87 / 27 :=
        div_le_div₀ (by norm_num) hM5 (by norm_num) h27
      linarith
    have h2 : Lam u / ℓ ≤ 1.001 * lamL τ ℓ := by rw [div_le_iff₀ hℓ0]; linarith
    have h3 : (1 + u) ^ 2 ≤ 1.0755 * u ^ 2 := by nlinarith
    have e : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) =
        2 * Kp * 1.0004 * 110 * ((1 + u) ^ 2 * (Lam u / ℓ) * (1 + M5 4.5888 / u)) := by ring
    rw [e]
    have h4 : (1 + u) ^ 2 * (Lam u / ℓ) * (1 + M5 4.5888 / u) ≤
        1.0755 * u ^ 2 * (1.001 * lamL τ ℓ) * 1.0323 := by
      apply mul_le_mul (mul_le_mul h3 h2 (by positivity) (by positivity)) h1 (by positivity)
        (by positivity)
    have h5 : 260 * lamL τ ℓ * (Kp * u ^ 2 * 3.29) ≤ 260 * lamL τ ℓ * Xu u :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    rw [hKp] at h5 ⊢
    nlinarith [mul_nonneg hlam0 (sq_nonneg u)]
  have ha : 2 * Kp * (1.0004 * (0 + (0 / 4.5888 + 0 / 4.5888 ^ 2 + 2 * C / 4.5888 ^ 3 +
      6 * (2 * C) / 4.5888 ^ 4 + 24 * C / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 +
        720 * 0 / 4.5888 ^ 7) / u)) ≤ 0.001 * alphaL τ ℓ * Xu u := by
    have h1 : (0 / 4.5888 + 0 / 4.5888 ^ 2 + 2 * C / 4.5888 ^ 3 + 6 * (2 * C) / 4.5888 ^ 4 +
        24 * C / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) ≤ 0.0596 * C := by
      norm_num; nlinarith
    have hdd2 : 3.0276 ≤ dd ^ 2 := by nlinarith
    have hCb : C ≤ 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / 3.0276 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hdd2
    have h3 : (1 + u) ^ 2 ≤ 1.0755 * u ^ 2 := by nlinarith
    have h5 : 0.001 * alphaL τ ℓ * (Kp * u ^ 2 * 3.29) ≤ 0.001 * alphaL τ ℓ * Xu u :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have h6 : 2 * Kp * (1.0004 * (0 + (0 / 4.5888 + 0 / 4.5888 ^ 2 + 2 * C / 4.5888 ^ 3 +
        6 * (2 * C) / 4.5888 ^ 4 + 24 * C / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 +
          720 * 0 / 4.5888 ^ 7) / u)) ≤ 2 * Kp * (1.0004 * (0.0596 * C / u)) := by
      apply mul_le_mul_of_nonneg_left _ (by rw [hKp]; norm_num)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [zero_add]; exact div_le_div_of_nonneg_right h1 hu0.le
    refine h6.trans ?_
    rw [hKp] at h5 ⊢
    have e7 : 2 * 2.2 * (1.0004 * (0.0596 * C / u)) = 2 * 2.2 * 1.0004 * 0.0596 * C / u := by
      ring
    rw [e7, div_le_iff₀ hu0]
    have h7 : C ≤ 1.0091 * alphaL τ ℓ * (1.0755 * u ^ 2) / 3.0276 := by
      refine hCb.trans (div_le_div_of_nonneg_right ?_ (by norm_num))
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hu3 : 27 * u ^ 2 ≤ u ^ 3 := by nlinarith [sq_nonneg u]
    have s0 : 0.001 * alphaL τ ℓ * (2.2 * u ^ 2 * 3.29) * u ≤ 0.001 * alphaL τ ℓ * Xu u * u :=
      mul_le_mul_of_nonneg_right h5 hu0.le
    have s1 : 2 * 2.2 * 1.0004 * 0.0596 * C ≤
        2 * 2.2 * 1.0004 * 0.0596 * (1.0091 * alphaL τ ℓ * (1.0755 * u ^ 2) / 3.0276) :=
      mul_le_mul_of_nonneg_left h7 (by norm_num)
    have s2 : 2 * 2.2 * 1.0004 * 0.0596 * (1.0091 * alphaL τ ℓ * (1.0755 * u ^ 2) / 3.0276) ≤
        0.0946 * (alphaL τ ℓ * u ^ 2) := by
      have e : 2 * 2.2 * 1.0004 * 0.0596 * (1.0091 * alphaL τ ℓ * (1.0755 * u ^ 2) / 3.0276) =
          (2 * 2.2 * 1.0004 * 0.0596 * 1.0091 * 1.0755 / 3.0276) * (alphaL τ ℓ * u ^ 2) := by
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have s3 : 0.0946 * (alphaL τ ℓ * u ^ 2) ≤ 0.001 * alphaL τ ℓ * (2.2 * u ^ 2 * 3.29) * u := by
      have : 27 * (alphaL τ ℓ * u ^ 2) ≤ alphaL τ ℓ * u ^ 3 := by
        have := mul_le_mul_of_nonneg_left hu3 hα0; linarith
      have e : 0.001 * alphaL τ ℓ * (2.2 * u ^ 2 * 3.29) * u =
          0.001 * 2.2 * 3.29 * (alphaL τ ℓ * u ^ 3) := by ring
      rw [e]; nlinarith
    linarith
  have hlX : 0 ≤ 0.001 * lamL τ ℓ * Xu u := by positivity
  have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)) +
      110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u) + 0 + (0 / 4.5888 +
        0 / 4.5888 ^ 2 + 2 * C / 4.5888 ^ 3 + 6 * (2 * C) / 4.5888 ^ 4 + 24 * C / 4.5888 ^ 5 +
          120 * 0 / 4.5888 ^ 6 + 720 * 0 / 4.5888 ^ 7) / u)) =
      2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 4.5888)))) +
      2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 4.5888 / u))) +
      2 * Kp * (1.0004 * (0 + (0 / 4.5888 + 0 / 4.5888 ^ 2 + 2 * C / 4.5888 ^ 3 +
      6 * (2 * C) / 4.5888 ^ 4 + 24 * C / 4.5888 ^ 5 + 120 * 0 / 4.5888 ^ 6 +
        720 * 0 / 4.5888 ^ 7) / u)) := by ring
  rw [e]
  have e2 : 0.001 * (lamL τ ℓ + alphaL τ ℓ) * Xu u =
      0.001 * lamL τ ℓ * Xu u + 0.001 * alphaL τ ℓ * Xu u := by ring
  rw [e2]
  linarith

set_option maxHeartbeats 800000 in
/-- **(e)**, `u < 27`. -/
lemma LargeRange.remE_small (hR : LargeRange τ ℓ u) (h27 : u < 27) :
    ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤ lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 200000000000 / ℓ +
      Real.exp (-(u0 ℓ / 3)) := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hu0 : 0 < u := by linarith
  have huu0 := hR.u0_ge
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hsm : u < u0 ℓ - 2 := by linarith
  set dd := u0 ℓ - 0.26 - u
  have hdd : 0.9991 * u0 ℓ ≤ dd := by simp only [dd]; linarith
  set C := 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / dd ^ 4
  have hdd0 : 0 < dd := by linarith
  have hC : 0 ≤ C := by positivity
  have hr : 0.9988 ≤ Dickman.ratio (u - 1) - 0.0012 := by linarith [hR.r0_ge_one]
  have hE := hR.E3_gen (rmin := 0.9988) (Ah := 0) (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 0)
    (b4 := C) (b5 := 2 * C) (b6 := C) (by norm_num) hr le_rfl le_rfl le_rfl le_rfl le_rfl hC
    (by positivity) hC
    (fun w _ hwu => hR.aTerm_head_small hsm hwu)
    (by
      intro w huw _
      have := hR.aTerm_tail_small hsm 4 huw
      have e : 1.0091 * alphaL τ ℓ * (1 + u) ^ 2 / (u0 ℓ - 0.26 - u) ^ 4 *
          ((1 + (w - u)) ^ 2 * (w - u) ^ 4) = 0 + 0 * (w - u) + 0 * (w - u) ^ 2 +
          0 * (w - u) ^ 3 + C * (w - u) ^ 4 + 2 * C * (w - u) ^ 5 + C * (w - u) ^ 6 := by
        simp only [C, dd]; ring
      linarith)
  refine hE.trans ?_
  have hM5 := M5_09988
  have hM50 : 0 ≤ M5 0.9988 := by unfold M5; norm_num
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have hKp : Kp = 2.2 := rfl
  have hPhi : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 0.9988)))) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) := by
    have hy : kappa τ / (u * ℓ) ≤ 0.0667 := by
      have := hR.kappa_le
      rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ hℓ0] at this; nlinarith
    have hur := hR.ur_ge
    have hm : (0.5446 : ℝ) ≤ 1 - 1 / (u * Dickman.ratio u) := by
      have : 1 / (u * Dickman.ratio u) ≤ 1 / 2.196 := one_div_le_one_div_of_le (by norm_num) hur
      norm_num at this ⊢; linarith
    have hc := hR.ellPhiBen_ge (c := 0.51) hm (by norm_num) hy (by norm_num)
    have h1 : 1 + 1 / (u * 0.9988) ≤ 1.5007 := by
      have : 1 / (u * 0.9988) ≤ 1 / (2 * 0.9988) := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
      norm_num at this ⊢; linarith
    have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 0.9988)))) =
        (2 * Kp * 1.0004 * 4 * (1 + 1 / (u * 0.9988))) * (kappa τ / ℓ) := by ring
    rw [e]
    apply hR.phi_part (by rw [hKp]; positivity) hc
    rw [hKp]; nlinarith
  have hA : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 0.9988 / u))) ≤
      170197000000 / ℓ := by
    have h1 : 1 + M5 0.9988 / u ≤ 165 := by
      have : M5 0.9988 / u ≤ 328 / 2 := div_le_div₀ (by norm_num) hM5 (by norm_num) hu
      linarith
    have h2 : (1 + u) ^ 2 * Lam u ≤ 784 * (784 * 3.4658) := by
      have hΛ : Lam u ≤ 784 * 3.4658 := (Lam_mono (by linarith) h27.le).trans Lam_27_le
      have h3 : (1 + u) ^ 2 ≤ 784 := by nlinarith
      exact mul_le_mul h3 hΛ hΛ0 (by norm_num)
    have e : 2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 0.9988 / u))) =
        2 * Kp * 1.0004 * 110 * ((1 + u) ^ 2 * Lam u * (1 + M5 0.9988 / u)) / ℓ := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hℓ0.le
    have h4 : (1 + u) ^ 2 * Lam u * (1 + M5 0.9988 / u) ≤ 784 * (784 * 3.4658) * 165 :=
      mul_le_mul h2 h1 (by positivity) (by norm_num)
    rw [hKp]; nlinarith
  have ha : 2 * Kp * (1.0004 * (0 + (0 / 0.9988 + 0 / 0.9988 ^ 2 + 2 * 0 / 0.9988 ^ 3 +
      6 * 0 / 0.9988 ^ 4 + 24 * C / 0.9988 ^ 5 + 120 * (2 * C) / 0.9988 ^ 6 +
        720 * C / 0.9988 ^ 7) / u)) ≤ 1800 / ℓ := by
    have h1 : (0 / 0.9988 + 0 / 0.9988 ^ 2 + 2 * 0 / 0.9988 ^ 3 + 6 * 0 / 0.9988 ^ 4 +
        24 * C / 0.9988 ^ 5 + 120 * (2 * C) / 0.9988 ^ 6 + 720 * C / 0.9988 ^ 7) ≤ 992.1 * C := by
      norm_num; nlinarith
    have hdd4 : 0.99 * ℓ ≤ dd ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hdd 4
      rw [hR.ell_eq]; nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ u0 ℓ) 4]
    have hCb : C ≤ 1.0091 * 0.001 * 784 / (0.99 * ℓ) := by
      simp only [C]
      have hα := hR.alpha_le
      have h3 : (1 + u) ^ 2 ≤ 784 := by nlinarith
      apply div_le_div₀ (by positivity) _ (by positivity) hdd4
      have := mul_le_mul hα h3 (by positivity) (by norm_num)
      nlinarith
    rw [zero_add]
    have h2 : 2 * Kp * (1.0004 * ((0 / 0.9988 + 0 / 0.9988 ^ 2 + 2 * 0 / 0.9988 ^ 3 +
        6 * 0 / 0.9988 ^ 4 + 24 * C / 0.9988 ^ 5 + 120 * (2 * C) / 0.9988 ^ 6 +
          720 * C / 0.9988 ^ 7) / u)) ≤ 2 * Kp * (1.0004 * (992.1 * C / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by rw [hKp]; norm_num)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc _ ≤ 992.1 * C / u := div_le_div_of_nonneg_right h1 hu0.le
        _ ≤ 992.1 * C / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hu
    refine h2.trans ?_
    rw [hKp]
    have e : 1.0091 * 0.001 * 784 / (0.99 * ℓ) = (1.0091 * 0.001 * 784 / 0.99) / ℓ := by
      field_simp
    rw [e] at hCb
    have h3 : 2 * 2.2 * (1.0004 * (992.1 * C / 2)) ≤
        2 * 2.2 * (1.0004 * (992.1 * ((1.0091 * 0.001 * 784 / 0.99) / ℓ) / 2)) := by
      gcongr
    refine h3.trans (le_of_eq_of_le ?_ (div_le_div_of_nonneg_right (by norm_num :
      2 * 2.2 * (1.0004 * (992.1 * (1.0091 * 0.001 * 784 / 0.99) / 2)) ≤ (1800 : ℝ)) hℓ0.le))
    field_simp
  have hE0 := Real.exp_pos (-(u0 ℓ / 3))
  have e : 2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 0.9988)) +
      110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 0.9988 / u) + 0 + (0 / 0.9988 + 0 / 0.9988 ^ 2 +
        2 * 0 / 0.9988 ^ 3 + 6 * 0 / 0.9988 ^ 4 + 24 * C / 0.9988 ^ 5 +
          120 * (2 * C) / 0.9988 ^ 6 + 720 * C / 0.9988 ^ 7) / u)) =
      2 * Kp * (1.0004 * (4 * kappa τ / ℓ * (1 + 1 / (u * 0.9988)))) +
      2 * Kp * (1.0004 * (110 * (1 + u) ^ 2 * Lam u / ℓ * (1 + M5 0.9988 / u))) +
      2 * Kp * (1.0004 * (0 + (0 / 0.9988 + 0 / 0.9988 ^ 2 + 2 * 0 / 0.9988 ^ 3 +
      6 * 0 / 0.9988 ^ 4 + 24 * C / 0.9988 ^ 5 + 120 * (2 * C) / 0.9988 ^ 6 +
        720 * C / 0.9988 ^ 7) / u)) := by ring
  rw [e]
  have h4 : 170197000000 / ℓ + 1800 / ℓ ≤ 200000000000 / ℓ := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hℓ0.le
  linarith

/-- **Remainder (e)** (lines 461-477). -/
theorem remE : RemE := by
  intro τ ℓ u hR
  exact ⟨fun h27 hbig => hR.remE_big h27 hbig, fun h27 hsm => hR.remE_mid h27 hsm,
    fun h27 => hR.remE_small h27⟩

end BSaias.Large

end
