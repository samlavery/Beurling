module

public import RequestProject.Beurling.Noise.BSZ1Size

/-!
# Region Z1 of Theorem 5.6: pointwise bounds

For `τ ≥ 10⁸`, `ℓ > 30τ`, `0 ≤ u < 2` and `w ∈ [w_lo, U(ℓ)]` (so `w ≥ 0.9`):

* `Q(m, w) ≤ 0.5 (1+w)` and `ℓ Q(m, w) ≤ 25 (1+w)⁶` (`Qm_le`, `ell_Qm_le`);
* `ℓ η_f ≤ 2 (1+w)⁶` (`ell_etaF_le`);
* `0 ≤ g(w) ≤ ρ(w-1) e^{-κ_Φ/(wℓ)} e^{Q(m,w)}` (`gfun_le`), since `ρ(u-1) = 1` and
  `Q(ℓ, u) ≥ 0`.

Combining, with `F(w) = ρ(w-1)(1+w)⁶ e^{(1+w)/2}/w` (`Fz1`):

* `g/w ≤ ρ(w-1) e^{-κ_Φ/(wℓ)}/w + (25/ℓ) F`, `g(1+w)/w ≤ F`, `g η_f/w ≤ (2/ℓ) F`.

These are cruder than the paper's bounds of Step 7(i) (`D' ≤ 9.7·10⁻⁴` on `[w_lo, 40]`, the
`h`-moments), but they are uniform in `ℓ`, and the final margin `0.22τ` absorbs them.
-/

@[expose] public section

open Real

namespace BSaias

namespace Z1

/-- The common majorant `F(w) = ρ(w-1)(1+w)⁶ e^{(1+w)/2}/w`. -/
noncomputable def Fz1 (w : ℝ) : ℝ :=
  Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)) / w

variable {τ ℓ u w : ℝ}

/-- The standing hypotheses of region Z1 at a point `w`. -/
structure Hyp (τ ℓ u w : ℝ) : Prop where
  hτ : 100000000 ≤ τ
  hℓ : 30 * τ < ℓ
  hu0 : 0 ≤ u
  hu2 : u < 2
  hw1 : wlo τ ℓ u ≤ w
  hw2 : w ≤ Uf τ ℓ

namespace Hyp

variable (h : Hyp τ ℓ u w)
include h

lemma ell_pos : 0 < ℓ := Z1.ell_pos h.hτ h.hℓ

lemma w_ge : 0.9 ≤ w := (w1_ge h.hτ h.hℓ).trans ((le_max_right _ _).trans h.hw1)

lemma w_pos : 0 < w := by linarith [h.w_ge]

lemma m_ge : 0.47 * ℓ ≤ mOf ℓ w := by
  unfold mOf
  have := h.w_ge; have := h.ell_pos
  rw [le_div_iff₀ (by linarith)]; nlinarith

lemma m_pos : 0 < mOf ℓ w := by have := h.m_ge; have := h.ell_pos; linarith

lemma m_ge_one : 1 ≤ mOf ℓ w := by
  have := h.m_ge; have := ell_gt h.hτ h.hℓ; linarith

lemma ell_div_m : ℓ / mOf ℓ w ≤ 1 / 0.47 := by
  rw [div_le_div_iff₀ h.m_pos (by norm_num)]; have := h.m_ge; linarith

lemma sqrt_m_ge : 0.68 * √ℓ ≤ √(mOf ℓ w) := by
  have h1 : √(0.47 * ℓ) ≤ √(mOf ℓ w) := Real.sqrt_le_sqrt h.m_ge
  rw [Real.sqrt_mul (by norm_num)] at h1
  have h2 : 0.68 ≤ √(0.47 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have := Real.sqrt_nonneg ℓ
  nlinarith

lemma u0m_ge_one : 1 ≤ u0 (mOf ℓ w) := by
  show 1 ≤ √(√(mOf ℓ w))
  rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), one_pow,
    Real.le_sqrt (by norm_num) h.m_pos.le, one_pow]
  exact h.m_ge_one

lemma sqrt_m_ge_one : 1 ≤ √(mOf ℓ w) := by
  rw [Real.le_sqrt (by norm_num) h.m_pos.le, one_pow]; exact h.m_ge_one

lemma rho_u : Dickman.rho (u - 1) = 1 := Dickman.rho_of_le_one (by linarith [h.hu2])

lemma A_le_lin : BSCert.Z2.A (mOf ℓ w) w ≤ 0.34 * (1 + w) := by
  unfold BSCert.Z2.A
  have hU := (U_size_both h.hτ h.hℓ).1
  have hw0 := h.w_pos
  have hwU := h.hw2
  have hU0 : 0 ≤ Uf τ ℓ := le_trans (u0_nonneg ℓ) (u0_le_U τ ℓ)
  have h3 : (1 + w) ^ 3 ≤ (1 + Uf τ ℓ) ^ 2 * (1 + w) := by
    have : (1 + w) ^ 2 ≤ (1 + Uf τ ℓ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  have hl : Real.log (2 + w) ≤ Real.log (3 + Uf τ ℓ) := Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hm := h.m_ge
  have hℓ0 := h.ell_pos
  rw [div_le_iff₀ h.m_pos]
  calc 11 * (1 + w) ^ 3 * Real.log (2 + w)
      ≤ 11 * ((1 + Uf τ ℓ) ^ 2 * (1 + w)) * Real.log (3 + Uf τ ℓ) := by
        apply mul_le_mul _ hl hl0 (by positivity)
        linarith
    _ = 11 * (1 + w) * ((1 + Uf τ ℓ) ^ 2 * Real.log (3 + Uf τ ℓ)) := by ring
    _ ≤ 11 * (1 + w) * (0.0145 * ℓ) := mul_le_mul_of_nonneg_left hU (by positivity)
    _ ≤ 0.34 * (1 + w) * mOf ℓ w := by nlinarith

lemma aQ_le_sq : aQ (mOf ℓ w) w ≤ w ^ 2 / (2 * √(mOf ℓ w)) := by
  unfold aQ
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h0 := u0_nonneg (mOf ℓ w)
  have hw := h.w_pos
  rcases le_total (w - u0 (mOf ℓ w)) 0 with hc | hc
  · rw [max_eq_right hc, zero_pow two_ne_zero]; positivity
  · rw [max_eq_left hc]; nlinarith

omit h in
lemma aQ_nonneg' : 0 ≤ aQ (mOf ℓ w) w := by unfold aQ; positivity

lemma aQ_le_lin : aQ (mOf ℓ w) w ≤ 0.03 * w := by
  refine h.aQ_le_sq.trans ?_
  have hU := (U_size_both h.hτ h.hℓ).2
  have hs := h.sqrt_m_ge
  have hw := h.w_pos
  have hsl : 0 < √ℓ := Real.sqrt_pos.mpr h.ell_pos
  have hm1 := h.sqrt_m_ge_one
  rw [div_le_iff₀ (by linarith)]
  have : w ≤ 0.036 * √ℓ := h.hw2.trans hU
  nlinarith

lemma A_nonneg' : 0 ≤ BSCert.Z2.A (mOf ℓ w) w := by
  unfold BSCert.Z2.A
  have hw := h.w_pos; have hm := h.m_pos
  have hl : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)) hl) hm.le

lemma Qm_nonneg : 0 ≤ Qf (mOf ℓ w) w := by
  unfold Qf; linarith [h.A_nonneg', aQ_nonneg' (ℓ := ℓ) (w := w)]

lemma Qm_le : Qf (mOf ℓ w) w ≤ 0.5 * (1 + w) := by
  unfold Qf; have := h.A_le_lin; have := h.aQ_le_lin; have := h.w_pos; linarith

lemma ell_A_le : ℓ * BSCert.Z2.A (mOf ℓ w) w ≤ 23.5 * (1 + w) ^ 4 := by
  unfold BSCert.Z2.A
  have hw := h.w_pos
  have hl : Real.log (2 + w) ≤ 1 + w := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + w by linarith); linarith
  have hl0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hd := h.ell_div_m
  have hm := h.m_pos
  have e : ℓ * (11 * (1 + w) ^ 3 * Real.log (2 + w) / mOf ℓ w) =
      11 * (1 + w) ^ 3 * Real.log (2 + w) * (ℓ / mOf ℓ w) := by ring
  rw [e]
  have h1 : 11 * (1 + w) ^ 3 * Real.log (2 + w) ≤ 11 * (1 + w) ^ 4 := by
    have : (1 + w) ^ 4 = (1 + w) ^ 3 * (1 + w) := by ring
    rw [this]; have := pow_pos (show 0 < 1 + w by linarith) 3; nlinarith
  calc 11 * (1 + w) ^ 3 * Real.log (2 + w) * (ℓ / mOf ℓ w) ≤ 11 * (1 + w) ^ 4 * (1 / 0.47) :=
        mul_le_mul h1 hd (div_nonneg h.ell_pos.le hm.le) (by positivity)
    _ ≤ 23.5 * (1 + w) ^ 4 := by nlinarith [pow_pos (show 0 < 1 + w by linarith) 4]

lemma ell_aQ_le : ℓ * aQ (mOf ℓ w) w ≤ 1.1 * w ^ 4 := by
  have hw := h.w_pos
  have hℓ0 := h.ell_pos
  rcases le_or_gt w (u0 (mOf ℓ w)) with hc | hc
  · have : aQ (mOf ℓ w) w = 0 := by
      unfold aQ; rw [max_eq_right (by linarith)]; simp
    rw [this, mul_zero]; positivity
  · -- `w > m^{1/4}` gives `√m < w²`, so `√ℓ ≤ w²/0.68`.
    have hsq : √(mOf ℓ w) < w ^ 2 := by
      have := u0_sq (mOf ℓ w)
      rw [← this]; exact pow_lt_pow_left₀ hc (u0_nonneg _) (by norm_num)
    have hs := h.sqrt_m_ge
    have hsl : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
    have hsl2 : √ℓ * √ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
    have hm1 := h.sqrt_m_ge_one
    calc ℓ * aQ (mOf ℓ w) w ≤ ℓ * (w ^ 2 / (2 * √(mOf ℓ w))) :=
          mul_le_mul_of_nonneg_left h.aQ_le_sq hℓ0.le
      _ ≤ ℓ * (w ^ 2 / (2 * (0.68 * √ℓ))) := by
          apply mul_le_mul_of_nonneg_left _ hℓ0.le
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
      _ = √ℓ * w ^ 2 / 1.36 := by nth_rewrite 1 [← hsl2]; field_simp; ring
      _ ≤ 1.1 * w ^ 4 := by
          rw [div_le_iff₀ (by norm_num)]
          have : √ℓ ≤ w ^ 2 / 0.68 := by rw [le_div_iff₀ (by norm_num)]; linarith
          have h2 : √ℓ * w ^ 2 ≤ w ^ 2 / 0.68 * w ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
          nlinarith [pow_pos hw 4]

lemma ell_Qm_le : ℓ * Qf (mOf ℓ w) w ≤ 25 * (1 + w) ^ 6 := by
  unfold Qf
  rw [mul_add]
  have h1 := h.ell_A_le
  have h2 := h.ell_aQ_le
  have hw := h.w_pos
  have h3 : w ^ 4 ≤ (1 + w) ^ 4 := pow_le_pow_left₀ hw.le (by linarith) 4
  have h4 : (1 + w) ^ 4 ≤ (1 + w) ^ 6 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have h5 : 0 ≤ (1 + w) ^ 4 := by positivity
  linarith

lemma etaF_nonneg : 0 ≤ etaF τ ℓ w := by
  unfold etaF dpos kappa
  have hw := h.w_pos
  have hm := h.m_pos
  have hℓ := h.ell_pos
  have hτ0 : 0 ≤ τ := by linarith [h.hτ]
  have : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hA := h.A_nonneg'
  have : 0 ≤ max (w - u0 (mOf ℓ w)) 0 := le_max_right _ _
  have := u0_nonneg (mOf ℓ w)
  simp only
  positivity

omit h in
lemma dpos_nonneg : 0 ≤ dpos (mOf ℓ w) w := le_max_right _ _

lemma dpos_le : dpos (mOf ℓ w) w ≤ w :=
  max_le (by linarith [u0_nonneg (mOf ℓ w)]) h.w_pos.le

lemma one_le_pw (k : ℕ) (hk : 1 ≤ k) : 1 + w ≤ (1 + w) ^ k := by
  have := pow_le_pow_right₀ (show 1 ≤ 1 + w by linarith [h.w_pos]) hk; simpa using this

lemma pw_mono {j k : ℕ} (hjk : j ≤ k) : (1 + w) ^ j ≤ (1 + w) ^ k :=
  pow_le_pow_right₀ (by linarith [h.w_pos]) hjk

lemma T1_le : ℓ * (kappa τ / mOf ℓ w ^ 2) ≤ 0.61 := by
  have hm := h.m_pos
  have hℓ0 := h.ell_pos
  have hk := kappa_div_le h.hτ h.hℓ
  have hk0 := kappa_div_nonneg h.hτ h.hℓ
  have hdiv := h.ell_div_m
  have e : ℓ * (kappa τ / mOf ℓ w ^ 2) = (kappa τ / ℓ) * (ℓ / mOf ℓ w) ^ 2 := by
    field_simp
  rw [e]
  have h0 : 0 ≤ ℓ / mOf ℓ w := div_nonneg hℓ0.le hm.le
  have h2 : (ℓ / mOf ℓ w) ^ 2 ≤ (1 / 0.47) ^ 2 := pow_le_pow_left₀ h0 hdiv 2
  have h3 : (kappa τ / ℓ) * (ℓ / mOf ℓ w) ^ 2 ≤ 0.13334 * (1 / 0.47) ^ 2 :=
    mul_le_mul hk h2 (by positivity) (by norm_num)
  linarith

lemma T2_le : ℓ * (BSCert.Z2.A (mOf ℓ w) w / mOf ℓ w) ≤ 0.01 * (1 + w) ^ 6 := by
  have hA := h.ell_A_le
  have hm := h.m_pos
  have hmge := h.m_ge
  have hℓ3 := ell_gt h.hτ h.hℓ
  have e : ℓ * (BSCert.Z2.A (mOf ℓ w) w / mOf ℓ w) =
      (ℓ * BSCert.Z2.A (mOf ℓ w) w) / mOf ℓ w := by ring
  rw [e, div_le_iff₀ hm]
  have p4 := h.pw_mono (show 4 ≤ 6 by norm_num)
  have p6 : 0 ≤ (1 + w) ^ 6 := by positivity
  have hm9 : 1000000000 ≤ mOf ℓ w := by linarith
  have := mul_le_mul_of_nonneg_left hm9 p6
  linarith

lemma T3_le : ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w))) +
    dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w)))) ≤ 1.1 * (1 + w) ^ 6 := by
  have hm := h.m_pos
  have hℓ0 := h.ell_pos
  have hw := h.w_pos
  have hd0 := dpos_nonneg (ℓ := ℓ) (w := w)
  have hdw := h.dpos_le
  have hu0m := h.u0m_ge_one
  have hsm := h.sqrt_m_ge_one
  have hdiv := h.ell_div_m
  set d := dpos (mOf ℓ w) w
  set m := mOf ℓ w
  have e1 : ℓ * (d / (4 * (m * u0 m)) + d ^ 2 / (4 * (m * √m))) =
      (ℓ / m) * (d / (4 * u0 m) + d ^ 2 / (4 * √m)) := by field_simp
  rw [e1]
  have a1 : d / (4 * u0 m) ≤ w / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have a2 : d ^ 2 / (4 * √m) ≤ w ^ 2 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : d ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hd0 hdw 2
    nlinarith [sq_nonneg w]
  have hb : d / (4 * u0 m) + d ^ 2 / (4 * √m) ≤ (1 + w) ^ 2 / 4 := by nlinarith
  have hb0 : 0 ≤ d / (4 * u0 m) + d ^ 2 / (4 * √m) := by positivity
  have p2 := h.pw_mono (show 2 ≤ 6 by norm_num)
  calc (ℓ / m) * (d / (4 * u0 m) + d ^ 2 / (4 * √m)) ≤ (1 / 0.47) * ((1 + w) ^ 2 / 4) :=
        mul_le_mul hdiv hb hb0 (by norm_num)
    _ ≤ 1.1 * (1 + w) ^ 6 := by linarith

lemma T4_le : ℓ * ((1 + w) ^ 2 / ℓ *
    (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / mOf ℓ w +
      dpos (mOf ℓ w) w / √(mOf ℓ w))) ≤ 0.01 * (1 + w) ^ 6 := by
  have hm := h.m_pos
  have hℓ0 := h.ell_pos
  have hw := h.w_pos
  have hd0 := dpos_nonneg (ℓ := ℓ) (w := w)
  have hdw := h.dpos_le
  have hmge := h.m_ge
  have hℓ3 := ell_gt h.hτ h.hℓ
  have hsm2 := h.sqrt_m_ge
  set d := dpos (mOf ℓ w) w
  set m := mOf ℓ w
  have e : ℓ * ((1 + w) ^ 2 / ℓ *
      (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m + d / √m)) =
      (1 + w) ^ 2 *
      (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m + d / √m) := by
    field_simp
  rw [e]
  have hl : Real.log (2 + w) ≤ 1 + w := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + w by linarith); linarith
  have hq : (1 + w) ^ 3 / (2 + w) ≤ (1 + w) ^ 3 := div_le_self (by positivity) (by linarith)
  have hc3 : 0 < (1 + w) ^ 3 := pow_pos (by linarith) 3
  have b1 : 11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m ≤
      0.001 * (1 + w) ^ 3 := by
    rw [div_le_iff₀ hm]
    have h33 : 3 * (1 + w) ^ 2 * Real.log (2 + w) ≤ 3 * (1 + w) ^ 3 := by
      have e3 : (1 + w) ^ 3 = (1 + w) ^ 2 * (1 + w) := by ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * (1 + w) ^ 2 by positivity)
      linarith
    have hm9 : 1000000000 ≤ m := by linarith
    have := mul_le_mul_of_nonneg_left hm9 hc3.le
    linarith
  have b2 : d / √m ≤ 0.001 * (1 + w) ^ 3 := by
    have hsl : 3000 ≤ √ℓ := by
      rw [Real.le_sqrt (by norm_num) hℓ0.le]; linarith
    have hsm3 : 2000 ≤ √m := by linarith
    rw [div_le_iff₀ (by linarith)]
    have p3 := h.one_le_pw 3 (by norm_num)
    have := mul_le_mul_of_nonneg_left hsm3 hc3.le
    linarith
  have hc : 11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m + d / √m ≤
      0.002 * (1 + w) ^ 3 := by linarith
  have hc0 : 0 ≤ (1 + w) ^ 2 := by positivity
  have e5 : (1 + w) ^ 2 * (0.002 * (1 + w) ^ 3) = 0.002 * (1 + w) ^ 5 := by ring
  have p5 := h.pw_mono (show 5 ≤ 6 by norm_num)
  have := mul_le_mul_of_nonneg_left hc hc0
  have hp : 0 ≤ (1 + w) ^ 5 := by positivity
  linarith

lemma ell_etaF_le : ℓ * etaF τ ℓ w ≤ 2 * (1 + w) ^ 6 := by
  have e : ℓ * etaF τ ℓ w = ℓ * (kappa τ / mOf ℓ w ^ 2) +
      ℓ * (BSCert.Z2.A (mOf ℓ w) w / mOf ℓ w) +
      ℓ * (dpos (mOf ℓ w) w / (4 * (mOf ℓ w * u0 (mOf ℓ w))) +
        dpos (mOf ℓ w) w ^ 2 / (4 * (mOf ℓ w * √(mOf ℓ w)))) +
      ℓ * ((1 + w) ^ 2 / ℓ *
        (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / mOf ℓ w +
          dpos (mOf ℓ w) w / √(mOf ℓ w))) := by
    unfold etaF; simp only; ring
  rw [e]
  have := h.T1_le; have := h.T2_le; have := h.T3_le; have := h.T4_le
  have p0 := h.pw_mono (show 0 ≤ 6 by norm_num)
  simp only [pow_zero] at p0
  linarith

lemma Q_ell_u_nonneg : 0 ≤ Qf ℓ u := by
  unfold Qf BSCert.Z2.A aQ
  have := h.ell_pos; have := h.hu0
  have : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  positivity

/-- `0 ≤ g(w) ≤ ρ(w-1) e^{-κ_Φ/(wℓ)} e^{Q(m,w)}` for any cut-off. -/
lemma gfun_le (I : Set ℝ) :
    0 ≤ gfun τ ℓ u I w ∧
      gfun τ ℓ u I w ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) *
        Real.exp (Qf (mOf ℓ w) w) := by
  unfold gfun
  have hr := Dickman.rho_pos (w - 1)
  have hb : 0 ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) *
      Real.exp (Qf (mOf ℓ w) w) := by positivity
  by_cases hI : w ∈ I
  · rw [Set.indicator_of_mem hI, h.rho_u, div_one]
    refine ⟨by positivity, ?_⟩
    unfold Dfun
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply Real.exp_le_exp.mpr
    linarith [h.Q_ell_u_nonneg]
  · rw [Set.indicator_of_notMem hI]; exact ⟨le_rfl, hb⟩

lemma Fz1_nonneg : 0 ≤ Fz1 w := by
  unfold Fz1; have := h.w_pos; have := Dickman.rho_pos (w - 1); positivity

omit h in
lemma exp_le_one_add (x : ℝ) (_hx : 0 ≤ x) : Real.exp x ≤ 1 + x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have := Real.exp_pos x
  nlinarith

/-- `g/w ≤ ρ(w-1) e^{-κ_Φ/(wℓ)}/w + (25/ℓ) F(w)`. -/
lemma bound_M (I : Set ℝ) :
    gfun τ ℓ u I w / w ≤
      Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) / w + 25 / ℓ * Fz1 w := by
  obtain ⟨-, hg⟩ := h.gfun_le I
  have hw := h.w_pos
  have hℓ := h.ell_pos
  have hr := Dickman.rho_pos (w - 1)
  set Q := Qf (mOf ℓ w) w
  have hQ0 : 0 ≤ Q := h.Qm_nonneg
  have hQ1 : Real.exp Q ≤ Real.exp (0.5 * (1 + w)) := Real.exp_le_exp.mpr h.Qm_le
  have hQ2 : Q ≤ 25 * (1 + w) ^ 6 / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith [h.ell_Qm_le]
  have hy : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ kappa τ / (w * ℓ) := by unfold kappa; have := h.hτ; positivity
    linarith
  have hy0 := Real.exp_pos (-(kappa τ / (w * ℓ)))
  have h1 := exp_le_one_add Q hQ0
  have key : gfun τ ℓ u I w ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) +
      Dickman.rho (w - 1) * (25 * (1 + w) ^ 6 / ℓ) * Real.exp (0.5 * (1 + w)) := by
    have hQe : Q * Real.exp Q ≤ 25 * (1 + w) ^ 6 / ℓ * Real.exp (0.5 * (1 + w)) :=
      mul_le_mul hQ2 hQ1 (Real.exp_pos _).le (by positivity)
    calc gfun τ ℓ u I w ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) *
          Real.exp Q := hg
      _ ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) * (1 + Q * Real.exp Q) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) +
          Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) * (Q * Real.exp Q) := by ring
      _ ≤ Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) +
          Dickman.rho (w - 1) * 1 * (25 * (1 + w) ^ 6 / ℓ * Real.exp (0.5 * (1 + w))) := by
          gcongr
      _ = _ := by ring
  have e : Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) / w + 25 / ℓ * Fz1 w =
      (Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) +
      Dickman.rho (w - 1) * (25 * (1 + w) ^ 6 / ℓ) * Real.exp (0.5 * (1 + w))) / w := by
    unfold Fz1; field_simp
  rw [e]
  exact div_le_div_of_nonneg_right key hw.le

/-- `g(1+w)/w ≤ F(w)`. -/
lemma bound_E2 (I : Set ℝ) : gfun τ ℓ u I w * (1 + w) / w ≤ Fz1 w := by
  obtain ⟨hg0, hg⟩ := h.gfun_le I
  have hw := h.w_pos
  have hr := Dickman.rho_pos (w - 1)
  have hQ1 : Real.exp (Qf (mOf ℓ w) w) ≤ Real.exp (0.5 * (1 + w)) := Real.exp_le_exp.mpr h.Qm_le
  have hy : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ kappa τ / (w * ℓ) := by unfold kappa; have := h.hτ; have := h.ell_pos; positivity
    linarith
  have hg' : gfun τ ℓ u I w ≤ Dickman.rho (w - 1) * Real.exp (0.5 * (1 + w)) := by
    calc gfun τ ℓ u I w ≤ _ := hg
      _ ≤ Dickman.rho (w - 1) * 1 * Real.exp (0.5 * (1 + w)) := by
          gcongr
      _ = _ := by ring
  unfold Fz1
  apply div_le_div_of_nonneg_right _ hw.le
  have h6 : 1 + w ≤ (1 + w) ^ 6 := by
    have := pow_le_pow_right₀ (show 1 ≤ 1 + w by linarith) (show 1 ≤ 6 by norm_num)
    simpa using this
  calc gfun τ ℓ u I w * (1 + w) ≤ Dickman.rho (w - 1) * Real.exp (0.5 * (1 + w)) * (1 + w) :=
        mul_le_mul_of_nonneg_right hg' (by linarith)
    _ ≤ Dickman.rho (w - 1) * Real.exp (0.5 * (1 + w)) * (1 + w) ^ 6 :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by ring

/-- `g η_f/w ≤ (2/ℓ) F(w)`. -/
lemma bound_E3 (I : Set ℝ) : gfun τ ℓ u I w * etaF τ ℓ w / w ≤ 2 / ℓ * Fz1 w := by
  obtain ⟨hg0, hg⟩ := h.gfun_le I
  have hw := h.w_pos
  have hℓ := h.ell_pos
  have hr := Dickman.rho_pos (w - 1)
  have hQ1 : Real.exp (Qf (mOf ℓ w) w) ≤ Real.exp (0.5 * (1 + w)) := Real.exp_le_exp.mpr h.Qm_le
  have hy : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ kappa τ / (w * ℓ) := by unfold kappa; have := h.hτ; positivity
    linarith
  have hg' : gfun τ ℓ u I w ≤ Dickman.rho (w - 1) * Real.exp (0.5 * (1 + w)) := by
    calc gfun τ ℓ u I w ≤ _ := hg
      _ ≤ Dickman.rho (w - 1) * 1 * Real.exp (0.5 * (1 + w)) := by
          gcongr
      _ = _ := by ring
  have he : etaF τ ℓ w ≤ 2 * (1 + w) ^ 6 / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith [h.ell_etaF_le]
  have he0 := h.etaF_nonneg
  unfold Fz1
  have e : 2 / ℓ * (Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)) / w) =
      Dickman.rho (w - 1) * Real.exp (0.5 * (1 + w)) * (2 * (1 + w) ^ 6 / ℓ) / w := by ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hw.le
  exact mul_le_mul hg' he he0 (by positivity)

end Hyp

end Z1

end BSaias

end
