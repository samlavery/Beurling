module

public import RequestProject.Beurling.Noise.BSZ2Main

/-!
# The error terms `E₁`, `E₂`, `E₃` in region Z2 (Theorem 5.6, Step 7(iii))

Under `Z2Hyp τ ℓ u`, with the paper's cut-off:

* `E1_le` : `E₁ ≤ 2K' u² r₀ e^{β_I - α}/ℓ` (`BSCert.Z2.E1`), using `D(u-1) ≤ β_I - α` and
  `ρ(u-2)/ρ(u-1) = (u-1) r(u-1)`;
* `E2_le` : `E₂ ≤ (K'/ℓ)(u/(u-1))((u-1)e^{β_I} + e^{β_II}(1/(r₀ - γ₁) + q))` (`BSCert.Z2.E2`),
  using `(1+w)/w ≤ u/(u-1)` and `∫_{u-1}^u ρ(w-1) dw = (u-1)ρ(u-1)`;
* `E3_le` : `E₃ ≤ 2K'(η̄(u,v)e^{β_I} + (e^{β_II}/u)(η̄(u+60, v+60)/(r₀-γ₁) + η̄(Ū, Ū-u₀) q))`
  (`BSCert.Z2.E3`), using `η_f ≤ η̄` and the monotonicity of `η̄`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace BSaias

open BSCert.Z2 (betaI betaII alpha gamma1 gammaMax qq eta)

namespace Z2Hyp

variable {τ ℓ u : ℝ} (h : Z2Hyp τ ℓ u)
include h

/-! ## `E₁` -/

theorem E1_le : E1term τ ℓ u (paperCut τ ℓ) ≤ BSCert.Z2.E1 Dickman.ratio ℓ u := by
  have hu := h.hu1
  have hℓ := h.ℓ_pos
  unfold E1term BSCert.Z2.E1
  rw [h.wlo_eq, show 1 + (u - 1) = u by ring]
  have hD := D_partI (τ := τ) h.hτ hℓ hu le_rfl (by linarith : u - 1 ≤ u)
  rw [show u - (u - 1) = 1 by ring, mul_one] at hD
  have hg : gfun τ ℓ u (paperCut τ ℓ) (u - 1) ≤
      (u - 1) * Dickman.ratio (u - 1) * Real.exp (betaI ℓ u - alpha ℓ u) := by
    refine (h.gfun_le _ _).trans ?_
    unfold gBase
    have hr : Dickman.rho (u - 1 - 1) / Dickman.rho (u - 1) = (u - 1) * Dickman.ratio (u - 1) := by
      unfold Dickman.ratio; have := h.rho0_pos; have : u - 1 ≠ 0 := by linarith
      field_simp
    rw [hr]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD)
    have := h.r0_ge; nlinarith
  have hK : (0 : ℝ) ≤ 2 * Kp * u ^ 2 := by unfold Kp; positivity
  calc 2 * Kp * u ^ 2 * gfun τ ℓ u (paperCut τ ℓ) (u - 1) / ((u - 1) * ℓ)
      ≤ 2 * Kp * u ^ 2 * ((u - 1) * Dickman.ratio (u - 1) * Real.exp (betaI ℓ u - alpha ℓ u)) /
        ((u - 1) * ℓ) := by
        apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hK)
        have : 0 < (u - 1) * ℓ := by apply mul_pos (by linarith) hℓ
        exact this.le
    _ = _ := by
        unfold Kp
        have : u - 1 ≠ 0 := by linarith
        field_simp

/-! ## `E₂` -/

lemma frac_le {w : ℝ} (hw : u - 1 ≤ w) : (1 + w) / w ≤ u / (u - 1) := by
  have hu := h.hu1
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma piece_E2 {w : ℝ} (hw : u - 1 ≤ w) :
    gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w ≤ u / (u - 1) * gBase τ ℓ u w := by
  have hw0 : 0 < w := by linarith [h.hu1]
  have hg := h.gfun_nonneg (paperCut τ ℓ) w
  have hf := h.frac_le hw
  calc gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w = gfun τ ℓ u (paperCut τ ℓ) w * ((1 + w) / w) := by
        ring
    _ ≤ gBase τ ℓ u w * (u / (u - 1)) :=
        mul_le_mul (h.gfun_le _ _) hf (by positivity) (h.gBase_nonneg w)
    _ = _ := by ring

theorem E2_le : E2term τ ℓ u (paperCut τ ℓ) ≤ BSCert.Z2.E2 Dickman.ratio ℓ u := by
  have hu := h.hu1
  have hu0 : 0 < u := by linarith
  have hℓ := h.ℓ_pos
  have hb1 := h.u_le_b
  have hb2 := h.b_le_U
  have hk1 := h.gamma1_lt
  have hkm := h.gammaMax_lt
  have hρ0 := h.rho0_pos
  have hc : 0 ≤ u / (u - 1) := div_nonneg (by linarith) (by linarith)
  have hq : 0 < qq Dickman.ratio ℓ u := by unfold qq; exact div_pos (Real.exp_pos _) hkm
  unfold E2term BSCert.Z2.E2
  rw [h.wlo_eq, h.split3 h.intE2]
  -- piece 1
  have i1 : ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w ≤
      u / (u - 1) * (Real.exp (betaI ℓ u) * (u - 1)) := by
    have hR := intervalIntegrable_rho_shift (u - 1) u
    calc ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w
        ≤ ∫ w in (u - 1)..u, (u / (u - 1) * (Real.exp (betaI ℓ u) / Dickman.rho (u - 1)) *
            Dickman.rho (w - 1)) := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (h.sub_int h.intE2 le_rfl (by linarith) h.hu2) (hR.const_mul _)
          intro w hw
          refine (h.piece_E2 hw.1).trans ?_
          have := h.gBase_partI' hw.1 hw.2
          have e : u / (u - 1) * (Real.exp (betaI ℓ u) / Dickman.rho (u - 1)) *
              Dickman.rho (w - 1) = u / (u - 1) * (Dickman.rho (w - 1) / Dickman.rho (u - 1) *
                Real.exp (betaI ℓ u)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc
      _ = _ := by
          rw [intervalIntegral.integral_const_mul, mass_flat hu]
          field_simp
  -- piece 2
  have i2 : ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w ≤
      u / (u - 1) * (Real.exp (betaII ℓ u) * (1 / (Dickman.ratio (u - 1) - gamma1 ℓ u))) := by
    have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gamma1 ℓ u) u u h.bpt
    calc ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w
        ≤ ∫ w in u..h.bpt, (u / (u - 1) * Real.exp (betaII ℓ u) *
            Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (w - u)))) := by
          apply intervalIntegral.integral_mono_on hb1
            (h.sub_int h.intE2 (by linarith) hb1 hb2) (hE.const_mul _)
          intro w hw
          refine (h.piece_E2 (by linarith [hw.1])).trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (h.gBase_partII_exp hw.1 (h.D_on_b hw.1 hw.2)) hc
      _ ≤ u / (u - 1) * Real.exp (betaII ℓ u) *
            (Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (u - u))) /
              (Dickman.ratio (u - 1) - gamma1 ℓ u)) := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_expl_le hk1) (by positivity)
      _ = _ := by simp; ring
  -- piece 3
  have i3 : ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w ≤
      u / (u - 1) * (Real.exp (betaII ℓ u) * qq Dickman.ratio ℓ u) := by
    rcases le_or_gt (Uf τ ℓ) (u + 60) with hU | hU
    · rw [show h.bpt = Uf τ ℓ from min_eq_right hU, intervalIntegral.integral_same]
      positivity
    · have hbU : h.bpt = u + 60 := min_eq_left hU.le
      have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gammaMax ℓ u) u h.bpt (Uf τ ℓ)
      calc ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w
          ≤ ∫ w in h.bpt..Uf τ ℓ, (u / (u - 1) * Real.exp (betaII ℓ u) *
              Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (w - u)))) := by
            apply intervalIntegral.integral_mono_on hb2
              (h.sub_int h.intE2 (by linarith) hb2 le_rfl) (hE.const_mul _)
            intro w hw
            have hw1 : u ≤ w := by linarith [hw.1]
            refine (h.piece_E2 (by linarith)).trans ?_
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (h.gBase_partII_exp hw1 (h.D_on_U hw1 hw.2)) hc
        _ ≤ u / (u - 1) * Real.exp (betaII ℓ u) *
              (Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (h.bpt - u))) /
                (Dickman.ratio (u - 1) - gammaMax ℓ u)) := by
            rw [intervalIntegral.integral_const_mul]
            exact mul_le_mul_of_nonneg_left (integral_expl_le hkm) (by positivity)
        _ = _ := by unfold qq; rw [hbU]; ring_nf
  have hK : (0 : ℝ) ≤ Kp / ℓ := by unfold Kp; positivity
  calc Kp / ℓ * ((∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w) +
        (∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w) +
        ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w)
      ≤ Kp / ℓ * (u / (u - 1) * (Real.exp (betaI ℓ u) * (u - 1)) +
        u / (u - 1) * (Real.exp (betaII ℓ u) * (1 / (Dickman.ratio (u - 1) - gamma1 ℓ u))) +
        u / (u - 1) * (Real.exp (betaII ℓ u) * qq Dickman.ratio ℓ u)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add i1 i2) i3) hK
    _ = _ := by unfold Kp; ring

/-! ## `E₃` -/

lemma eta_bound1 {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    etaF τ ℓ w ≤ eta ℓ u u (u - u0 ℓ) :=
  (etaF_le_eta (by linarith [h.hτ]) h.hℓ h.hu1 hw1).trans
    (eta_mono h.ℓ_pos h.hu1 (by linarith [h.hu1]) hwu (by linarith))

lemma eta_bound2 {w : ℝ} (hw1 : u ≤ w) (hw2 : w ≤ u + 60) :
    etaF τ ℓ w ≤ eta ℓ u (u + 60) (u - u0 ℓ + 60) :=
  (etaF_le_eta (by linarith [h.hτ]) h.hℓ h.hu1 (by linarith)).trans
    (eta_mono h.ℓ_pos h.hu1 (by linarith [h.hu1]) hw2 (by linarith))

lemma eta_bound3 {w : ℝ} (hw1 : u ≤ w) (hw2 : w ≤ Uf τ ℓ) :
    etaF τ ℓ w ≤ eta ℓ u (BSCert.Z2.Ubar ℓ) (BSCert.Z2.UbMu0 ℓ) := by
  have hU := h.U_le_Ubar
  refine (etaF_le_eta (by linarith [h.hτ]) h.hℓ h.hu1 (by linarith)).trans
    (eta_mono h.ℓ_pos h.hu1 (by linarith [h.hu1]) (hw2.trans hU) ?_)
  have : BSCert.Z2.Ubar ℓ = u0 ℓ + BSCert.Z2.UbMu0 ℓ := rfl
  linarith

lemma etaF_nonneg {w : ℝ} (hw : u - 1 ≤ w) : 0 ≤ etaF τ ℓ w := by
  have hℓ := h.ℓ_pos
  have hw0 : 0 < w := by linarith [h.hu1]
  have hm : 0 < mOf ℓ w := mOf_pos hℓ hw0
  have h1 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ dpos (mOf ℓ w) w := le_max_right _ _
  have h3 : 0 < u0 (mOf ℓ w) := u0_pos hm
  have h4 : 0 ≤ τ := by linarith [h.hτ]
  have h5 : 0 ≤ BSCert.Z2.A (mOf ℓ w) w := by unfold BSCert.Z2.A; positivity
  unfold etaF kappa
  positivity

/-- `g η_f/w ≤ η̄ (g/w) ≤ η̄ (gBase/w)` for a majorant `η̄ ≥ η_f`. -/
lemma piece_E3 {w e : ℝ} (hw : u - 1 ≤ w) (he : etaF τ ℓ w ≤ e) :
    gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w ≤ e * (gBase τ ℓ u w / w) := by
  have hw0 : 0 < w := by linarith [h.hu1]
  have hg := h.gfun_nonneg (paperCut τ ℓ) w
  have he0 : 0 ≤ e := (h.etaF_nonneg hw).trans he
  calc gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w =
        (gfun τ ℓ u (paperCut τ ℓ) w / w) * etaF τ ℓ w := by ring
    _ ≤ (gfun τ ℓ u (paperCut τ ℓ) w / w) * e :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ (gBase τ ℓ u w / w) * e :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (h.gfun_le _ _) hw0.le) he0
    _ = _ := by ring

theorem E3_le : E3term τ ℓ u (paperCut τ ℓ) ≤ BSCert.Z2.E3 Dickman.ratio ℓ u := by
  have hu := h.hu1
  have hu0 : 0 < u := by linarith
  have hℓ := h.ℓ_pos
  have hb1 := h.u_le_b
  have hb2 := h.b_le_U
  have hk1 := h.gamma1_lt
  have hkm := h.gammaMax_lt
  have hρ0 := h.rho0_pos
  have hq : 0 < qq Dickman.ratio ℓ u := by unfold qq; exact div_pos (Real.exp_pos _) hkm
  set e1 := eta ℓ u u (u - u0 ℓ)
  set e2 := eta ℓ u (u + 60) (u - u0 ℓ + 60)
  set e3 := eta ℓ u (BSCert.Z2.Ubar ℓ) (BSCert.Z2.UbMu0 ℓ)
  have he1 : 0 ≤ e1 := eta_nonneg hℓ hu (by linarith)
  have he2 : 0 ≤ e2 := eta_nonneg hℓ hu (by linarith)
  have he3 : 0 ≤ e3 := eta_nonneg hℓ hu (by
    have := h.U_le_Ubar; have := Uf_pos (τ := τ) hℓ; linarith)
  unfold E3term BSCert.Z2.E3
  rw [h.wlo_eq, h.split3 h.intE3]
  -- piece 1
  have i1 : ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w ≤
      e1 * Real.exp (betaI ℓ u) := by
    have hPi := intervalIntegrable_P (a := u - 1) (b := u) (by linarith) (by linarith)
    calc ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w
        ≤ ∫ w in (u - 1)..u, (e1 * (Real.exp (betaI ℓ u) / Dickman.rho (u - 1)) *
            (Dickman.rho (w - 1) / w)) := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (h.sub_int h.intE3 le_rfl (by linarith) h.hu2) (hPi.const_mul _)
          intro w hw
          have hw0 : 0 < w := by linarith [hw.1]
          refine (h.piece_E3 hw.1 (h.eta_bound1 hw.1 hw.2)).trans ?_
          have := div_le_div_of_nonneg_right (h.gBase_partI' hw.1 hw.2) hw0.le
          calc e1 * (gBase τ ℓ u w / w) ≤ e1 * (Dickman.rho (w - 1) / Dickman.rho (u - 1) *
                Real.exp (betaI ℓ u) / w) := mul_le_mul_of_nonneg_left this he1
            _ = _ := by field_simp
      _ = e1 * Real.exp (betaI ℓ u) * (1 - Dickman.rho u / Dickman.rho (u - 1)) := by
          rw [intervalIntegral.integral_const_mul, mass_I hu]
          field_simp
      _ ≤ e1 * Real.exp (betaI ℓ u) := by
          have : 0 ≤ Dickman.rho u / Dickman.rho (u - 1) := by
            have := Dickman.rho_pos u; positivity
          have : 0 ≤ e1 * Real.exp (betaI ℓ u) := by positivity
          nlinarith
  -- piece 2
  have i2 : ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w ≤
      Real.exp (betaII ℓ u) / u * (e2 / (Dickman.ratio (u - 1) - gamma1 ℓ u)) := by
    have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gamma1 ℓ u) u u h.bpt
    calc ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w
        ≤ ∫ w in u..h.bpt, (e2 * Real.exp (betaII ℓ u) / u *
            Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (w - u)))) := by
          apply intervalIntegral.integral_mono_on hb1
            (h.sub_int h.intE3 (by linarith) hb1 hb2) (hE.const_mul _)
          intro w hw
          have hw0 : 0 < w := by linarith [hw.1]
          refine (h.piece_E3 (by linarith [hw.1]) (h.eta_bound2 hw.1
            (hw.2.trans h.b_le_60))).trans ?_
          have hgb := h.gBase_partII_exp hw.1 (h.D_on_b hw.1 hw.2)
          have hgw : gBase τ ℓ u w / w ≤ gBase τ ℓ u w / u :=
            div_le_div_of_nonneg_left (h.gBase_nonneg w) hu0 hw.1
          have := div_le_div_of_nonneg_right hgb hu0.le
          calc e2 * (gBase τ ℓ u w / w) ≤ e2 * (Real.exp (betaII ℓ u) *
                Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (w - u))) / u) :=
                mul_le_mul_of_nonneg_left (hgw.trans this) he2
            _ = _ := by ring
      _ ≤ e2 * Real.exp (betaII ℓ u) / u *
            (Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (u - u))) /
              (Dickman.ratio (u - 1) - gamma1 ℓ u)) := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_expl_le hk1) (by positivity)
      _ = _ := by simp; ring
  -- piece 3
  have i3 : ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w ≤
      Real.exp (betaII ℓ u) / u * (e3 * qq Dickman.ratio ℓ u) := by
    rcases le_or_gt (Uf τ ℓ) (u + 60) with hU | hU
    · rw [show h.bpt = Uf τ ℓ from min_eq_right hU, intervalIntegral.integral_same]
      positivity
    · have hbU : h.bpt = u + 60 := min_eq_left hU.le
      have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gammaMax ℓ u) u h.bpt
        (Uf τ ℓ)
      calc ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w
          ≤ ∫ w in h.bpt..Uf τ ℓ, (e3 * Real.exp (betaII ℓ u) / u *
              Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (w - u)))) := by
            apply intervalIntegral.integral_mono_on hb2
              (h.sub_int h.intE3 (by linarith) hb2 le_rfl) (hE.const_mul _)
            intro w hw
            have hw1 : u ≤ w := by linarith [hw.1]
            refine (h.piece_E3 (by linarith) (h.eta_bound3 hw1 hw.2)).trans ?_
            have hgb := h.gBase_partII_exp hw1 (h.D_on_U hw1 hw.2)
            have hgw : gBase τ ℓ u w / w ≤ gBase τ ℓ u w / u :=
              div_le_div_of_nonneg_left (h.gBase_nonneg w) hu0 hw1
            have := div_le_div_of_nonneg_right hgb hu0.le
            calc e3 * (gBase τ ℓ u w / w) ≤ e3 * (Real.exp (betaII ℓ u) *
                  Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (w - u))) / u) :=
                  mul_le_mul_of_nonneg_left (hgw.trans this) he3
              _ = _ := by ring
        _ ≤ e3 * Real.exp (betaII ℓ u) / u *
              (Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (h.bpt - u))) /
                (Dickman.ratio (u - 1) - gammaMax ℓ u)) := by
            rw [intervalIntegral.integral_const_mul]
            exact mul_le_mul_of_nonneg_left (integral_expl_le hkm) (by positivity)
        _ = _ := by unfold qq; rw [hbU]; ring_nf
  have hK : (0 : ℝ) ≤ 2 * Kp := by unfold Kp; positivity
  calc 2 * Kp * ((∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w) +
        (∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w) +
        ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w)
      ≤ 2 * Kp * (e1 * Real.exp (betaI ℓ u) +
        Real.exp (betaII ℓ u) / u * (e2 / (Dickman.ratio (u - 1) - gamma1 ℓ u)) +
        Real.exp (betaII ℓ u) / u * (e3 * qq Dickman.ratio ℓ u)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add i1 i2) i3) hK
    _ = _ := by unfold Kp; ring

end Z2Hyp

end BSaias

end
