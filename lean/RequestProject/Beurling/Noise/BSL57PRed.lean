module

public import RequestProject.Beurling.Noise.BSL57PPt
public import RequestProject.Beurling.Noise.BSL57PMom

/-!
# Lemma 5.7: reduction of `ρ₄` and `E₃` to integrals against `π`

* `rho4_le` : `ℓρ₄ ≤ (K'/ρ(u-1)) ∫_{(u-1,Ū]} (1+w) D'₊ e^{D'₊} ρ(w-1) dw/w` (from
  `1[w ≤ U(m)] e^D - 1 ≤ (e^{D'} - 1)₊ ≤ D'₊ e^{D'₊}`, lines 456-457);
* `E3_le` : `ℓE₃ ≤ (2K'/ρ(u-1)) ∫_{(u-1,Ū]} ℓ η_f e^{D'₊} ρ(w-1) dw/w` (line 461).
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

variable {τ ℓ u : ℝ}

lemma exp_sub_one_le (x : ℝ) : Real.exp x - 1 ≤ max x 0 * Real.exp (max x 0) := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx]; simp only [zero_mul]; linarith [Real.exp_le_one_iff.mpr hx]
  · rw [max_eq_left hx]
    have h := Real.add_one_le_exp (-x)
    have e : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]

lemma LargeRange.Uf_ge (hR : LargeRange τ ℓ u) : u - 1 ≤ Uf τ ℓ := by linarith [hR.u_le]

lemma integrableOn_Ioc_of_continuousAt {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ∀ w, 0 < w → ContinuousAt F w) : IntegrableOn F (Ioc a b) := by
  have hc : ContinuousOn F (Icc a b) := fun w hw =>
    (hF w (lt_of_lt_of_le ha hw.1)).continuousWithinAt
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

lemma continuousAt_rho_div {w : ℝ} (hw : 0 < w) :
    ContinuousAt (fun w => Dickman.rho (w - 1) / w) w :=
  ((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt).div
    continuousAt_id hw.ne'

lemma LargeRange.gfun_le (hR : LargeRange τ ℓ u) {I : Set ℝ} {w : ℝ} (hw : 0 < w) :
    0 ≤ gfun τ ℓ u I w ∧
      gfun τ ℓ u I w ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) *
        Real.exp (max (Dp ℓ u w) 0) := by
  have hρ := Dickman.rho_pos (u - 1)
  have hb0 : 0 ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) :=
    div_nonneg (Dickman.rho_pos _).le hρ.le
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hD : Dfun τ ℓ u w ≤ max (Dp ℓ u w) 0 := by
    rw [Dfun_eq]
    have : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (mul_pos hw hR.ℓ_pos).le
    linarith [le_max_left (Dp ℓ u w) 0]
  unfold gfun
  by_cases hI : w ∈ I
  · rw [Set.indicator_of_mem hI]
    exact ⟨mul_nonneg hb0 (Real.exp_pos _).le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD) hb0⟩
  · rw [Set.indicator_of_notMem hI]
    exact ⟨le_rfl, mul_nonneg hb0 (Real.exp_pos _).le⟩

lemma etaF_nonneg_large {τ ℓ x : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hx : 0 < x) :
    0 ≤ etaF τ ℓ x := by
  have hm0 : 0 < mOf ℓ x := BSaias.mOf_pos hℓ hx
  have hd : 0 ≤ dpos (mOf ℓ x) x := le_max_right _ _
  have hk : 0 ≤ kappa τ := by unfold kappa; linarith
  have hlog : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hu' : 0 ≤ u0 (mOf ℓ x) := Real.sqrt_nonneg _
  unfold etaF BSCert.Z2.A
  simp only
  have : 0 < 2 + x := by linarith
  positivity

/-- **The reduction of `ρ₄`.** -/
lemma LargeRange.rho4_le (hR : LargeRange τ ℓ u) :
    ℓ * rho4 τ ℓ u ≤ Kp / Dickman.rho (u - 1) * ∫ w in Ioc (u - 1) (Uf τ ℓ),
      (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hρ := Dickman.rho_pos (u - 1)
  have hτ1 : 1 ≤ τ := by linarith [hR.1]
  have hτℓ : 3 * τ < ℓ := by linarith [hR.2.1, hR.τ_pos]
  have hab := hR.Uf_ge
  have hI1 : IntegrableOn (fun w => gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w)
      (Ioc (u - 1) (Uf τ ℓ)) := by
    have := (intervalIntegrable_E2 (u := u) hτ1 hτℓ (measurableSet_paperCut τ ℓ))
    rw [hR.wlo_eq, intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at this
    exact this
  have hI2 : IntegrableOn (fun w => (1 + w) * Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
    apply integrableOn_mul_rho (C := 1) (φ := fun w => 1 + w) hu
      (by fun_prop : Continuous (fun w : ℝ => 1 + w)).continuousOn
    intro w hw
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + w), one_mul]
    exact one_add_le_pow_five (by linarith)
  have hI3 : IntegrableOn (fun w => (1 + w) * max (Dp ℓ u w) 0 *
      Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w) (Ioc (u - 1) (Uf τ ℓ)) := by
    apply integrableOn_Ioc_of_continuousAt (by linarith)
    intro w hw
    have hD := continuousAt_Dp (u := u) hℓ0 hw
    exact ((((continuousAt_const.add continuousAt_id).mul (hD.max continuousAt_const)).mul
      (hD.max continuousAt_const).rexp).mul ((Dickman.continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousAt)).div continuousAt_id hw.ne'
  have hsub : ∫ w in Ioc (u - 1) (Uf τ ℓ), (1 + w) * Dickman.rho (w - 1) / w ≤
      ∫ w in Ioi (u - 1), (1 + w) * Dickman.rho (w - 1) / w := by
    apply setIntegral_mono_set hI2
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_
      have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
      exact div_nonneg (mul_nonneg (by linarith) (Dickman.rho_pos _).le) hw0.le
    · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
  have hpt : ∫ w in Ioc (u - 1) (Uf τ ℓ), (Dickman.rho (u - 1) *
      (gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w) - (1 + w) * Dickman.rho (w - 1) / w) ≤
      ∫ w in Ioc (u - 1) (Uf τ ℓ), (1 + w) * max (Dp ℓ u w) 0 *
        Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w := by
    apply setIntegral_mono_on ((hI1.const_mul _).sub (hI2.mono_set Ioc_subset_Ioi_self)) hI3
      measurableSet_Ioc
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hg : 0 ≤ (1 + w) * Dickman.rho (w - 1) / w :=
      div_nonneg (mul_nonneg (by linarith) (Dickman.rho_pos _).le) hw0.le
    have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
    have hD : Dfun τ ℓ u w ≤ Dp ℓ u w := by
      rw [Dfun_eq]; have : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (mul_pos hw0 hℓ0).le
      linarith
    have hm := exp_sub_one_le (Dp ℓ u w)
    have hm0 : 0 ≤ max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0) :=
      mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    have e : Dickman.rho (u - 1) * (gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w) -
        (1 + w) * Dickman.rho (w - 1) / w =
        (1 + w) * Dickman.rho (w - 1) / w *
          ((paperCut τ ℓ).indicator (fun w => Real.exp (Dfun τ ℓ u w)) w - 1) := by
      unfold gfun
      by_cases hI : w ∈ paperCut τ ℓ
      · rw [Set.indicator_of_mem hI, Set.indicator_of_mem hI]; field_simp
      · rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem hI]; ring
    have e2 : (1 + w) * max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0) *
        Dickman.rho (w - 1) / w = (1 + w) * Dickman.rho (w - 1) / w *
          (max (Dp ℓ u w) 0 * Real.exp (max (Dp ℓ u w) 0)) := by ring
    simp only [Pi.sub_apply]
    rw [e, e2]
    apply mul_le_mul_of_nonneg_left _ hg
    by_cases hI : w ∈ paperCut τ ℓ
    · rw [Set.indicator_of_mem hI]
      linarith [Real.exp_le_exp.mpr hD]
    · rw [Set.indicator_of_notMem hI]; linarith
  unfold rho4 E2term e2 Epi
  beta_reduce
  rw [hR.wlo_eq, intervalIntegral.integral_of_le hab]
  rw [integral_sub (hI1.const_mul _) (hI2.mono_set Ioc_subset_Ioi_self),
    integral_const_mul] at hpt
  set J1 := ∫ w in Ioc (u - 1) (Uf τ ℓ), gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w
  set J2 := ∫ w in Ioi (u - 1), (1 + w) * Dickman.rho (w - 1) / w
  set J2' := ∫ w in Ioc (u - 1) (Uf τ ℓ), (1 + w) * Dickman.rho (w - 1) / w
  set J3 := ∫ w in Ioc (u - 1) (Uf τ ℓ), (1 + w) * max (Dp ℓ u w) 0 *
    Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w
  have hfin : ℓ * (Kp / ℓ * J1 - Kp * (J2 / Dickman.rho (u - 1)) / ℓ) =
      Kp / Dickman.rho (u - 1) * (Dickman.rho (u - 1) * J1 - J2) := by
    field_simp
  rw [hfin]
  apply mul_le_mul_of_nonneg_left _ (by unfold Kp; positivity)
  linarith

/-- **The reduction of `E₃`.** -/
lemma LargeRange.E3_le (hR : LargeRange τ ℓ u) :
    ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤ 2 * Kp / Dickman.rho (u - 1) *
      ∫ w in Ioc (u - 1) (Uf τ ℓ), ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0) *
        Dickman.rho (w - 1) / w := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hρ := Dickman.rho_pos (u - 1)
  have hτ1 : 1 ≤ τ := by linarith [hR.1]
  have hτℓ : 3 * τ < ℓ := by linarith [hR.2.1, hR.τ_pos]
  have hab := hR.Uf_ge
  have hI1 : IntegrableOn (fun w => gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w)
      (Ioc (u - 1) (Uf τ ℓ)) := by
    have := (intervalIntegrable_E3 (u := u) hτ1 hτℓ (measurableSet_paperCut τ ℓ))
    rw [hR.wlo_eq, intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at this
    exact this
  have hI3 : IntegrableOn (fun w => ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0) *
      Dickman.rho (w - 1) / w) (Ioc (u - 1) (Uf τ ℓ)) := by
    apply integrableOn_Ioc_of_continuousAt (by linarith)
    intro w hw
    have hD := continuousAt_Dp (u := u) hℓ0 hw
    exact (((continuousAt_const.mul (etaF_continuousAt τ ℓ hℓ0 hw)).mul
      (hD.max continuousAt_const).rexp).mul ((Dickman.continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousAt)).div continuousAt_id hw.ne'
  unfold E3term
  rw [hR.wlo_eq, intervalIntegral.integral_of_le hab]
  have h : ∫ w in Ioc (u - 1) (Uf τ ℓ), gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w ≤
      ∫ w in Ioc (u - 1) (Uf τ ℓ), (1 / (ℓ * Dickman.rho (u - 1))) *
        (ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w) := by
    apply setIntegral_mono_on hI1 (hI3.const_mul _) measurableSet_Ioc
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    obtain ⟨h0, h1⟩ := hR.gfun_le (I := paperCut τ ℓ) hw0
    have hη := etaF_nonneg_large (τ := τ) (ℓ := ℓ) hR.τ_pos.le hℓ0 hw0
    have e : (1 / (ℓ * Dickman.rho (u - 1))) * (ℓ * etaF τ ℓ w *
        Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w) =
        Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (max (Dp ℓ u w) 0) *
          etaF τ ℓ w / w := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hη) hw0.le
  rw [integral_const_mul] at h
  have hK : 0 ≤ 2 * Kp := by unfold Kp; norm_num
  calc ℓ * (2 * Kp * ∫ w in Ioc (u - 1) (Uf τ ℓ), gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w)
      ≤ ℓ * (2 * Kp * (1 / (ℓ * Dickman.rho (u - 1)) * ∫ w in Ioc (u - 1) (Uf τ ℓ),
          ℓ * etaF τ ℓ w * Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w)) := by
        gcongr
    _ = _ := by field_simp

end BSaias.Large

end
