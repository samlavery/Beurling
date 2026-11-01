module

public import RequestProject.Beurling.Noise.BSZ2Bounds

/-!
# The main term and the error terms in region Z2 (Theorem 5.6, Step 7(iii))

Under `Z2Hyp τ ℓ u`, with the paper's cut-off `I = {w ≤ U(m)}` (and in fact for any measurable
cut-off), split `[u-1, U(ℓ)]` at `u` and `b = min(u + 60, U(ℓ))`:

* `M_le` : `M ≤ 1 + (M - 1)_{bound}` (`BSCert.Z2.Mm1`);
* `E1_le`, `E2_le`, `E3_le` : `E_i ≤` the closed forms `BSCert.Z2.E1`, `E2`, `E3`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace BSaias

open BSCert.Z2 (betaI betaII alpha gamma1 gammaMax qq)

namespace Z2Hyp

variable {τ ℓ u : ℝ} (h : Z2Hyp τ ℓ u)
include h

/-- The split point `b = min(u + 60, U(ℓ))`. -/
noncomputable def bpt (_h : Z2Hyp τ ℓ u) : ℝ := min (u + 60) (Uf τ ℓ)

lemma u_le_b : u ≤ h.bpt := le_min (by linarith) h.hu2
lemma b_le_U : h.bpt ≤ Uf τ ℓ := min_le_right _ _
lemma b_le_60 : h.bpt ≤ u + 60 := min_le_left _ _

lemma D_on_b {w : ℝ} (hw1 : u ≤ w) (hw2 : w ≤ h.bpt) :
    Dfun τ ℓ u w ≤ betaII ℓ u + gamma1 ℓ u * (w - u) :=
  D_le_gamma1 (by linarith [h.hτ]) h.ℓ_pos h.hu1 hw1 (hw2.trans h.b_le_60)

lemma D_on_U {w : ℝ} (hw1 : u ≤ w) (hw2 : w ≤ Uf τ ℓ) :
    Dfun τ ℓ u w ≤ betaII ℓ u + gammaMax ℓ u * (w - u) :=
  D_le_gammaMax (by linarith [h.hτ]) h.ℓ_pos h.hu1 hw1 (hw2.trans h.U_le_Ubar)

/-- Splitting an integral over `[u-1, U]` at `u` and `b`. -/
lemma split3 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (u - 1) (Uf τ ℓ)) :
    ∫ w in (u - 1)..Uf τ ℓ, f w =
      (∫ w in (u - 1)..u, f w) + (∫ w in u..h.bpt, f w) + ∫ w in h.bpt..Uf τ ℓ, f w := by
  have hu := h.u_le_b
  have hb := h.b_le_U
  have h1 : IntervalIntegrable f volume (u - 1) u := hf.mono_set (by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable f volume u h.bpt := hf.mono_set (by
    rw [uIcc_of_le hu, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) hb)
  have h3 : IntervalIntegrable f volume h.bpt (Uf τ ℓ) := hf.mono_set (by
    rw [uIcc_of_le hb, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans h3),
    ← intervalIntegral.integral_add_adjacent_intervals h2 h3]
  ring

lemma intM : IntervalIntegrable (fun w => gfun τ ℓ u (paperCut τ ℓ) w / w) volume (u - 1)
    (Uf τ ℓ) := by
  have := intervalIntegrable_M (τ := τ) (ℓ := ℓ) (u := u) (by linarith [h.hτ])
    (by linarith [h.hℓ, h.hτ])
    (measurableSet_paperCut τ ℓ)
  rwa [h.wlo_eq] at this

lemma intE2 : IntervalIntegrable (fun w => gfun τ ℓ u (paperCut τ ℓ) w * (1 + w) / w) volume
    (u - 1) (Uf τ ℓ) := by
  have := intervalIntegrable_E2 (τ := τ) (ℓ := ℓ) (u := u) (by linarith [h.hτ])
    (by linarith [h.hℓ, h.hτ])
    (measurableSet_paperCut τ ℓ)
  rwa [h.wlo_eq] at this

lemma intE3 : IntervalIntegrable (fun w => gfun τ ℓ u (paperCut τ ℓ) w * etaF τ ℓ w / w)
    volume (u - 1) (Uf τ ℓ) := by
  have := intervalIntegrable_E3 (τ := τ) (ℓ := ℓ) (u := u) (by linarith [h.hτ])
    (by linarith [h.hℓ, h.hτ])
    (measurableSet_paperCut τ ℓ)
  rwa [h.wlo_eq] at this

set_option linter.unusedSectionVars false in
lemma sub_int {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume (u - 1) (Uf τ ℓ))
    (ha : u - 1 ≤ a) (hab : a ≤ b) (hb : b ≤ Uf τ ℓ) : IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc ha hb)

/-! ## The main term -/

/-- `M`, piece `[u-1, u]` (Part I). -/
lemma piece1 : ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w / w ≤
    Real.exp (betaI ℓ u) / Dickman.rho (u - 1) * (Dickman.rho (u - 1) - Dickman.rho u) -
    Real.exp (betaI ℓ u) / Dickman.rho (u - 1) * (1 - Real.exp (-alpha ℓ u)) *
      (Dickman.rho (u - 1) - u * Dickman.rho u) := by
  have hu := h.hu1
  have hPi := intervalIntegrable_P (a := u - 1) (b := u) (by linarith) (by linarith)
  have hP2i := intervalIntegrable_P2 (a := u - 1) (b := u) (u := u) (by linarith)
    (by linarith)
  have hρ0 := h.rho0_pos
  calc ∫ w in (u - 1)..u, gfun τ ℓ u (paperCut τ ℓ) w / w
      ≤ ∫ w in (u - 1)..u, (Real.exp (betaI ℓ u) / Dickman.rho (u - 1) *
          (Dickman.rho (w - 1) / w) - Real.exp (betaI ℓ u) / Dickman.rho (u - 1) *
          (1 - Real.exp (-alpha ℓ u)) * (Dickman.rho (w - 1) * (u - w) / w)) := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (h.sub_int h.intM le_rfl (by linarith) h.hu2) ((hPi.const_mul _).sub (hP2i.const_mul _))
        intro w hw
        have hw0 : 0 < w := by linarith [hw.1]
        have h1 := (h.gfun_le (paperCut τ ℓ) w).trans (h.gBase_partI hw.1 hw.2)
        calc gfun τ ℓ u (paperCut τ ℓ) w / w ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) *
              Real.exp (betaI ℓ u) * (1 - (1 - Real.exp (-alpha ℓ u)) * (u - w)) / w :=
              div_le_div_of_nonneg_right h1 hw0.le
          _ = _ := by field_simp
    _ = _ := by
        rw [intervalIntegral.integral_sub (hPi.const_mul _) (hP2i.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          mass_I hu, mass_lin hu]

/-- `M`, piece `[u, b]` (Part II, slope `γ₁`). -/
lemma piece2 : ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w / w ≤
    Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * (∫ w in u..h.bpt, Dickman.rho (w - 1) / w) +
    Real.exp (betaII ℓ u) / u * (1 / (Dickman.ratio (u - 1) - gamma1 ℓ u) -
      1 / Dickman.ratio (u - 1)) := by
  have hu := h.hu1
  have hu0 : 0 < u := by linarith
  have hb1 := h.u_le_b
  have hb2 := h.b_le_U
  have hk1 := h.gamma1_lt
  have hr0 := h.r0_ge
  have hγ1 : 0 ≤ gamma1 ℓ u := gamma1_nonneg h.ℓ_pos hu
  have hPi := intervalIntegrable_P (a := u) (b := h.bpt) hu0 hb1
  have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gamma1 ℓ u) u u h.bpt
  have hE0 := intervalIntegrable_expl (Dickman.ratio (u - 1)) u u h.bpt
  calc ∫ w in u..h.bpt, gfun τ ℓ u (paperCut τ ℓ) w / w
      ≤ ∫ w in u..h.bpt, (Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
          (Dickman.rho (w - 1) / w) + Real.exp (betaII ℓ u) / u *
          (Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (w - u))) -
            Real.exp (-(Dickman.ratio (u - 1) * (w - u))))) := by
        apply intervalIntegral.integral_mono_on hb1
          (h.sub_int h.intM (by linarith) hb1 hb2)
          ((hPi.const_mul _).add ((hE.sub hE0).const_mul _))
        intro w hw
        have hw0 : 0 < w := by linarith [hw.1]
        have h1 := div_le_div_of_nonneg_right (h.gfun_le (paperCut τ ℓ) w) hw0.le
        exact h1.trans (h.gBase_partII_M hw.1 hγ1 (h.D_on_b hw.1 hw.2))
    _ = Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * (∫ w in u..h.bpt, Dickman.rho (w - 1) / w)
        + Real.exp (betaII ℓ u) / u *
        ((1 - Real.exp (-((Dickman.ratio (u - 1) - gamma1 ℓ u) * (h.bpt - u)))) /
          (Dickman.ratio (u - 1) - gamma1 ℓ u) -
         (1 - Real.exp (-(Dickman.ratio (u - 1) * (h.bpt - u)))) / Dickman.ratio (u - 1)) := by
        rw [intervalIntegral.integral_add (hPi.const_mul _) ((hE.sub hE0).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hE hE0, integral_expl hk1.ne',
          integral_expl (by linarith : Dickman.ratio (u - 1) ≠ 0)]
        simp
    _ ≤ _ := by
        have hEu : 0 ≤ Real.exp (betaII ℓ u) / u := by positivity
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hEu)
        set k1 := Dickman.ratio (u - 1) - gamma1 ℓ u
        set r0 := Dickman.ratio (u - 1)
        have ht : 0 ≤ h.bpt - u := by linarith
        have e1 : Real.exp (-(r0 * (h.bpt - u))) ≤ Real.exp (-(k1 * (h.bpt - u))) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have e2 : Real.exp (-(r0 * (h.bpt - u))) / r0 ≤ Real.exp (-(k1 * (h.bpt - u))) / k1 :=
          div_le_div₀ (Real.exp_pos _).le e1 hk1 (by linarith)
        have : (1 - Real.exp (-(k1 * (h.bpt - u)))) / k1 -
            (1 - Real.exp (-(r0 * (h.bpt - u)))) / r0 = (1 / k1 - 1 / r0) -
            (Real.exp (-(k1 * (h.bpt - u))) / k1 - Real.exp (-(r0 * (h.bpt - u))) / r0) := by ring
        linarith

/-- `M`, piece `[b, U]` (Part II, slope `γ_max`). -/
lemma piece3 : ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w / w ≤
    Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
      (∫ w in h.bpt..Uf τ ℓ, Dickman.rho (w - 1) / w) +
    Real.exp (betaII ℓ u) / u * qq Dickman.ratio ℓ u := by
  have hu := h.hu1
  have hu0 : 0 < u := by linarith
  have hb1 := h.u_le_b
  have hb2 := h.b_le_U
  have hkm := h.gammaMax_lt
  have hq : 0 < qq Dickman.ratio ℓ u := by unfold qq; exact div_pos (Real.exp_pos _) hkm
  rcases le_or_gt (Uf τ ℓ) (u + 60) with hU | hU
  · have hbU : h.bpt = Uf τ ℓ := min_eq_right hU
    rw [hbU, intervalIntegral.integral_same, intervalIntegral.integral_same]
    have : 0 ≤ Real.exp (betaII ℓ u) / u * qq Dickman.ratio ℓ u := by positivity
    linarith
  · have hbU : h.bpt = u + 60 := min_eq_left hU.le
    have hPi := intervalIntegrable_P (a := h.bpt) (b := Uf τ ℓ) (by linarith) hb2
    have hE := intervalIntegrable_expl (Dickman.ratio (u - 1) - gammaMax ℓ u) u h.bpt (Uf τ ℓ)
    calc ∫ w in h.bpt..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) w / w
        ≤ ∫ w in h.bpt..Uf τ ℓ, (Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
            (Dickman.rho (w - 1) / w) + Real.exp (betaII ℓ u) / u *
            Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (w - u)))) := by
          apply intervalIntegral.integral_mono_on hb2
            (h.sub_int h.intM (by linarith) hb2 le_rfl) ((hPi.const_mul _).add (hE.const_mul _))
          intro w hw
          have hw0 : 0 < w := by linarith [hw.1]
          have hw1 : u ≤ w := by linarith [hw.1]
          have h1 := div_le_div_of_nonneg_right (h.gfun_le (paperCut τ ℓ) w) hw0.le
          have h2 := h1.trans (h.gBase_partII_M hw1 h.gammaMax_nonneg (h.D_on_U hw1 hw.2))
          refine h2.trans ?_
          have : 0 ≤ Real.exp (betaII ℓ u) / u := by positivity
          have := Real.exp_pos (-(Dickman.ratio (u - 1) * (w - u)))
          nlinarith
      _ = Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
            (∫ w in h.bpt..Uf τ ℓ, Dickman.rho (w - 1) / w) + Real.exp (betaII ℓ u) / u *
            ∫ w in h.bpt..Uf τ ℓ,
              Real.exp (-((Dickman.ratio (u - 1) - gammaMax ℓ u) * (w - u))) := by
          rw [intervalIntegral.integral_add (hPi.const_mul _) (hE.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          refine (integral_expl_le hkm).trans (le_of_eq ?_)
          unfold qq
          rw [hbU]
          ring_nf

/-- The closed form `1 + (M-1)_{bound}`. -/
lemma one_add_Mm1 : 1 + BSCert.Z2.Mm1 Dickman.ratio ℓ u =
    Real.exp (betaI ℓ u) / Dickman.rho (u - 1) * (Dickman.rho (u - 1) - Dickman.rho u) -
    Real.exp (betaI ℓ u) / Dickman.rho (u - 1) * (1 - Real.exp (-alpha ℓ u)) *
      (Dickman.rho (u - 1) - u * Dickman.rho u) +
    Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * Dickman.rho u +
    Real.exp (betaII ℓ u) / u * ((1 / (Dickman.ratio (u - 1) - gamma1 ℓ u) -
      1 / Dickman.ratio (u - 1)) + qq Dickman.ratio ℓ u) := by
  have hu0 : 0 < u := by linarith [h.hu1]
  have hρ0 := h.rho0_pos
  have hρu := Dickman.rho_pos u
  have hk1 := h.gamma1_lt
  have hr0 : 0 < Dickman.ratio (u - 1) := by linarith [h.r0_ge]
  have hru : Dickman.ratio u = Dickman.rho (u - 1) / (u * Dickman.rho u) := rfl
  unfold BSCert.Z2.Mm1
  rw [hru]
  have hg : gamma1 ℓ u / (Dickman.ratio (u - 1) * (Dickman.ratio (u - 1) - gamma1 ℓ u)) =
      1 / (Dickman.ratio (u - 1) - gamma1 ℓ u) - 1 / Dickman.ratio (u - 1) := by
    field_simp; ring
  rw [hg]
  field_simp
  ring

/-- **`M ≤ 1 + (M-1)_{bound}`** (the main term in region Z2). -/
theorem M_le : Mterm τ ℓ u (paperCut τ ℓ) ≤ 1 + BSCert.Z2.Mm1 Dickman.ratio ℓ u := by
  have hu := h.hu1
  have hu0 : 0 < u := by linarith
  have hb1 := h.u_le_b
  have hb2 := h.b_le_U
  unfold Mterm
  rw [h.wlo_eq, h.split3 h.intM, h.one_add_Mm1]
  have i1 := h.piece1
  have i2 := h.piece2
  have i3 := h.piece3
  have hPsum : (∫ w in u..h.bpt, Dickman.rho (w - 1) / w) +
      (∫ w in h.bpt..Uf τ ℓ, Dickman.rho (w - 1) / w) =
      Dickman.rho u - Dickman.rho (Uf τ ℓ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_P hu0 hb1) (intervalIntegrable_P (by linarith) hb2)]
    exact mass_tail hu h.hu2
  have hρU := Dickman.rho_pos (Uf τ ℓ)
  have hρ0 := h.rho0_pos
  have hEII : 0 ≤ Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * Dickman.rho (Uf τ ℓ) := by
    positivity
  have hsum : Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
      (∫ w in u..h.bpt, Dickman.rho (w - 1) / w) + Real.exp (betaII ℓ u) /
      Dickman.rho (u - 1) * (∫ w in h.bpt..Uf τ ℓ, Dickman.rho (w - 1) / w) =
      Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * Dickman.rho u -
      Real.exp (betaII ℓ u) / Dickman.rho (u - 1) * Dickman.rho (Uf τ ℓ) := by
    rw [← mul_add, hPsum]; ring
  linarith

end Z2Hyp

end BSaias

end
