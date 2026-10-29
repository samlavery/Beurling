module

public import RequestProject.Beurling.Noise.BSL57Defs
public import RequestProject.Beurling.Noise.BSLargeSlack
public import RequestProject.Beurling.Noise.BSZ2Pointwise
public import RequestProject.Beurling.Noise.BSZ2Integrable

/-!
# Lemma 5.7: the decomposition (04c-saias.tex, lines 366-376)

`l57_decomp`: for `u ≥ 2` in the range of Lemma 5.7,
`ℓΣ ≥ c(u) + ℓ s_a - ℓ(ρ₁ + ρ₂ + ρ₃ + ρ₄ + E₃ + T)`.

The proof is the paper's: since `U(m) ≤ Ū`, `M ≤ ∫ π e^D 1[w ≤ Ū]`; `e^D = e^{D_Φ} e^{D'}` with
`e^{D'} ≤ 1 + D' + ½ D'² e^{D'₊}` (`exp_le_quad_pos`); `∫ π e^{D_Φ} ≤ 1 - Φ_ben` (`π` has mass
`1`, (R1)); `e^{D_Φ} D' ≤ D' + (1 - e^{D_Φ})|D'|`, and `D' ≥ 0` for `w ≥ u` (so the cut at `Ū`
may be removed); `E_π D' = (B/ℓ) j_A - s_a`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

/-- `e^x ≤ 1 + x + ½ x² e^{x₊}`. -/
lemma exp_le_quad_pos (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp (max x 0) := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
    -- `(1 + t) e^{-t} + t²/2` is non-decreasing on `[0, ∞)`
    set h : ℝ → ℝ := fun t => (1 + t) * Real.exp (-t) + t ^ 2 / 2
    have hd : ∀ t, HasDerivAt h (t * (1 - Real.exp (-t))) t := by
      intro t
      have h1 := ((hasDerivAt_id t).const_add 1).mul ((hasDerivAt_neg t).exp)
      have h2 := ((hasDerivAt_id t).pow 2).div_const 2
      convert h1.add h2 using 1
      simp only [id]; ring
    have hmono : MonotoneOn h (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun t _ => (hd t).continuousAt.continuousWithinAt)
        (fun t _ => (hd t).hasDerivWithinAt)
      intro t ht
      rw [interior_Ici, mem_Ioi] at ht
      have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact mul_nonneg ht.le (by linarith)
    have h0 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
    simp only [h, neg_zero, Real.exp_zero] at h0
    have hex := Real.exp_pos x
    have e : (1 + x) * Real.exp (-x) * Real.exp x = 1 + x := by
      rw [mul_assoc, ← Real.exp_add]; simp
    nlinarith
  · rw [max_eq_right hx, Real.exp_zero, mul_one]
    set k : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 - Real.exp t
    have hd : ∀ t, HasDerivAt k (1 + t - Real.exp t) t := by
      intro t
      have h1 := ((hasDerivAt_id t).const_add 1).add (((hasDerivAt_id t).pow 2).div_const 2)
      convert h1.sub (Real.hasDerivAt_exp t) using 1
      simp only [id]; ring
    have hanti : AntitoneOn k (Iic 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
        (fun t _ => (hd t).continuousAt.continuousWithinAt)
        (fun t _ => (hd t).hasDerivWithinAt)
      intro t _
      linarith [Real.add_one_le_exp t]
    have h0 := hanti (mem_Iic.mpr hx) (mem_Iic.mpr le_rfl) hx
    simp only [k, Real.exp_zero] at h0
    linarith

variable {τ ℓ u : ℝ}

lemma LargeRange.ℓ_pos (h : LargeRange τ ℓ u) : 0 < ℓ := by linarith [h.2.2.1]
lemma LargeRange.τ_pos (h : LargeRange τ ℓ u) : 0 < τ := by linarith [h.1]

lemma LargeRange.wlo_eq (h : LargeRange τ ℓ u) : wlo τ ℓ u = u - 1 := by
  unfold wlo
  apply max_eq_left
  have hτ := h.τ_pos
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : w1 τ ℓ ≤ 1 := by
    unfold w1; rw [div_le_one (by linarith [h.ℓ_pos])]; linarith
  linarith [h.2.2.2.1]

lemma Dfun_eq (w : ℝ) : Dfun τ ℓ u w = Dp ℓ u w - kappa τ / (w * ℓ) := by
  unfold Dfun Dp; ring

lemma Dp_eq (hℓ : 0 < ℓ) {w : ℝ} (hw : 0 < w) :
    Dp ℓ u w = 11 / ℓ * hA u w + (aQ (mOf ℓ w) w - aQ ℓ u) := by
  unfold Dp Qf hA
  rw [BSaias.A_mOf hℓ hw]
  unfold BSCert.Z2.A
  field_simp
  ring

lemma continuousAt_Dp (hℓ : 0 < ℓ) {w : ℝ} (hw : 0 < w) :
    ContinuousAt (fun w => Dp ℓ u w) w := by
  have hm : 0 < mOf ℓ w := BSaias.mOf_pos hℓ hw
  unfold Dp Qf aQ BSCert.Z2.A mOf u0 BSCert.Z2.u0
  unfold mOf at hm
  have hsq : √(ℓ * w / (1 + w)) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have h1 : (1 + w) ≠ 0 := by positivity
  have h2 : (2 + w) ≠ 0 := by positivity
  fun_prop (disch := first | assumption | positivity | exact hm.ne' | exact hsq)

lemma hfun_ge {u w : ℝ} (hu : 2 ≤ u) (huw : u ≤ w) :
    (1 + u) ^ 3 * Real.log (2 + u) ≤ hfun w := by
  unfold hfun
  have hw0 : 0 < w := by linarith
  have hl0 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 + u) ≤ Real.log (2 + w) := Real.log_le_log (by linarith) (by linarith)
  have hp : (1 + u) ^ 3 ≤ (1 + w) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  rw [le_div_iff₀ hw0]
  have h1 : (1 + u) ^ 3 * Real.log (2 + u) ≤ (1 + w) ^ 3 * Real.log (2 + w) :=
    mul_le_mul hp hl hl0 (by positivity)
  have h2 : 0 ≤ (1 + w) ^ 3 * Real.log (2 + w) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  nlinarith

/-- `D' ≥ 0` for `w ≥ u`. -/
lemma Dp_nonneg (hℓ : 0 < ℓ) (hu : 2 ≤ u) {w : ℝ} (huw : u ≤ w) : 0 ≤ Dp ℓ u w := by
  have hw0 : 0 < w := by linarith
  rw [Dp_eq hℓ hw0]
  have hA : 0 ≤ 11 / ℓ * hA u w := by
    unfold hA; exact mul_nonneg (by positivity) (by linarith [hfun_ge hu huw])
  have ha : aQ ℓ u ≤ aQ (mOf ℓ w) w := by
    unfold aQ
    have hm : 0 < mOf ℓ w := BSaias.mOf_pos hℓ hw0
    have hmℓ : mOf ℓ w ≤ ℓ := by
      unfold mOf; rw [div_le_iff₀ (by linarith)]; nlinarith
    have hu0 := u0_mOf_le hℓ hw0.le
    have hnum : max (u - u0 ℓ) 0 ≤ max (w - u0 (mOf ℓ w)) 0 :=
      max_le_max (by linarith) le_rfl
    have hs : √(mOf ℓ w) ≤ √ℓ := Real.sqrt_le_sqrt hmℓ
    have hsm : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hm
    calc (max (u - u0 ℓ) 0) ^ 2 / (2 * √ℓ) ≤ (max (u - u0 ℓ) 0) ^ 2 / (2 * √(mOf ℓ w)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ (max (w - u0 (mOf ℓ w)) 0) ^ 2 / (2 * √(mOf ℓ w)) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hnum 2)
            (by positivity)
  linarith

/-! ## Integrability against `π` -/

lemma int_phi (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hκ : 0 ≤ kappa τ) :
    IntegrableOn (fun w => Real.exp (-(kappa τ / (w * ℓ))) * Dickman.rho (w - 1) / w)
      (Ioi (u - 1)) := by
  apply integrableOn_mul_rho (C := 1) hu
  · intro w hw
    have hw0 : w ≠ 0 := by have := mem_Ici.mp hw; linarith
    apply ContinuousAt.continuousWithinAt
    exact ((continuousAt_const.div (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero hw0 hℓ.ne')).neg).rexp
  · intro w hw
    have hw0 : 0 < w := by linarith
    rw [abs_of_pos (Real.exp_pos _), one_mul]
    have : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := div_nonneg hκ (by positivity : 0 ≤ w * ℓ); linarith)
    exact this.trans (one_le_pow₀ (by linarith))

lemma continuousAt_hfun {w : ℝ} (hw : 0 < w) : ContinuousAt hfun w := by
  unfold hfun
  have h2 : (2 + w) ≠ 0 := by positivity
  fun_prop (disch := first | assumption | positivity | exact hw.ne')

lemma int_hA (hℓ : 0 < ℓ) (hu : 2 ≤ u) :
    IntegrableOn (fun w => 11 / ℓ * hA u w * Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
  set K := (1 + u) ^ 3 * Real.log (2 + u)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  apply integrableOn_mul_rho (C := 11 / ℓ * (1 + K)) hu
  · intro w hw
    have hw0 : 0 < w := by have := mem_Ici.mp hw; linarith
    apply ContinuousAt.continuousWithinAt
    unfold hA
    exact continuousAt_const.mul ((continuousAt_hfun hw0).sub continuousAt_const)
  · intro w hw
    have hw1 : 1 ≤ w := by linarith
    have hh := hfun_le_pow_five hw1
    have hh0 : 0 ≤ hfun w := by
      unfold hfun
      exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
        (by linarith)
    have hp : 1 ≤ (1 + w) ^ 5 := one_le_pow₀ (by linarith)
    unfold hA
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 11 / ℓ), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [abs_le]
    constructor <;> nlinarith

lemma int_Da (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) :
    IntegrableOn (fun w => (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w)
      (Ioi (u - 1)) :=
  integrableOn_aQ (ℓ := ℓ) (by linarith) hu (aQ ℓ u)

lemma int_R (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) (hκ : 0 ≤ kappa τ) :
    IntegrableOn (fun w => (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| *
      Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hg := ((int_hA (u := u) hℓ0 hu).norm).add (int_Da (u := u) hℓ hu).norm
  refine hg.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun w hw => ?_) measurableSet_Ioi
    have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
    apply ContinuousAt.continuousWithinAt
    have hc : ContinuousAt (fun w : ℝ => kappa τ / (w * ℓ)) w :=
      continuousAt_const.div (continuousAt_id.mul continuousAt_const)
        (mul_ne_zero hw0.ne' hℓ0.ne')
    exact (((continuousAt_const.sub hc.neg.rexp).mul (continuousAt_Dp hℓ0 hw0).abs).mul
      ((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt)).div
      continuousAt_id hw0.ne'
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_
    have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
    have he1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := div_nonneg hκ (by positivity : 0 ≤ w * ℓ); linarith)
    have he0 := Real.exp_pos (-(kappa τ / (w * ℓ)))
    have hψ : 0 ≤ Dickman.rho (w - 1) / w := div_nonneg (Dickman.rho_pos _).le hw0.le
    rw [Dp_eq hℓ0 hw0]
    have hab := abs_add_le (11 / ℓ * hA u w) (aQ (mOf ℓ w) w - aQ ℓ u)
    have hn := abs_nonneg (11 / ℓ * hA u w + (aQ (mOf ℓ w) w - aQ ℓ u))
    have h1 : (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |11 / ℓ * hA u w +
        (aQ (mOf ℓ w) w - aQ ℓ u)| ≤ |11 / ℓ * hA u w| + |aQ (mOf ℓ w) w - aQ ℓ u| := by
      nlinarith
    have hl0 : 0 ≤ (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |11 / ℓ * hA u w +
        (aQ (mOf ℓ w) w - aQ ℓ u)| * Dickman.rho (w - 1) / w := by
      rw [mul_div_assoc]; exact mul_nonneg (mul_nonneg (by linarith) hn) hψ
    have eA : ‖11 / ℓ * hA u w * Dickman.rho (w - 1) / w‖ = |11 / ℓ * hA u w| *
        (Dickman.rho (w - 1) / w) := by
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_of_nonneg hψ]
    have eD : ‖(aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w‖ =
        |aQ (mOf ℓ w) w - aQ ℓ u| * (Dickman.rho (w - 1) / w) := by
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_of_nonneg hψ]
    rw [Real.norm_eq_abs, abs_of_nonneg hl0]
    show _ ≤ ‖11 / ℓ * hA u w * Dickman.rho (w - 1) / w‖ +
      ‖(aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w‖
    rw [eA, eD, mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_right h1 hψ]

lemma mul_c_div {r : ℝ} (hr : r ≠ 0) (c x : ℝ) : r * (c * (x / r)) = c * x := by
  field_simp

/-! ## The main term -/

/-- **The main term of the decomposition**: `M ≤ 1 - Φ_ben + (B/ℓ) j_A - s_a + ρ₁ + ρ₂`. -/
theorem M_le (hR : LargeRange τ ℓ u) :
    Mterm τ ℓ u (paperCut τ ℓ) ≤
      1 - PhiBen τ ℓ u + 11 / ℓ * jA u - sA ℓ u + rho1 τ ℓ u + rho2 τ ℓ u := by
  obtain ⟨hτ, hτℓ, hℓ, hu2, huU⟩ := id hR
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith
  set U := Uf τ ℓ
  have hρu := Dickman.rho_pos (u - 1)
  -- the integrands
  set F1 : ℝ → ℝ := fun w => Real.exp (-(kappa τ / (w * ℓ))) * Dickman.rho (w - 1) / w +
    11 / ℓ * hA u w * Dickman.rho (w - 1) / w +
    (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w +
    (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| * Dickman.rho (w - 1) / w
  set G2 : ℝ → ℝ := fun w =>
    Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w
  have iE := int_phi (τ := τ) hℓ0 hu2 hκ
  have iA := int_hA (u := u) hℓ0 hu2
  have iD := int_Da (u := u) hℓ hu2
  have iR := int_R (τ := τ) (u := u) hℓ hu2 hκ
  have iF1 : IntegrableOn F1 (Ioi (u - 1)) := ((iE.add iA).add iD).add iR
  have hcG2 : ContinuousOn G2 (Icc (u - 1) U) := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    apply ContinuousAt.continuousWithinAt
    have hD := continuousAt_Dp (u := u) hℓ0 hw0
    exact (((hD.pow 2).mul (hD.max continuousAt_const).rexp).mul
      ((Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt)).div
      continuousAt_id hw0.ne'
  have iG2 : IntegrableOn G2 (Ioc (u - 1) U) :=
    (hcG2.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- step 1: drop the cut-off
  have hgB : ContinuousOn (fun w => gBase τ ℓ u w / w) (Icc (u - 1) U) := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    exact ((BSaias.gBase_continuousAt τ ℓ u hℓ0 hw0).div continuousAt_id hw0.ne').continuousWithinAt
  have h1 : Mterm τ ℓ u (paperCut τ ℓ) ≤ ∫ w in Ioc (u - 1) U, gBase τ ℓ u w / w := by
    unfold Mterm
    rw [hR.wlo_eq, intervalIntegral.integral_of_le (by linarith)]
    have hiM := BSaias.intervalIntegrable_M (u := u) (by linarith : (1 : ℝ) ≤ τ)
      (by linarith : 3 * τ < ℓ) (BSaias.measurableSet_paperCut τ ℓ)
    rw [hR.wlo_eq] at hiM
    refine setIntegral_mono_on hiM.1 ((hgB.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc fun w hw => ?_
    have hw0 : 0 < w := by linarith [hw.1]
    have hg0 : 0 ≤ gBase τ ℓ u w := by
      unfold gBase
      exact mul_nonneg (div_nonneg (Dickman.rho_pos _).le hρu.le) (Real.exp_pos _).le
    rw [BSaias.gfun_eq]
    by_cases hI : w ∈ paperCut τ ℓ
    · rw [Set.indicator_of_mem hI]
    · rw [Set.indicator_of_notMem hI, zero_div]; positivity
  -- step 2: the pointwise majorant
  have h2 : ∫ w in Ioc (u - 1) U, gBase τ ℓ u w / w ≤
      ((∫ w in Ioc (u - 1) U, F1 w) + 1 / 2 * ∫ w in Ioc (u - 1) U, G2 w) /
        Dickman.rho (u - 1) := by
    rw [← integral_const_mul, ← integral_add (iF1.mono_set Ioc_subset_Ioi_self)
      (iG2.const_mul _), ← integral_div]
    refine setIntegral_mono_on ((hgB.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (((iF1.mono_set Ioc_subset_Ioi_self).add (iG2.const_mul _)).div_const _)
      measurableSet_Ioc fun w hw => ?_
    have hw0 : 0 < w := by linarith [hw.1]
    have hψ : 0 ≤ Dickman.rho (w - 1) / w := div_nonneg (Dickman.rho_pos _).le hw0.le
    have hq := exp_le_quad_pos (Dp ℓ u w)
    have he1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := div_nonneg hκ (by positivity : 0 ≤ w * ℓ); linarith)
    have he0 : 0 < Real.exp (-(kappa τ / (w * ℓ))) := Real.exp_pos _
    have hDeq := Dp_eq (u := u) hℓ0 hw0
    -- `e^{D} ≤ e^{D_Φ} + D' + (1 - e^{D_Φ})|D'| + ½ D'² e^{D'₊}`
    have hpt : Real.exp (Dfun τ ℓ u w) ≤ Real.exp (-(kappa τ / (w * ℓ))) + Dp ℓ u w +
        (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| +
        1 / 2 * (Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0)) := by
      have e : Real.exp (Dfun τ ℓ u w) = Real.exp (-(kappa τ / (w * ℓ))) * Real.exp (Dp ℓ u w) := by
        rw [Dfun_eq, sub_eq_add_neg, Real.exp_add, mul_comm]
      rw [e]
      have hsq : 0 ≤ Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0) := by positivity
      have hab : -Dp ℓ u w ≤ |Dp ℓ u w| := neg_le_abs _
      nlinarith
    have hgB' : gBase τ ℓ u w / w =
        Real.exp (Dfun τ ℓ u w) * (Dickman.rho (w - 1) / w) / Dickman.rho (u - 1) := by
      unfold gBase; field_simp
    rw [hgB', div_le_div_iff_of_pos_right hρu]
    have hF1 : F1 w + 1 / 2 * G2 w = (Real.exp (-(kappa τ / (w * ℓ))) +
        (11 / ℓ * hA u w + (aQ (mOf ℓ w) w - aQ ℓ u)) +
        (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| +
        1 / 2 * (Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0))) *
        (Dickman.rho (w - 1) / w) := by
      simp only [F1, G2]; ring
    rw [hF1, ← hDeq]
    exact mul_le_mul_of_nonneg_right hpt hψ
  -- step 3: remove the cut at `Ū` in the `F1` part
  have h3 : ∫ w in Ioc (u - 1) U, F1 w ≤ ∫ w in Ioi (u - 1), F1 w := by
    rw [integral_Ioi_split' (by linarith : u - 1 ≤ U) iF1]
    have : 0 ≤ ∫ w in Ioi U, F1 w := by
      apply setIntegral_nonneg measurableSet_Ioi
      intro w hw
      have hwU : U < w := hw
      have hw0 : 0 < w := by linarith
      have hψ : 0 ≤ Dickman.rho (w - 1) / w := div_nonneg (Dickman.rho_pos _).le hw0.le
      have he1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := div_nonneg hκ (by positivity : 0 ≤ w * ℓ); linarith)
      have he0 : 0 < Real.exp (-(kappa τ / (w * ℓ))) := Real.exp_pos _
      have hD := Dp_nonneg (u := u) hℓ0 hu2 (by linarith : u ≤ w)
      rw [Dp_eq hℓ0 hw0] at hD
      have : F1 w = (Real.exp (-(kappa τ / (w * ℓ))) +
          (11 / ℓ * hA u w + (aQ (mOf ℓ w) w - aQ ℓ u)) +
          (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w|) * (Dickman.rho (w - 1) / w) := by
        simp only [F1]; ring
      rw [this]
      exact mul_nonneg (by have := abs_nonneg (Dp ℓ u w); nlinarith) hψ
    linarith
  -- step 4: evaluate `∫ F1` over `(u - 1, ∞)`
  have hψint := integral_Ioi_shift_div (a := u - 1) (by linarith)
  have hF1int : ∫ w in Ioi (u - 1), F1 w = Dickman.rho (u - 1) * (1 - PhiBen τ ℓ u) +
      Dickman.rho (u - 1) * (11 / ℓ * jA u) - Dickman.rho (u - 1) * sA ℓ u +
        Dickman.rho (u - 1) * rho1 τ ℓ u := by
    have hsplit : ∫ w in Ioi (u - 1), F1 w =
        (∫ w in Ioi (u - 1), Real.exp (-(kappa τ / (w * ℓ))) * Dickman.rho (w - 1) / w) +
        (∫ w in Ioi (u - 1), 11 / ℓ * hA u w * Dickman.rho (w - 1) / w) +
        (∫ w in Ioi (u - 1), (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w) +
        (∫ w in Ioi (u - 1), (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| *
          Dickman.rho (w - 1) / w) := by
      simp only [F1]
      rw [integral_add, integral_add, integral_add]
      all_goals
        first
        | exact iE
        | exact iA
        | exact iD
        | exact iR
        | exact iE.add iA
        | exact (iE.add iA).add iD
    rw [hsplit]
    have hP : ∫ w in Ioi (u - 1), Real.exp (-(kappa τ / (w * ℓ))) * Dickman.rho (w - 1) / w =
        Dickman.rho (u - 1) * (1 - PhiBen τ ℓ u) := by
      unfold PhiBen Epi
      have e : ∀ w, (1 - Real.exp (-(kappa τ / (w * ℓ)))) * Dickman.rho (w - 1) / w =
          Dickman.rho (w - 1) / w - Real.exp (-(kappa τ / (w * ℓ))) * Dickman.rho (w - 1) / w :=
          fun w => by
        ring
      simp_rw [e]
      rw [integral_sub hψint.1 iE, hψint.2, mul_sub, mul_one, mul_div_cancel₀ _ hρu.ne']
      ring
    have hJ : ∫ w in Ioi (u - 1), 11 / ℓ * hA u w * Dickman.rho (w - 1) / w =
        Dickman.rho (u - 1) * (11 / ℓ * jA u) := by
      unfold jA Epi
      have e : ∀ w, 11 / ℓ * hA u w * Dickman.rho (w - 1) / w =
          11 / ℓ * (hA u w * Dickman.rho (w - 1) / w) := fun w => by ring
      simp_rw [e]
      rw [integral_const_mul, mul_c_div hρu.ne']
    have hS : ∫ w in Ioi (u - 1), (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w =
        -(Dickman.rho (u - 1) * sA ℓ u) := by
      unfold sA Epi
      rw [mul_neg, neg_neg, mul_div_cancel₀ _ hρu.ne']
    have hR1 : ∫ w in Ioi (u - 1), (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w| *
        Dickman.rho (w - 1) / w =
        Dickman.rho (u - 1) * rho1 τ ℓ u := by
      unfold rho1 Epi
      rw [mul_div_cancel₀ _ hρu.ne']
    rw [hP, hJ, hS, hR1]
    ring
  have hrho2 : 1 / 2 * ∫ w in Ioc (u - 1) U, G2 w = Dickman.rho (u - 1) * rho2 τ ℓ u := by
    unfold rho2
    rw [mul_c_div hρu.ne']
  calc Mterm τ ℓ u (paperCut τ ℓ)
      ≤ ((∫ w in Ioc (u - 1) U, F1 w) + 1 / 2 * ∫ w in Ioc (u - 1) U, G2 w) /
          Dickman.rho (u - 1) := h1.trans h2
    _ ≤ ((∫ w in Ioi (u - 1), F1 w) + 1 / 2 * ∫ w in Ioc (u - 1) U, G2 w) /
          Dickman.rho (u - 1) := by
        gcongr
    _ = 1 - PhiBen τ ℓ u + 11 / ℓ * jA u - sA ℓ u + rho1 τ ℓ u + rho2 τ ℓ u := by
        rw [hF1int, hrho2]
        field_simp

end BSaias.Large

end
