module

public import RequestProject.Beurling.LocalPNT.Extension

/-!
# Step 3 of the proof of Theorem 5.24: the `T₀` part on `(y, ∞)`

For `x ≥ X₀`, `T₀(x) - x = E_rig(x) + R(x)` with `|E_rig(x) + R(x)| ≤ 3κx`
(eq. Erig and Lemma 3.4). Hence, for `σ > 1`,

  `σ ∫_y^∞ (T₀(x) - T₀(y)) x^{-σ-1} dx ≤ (1 + 6κσ) y^{1-σ}/(σ - 1)`

(`tailT_le`); the main term `x` gives exactly `y^{1-σ}/(σ-1)`.
-/

@[expose] public section

open Set Real MeasureTheory Oscillation Construction

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `κ x^{0.4} ≥ 7` for `x ≥ X₀`. -/
lemma kappa_mul_rpow_ge {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : 7 ≤ kap X₀ * x ^ (0.4 : ℝ) := by
  have hX0 := h.X0_pos
  have h1 : (X₀ : ℝ) ^ (0.4 : ℝ) ≤ x ^ (0.4 : ℝ) := Real.rpow_le_rpow hX0.le hx (by norm_num)
  have h2 : kap X₀ * (X₀ : ℝ) ^ (0.4 : ℝ) = (X₀ : ℝ) ^ (1 / 300 : ℝ) := by
    simp only [kap, kappaParam]
    rw [← Real.rpow_add hX0]; norm_num
  have h3 : 7 ≤ (X₀ : ℝ) ^ (1 / 300 : ℝ) := by
    have := rpow_ge_of_half h.logX (v := (X₀ : ℝ)) (by linarith)
      (show (0 : ℝ) ≤ 1 / 300 by norm_num)
    nlinarith [h.logX]
  have hk : 0 < kap X₀ := kappa_pos_aux h.logX
  nlinarith

/-- `|T₀(x) - x| ≤ 3κx` for `x ≥ X₀`. -/
lemma abs_T0_sub_le {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    |T0 θ X₀ α γ xp x - x| ≤ 3 * kap X₀ * x := by
  have hX := h.logX
  have hx0 : 0 < x := lt_of_lt_of_le h.X0_pos hx
  have hx1 : 1 ≤ x := le_trans h.one_le_X0 hx
  rw [h.T0_high hx]
  have hκ0 := kappa_pos_aux hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast h.one_le_X0
  have hr1 := abs_rigidErr_le_fine X₀ hκ0 hX1n hx
  have hR := abs_osc_le h.spacing h.alpha_le hx1 (θ := θ) (γ := γ)
  have hls := logStar_le_rpow hx1 (show (0 : ℝ) < 0.05 by norm_num)
  have hθ2 := h.theta_mem.2
  have p4 : x ^ θ * (logStar x : ℝ) ≤ 21 * x ^ (0.55 : ℝ) := by
    calc x ^ θ * (logStar x : ℝ) ≤ x ^ θ * ((1 / 0.05 + 1) * x ^ (0.05 : ℝ)) := by gcongr
      _ = 21 * x ^ (θ + 0.05) := by rw [Real.rpow_add hx0]; ring
      _ ≤ 21 * x ^ (0.55 : ℝ) := by
          have := Real.rpow_le_rpow_of_exponent_le hx1 (show θ + 0.05 ≤ (0.55 : ℝ) by linarith)
          linarith
  have hk7 := h.kappa_mul_rpow_ge hx
  have hbig : 7 ≤ x ^ (0.05 : ℝ) := by
    have := rpow_ge_of_half hX (v := x) (by linarith [h.X0_pos])
      (show (0 : ℝ) ≤ 0.05 by norm_num)
    nlinarith
  have h55 : 1 ≤ x ^ (0.55 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hK : 42 * x ^ (0.55 : ℝ) + 1 ≤ kap X₀ * x := by
    have : 42 * x ^ (0.55 : ℝ) + 1 ≤ 43 * x ^ (0.55 : ℝ) := by linarith
    have e3 : x ^ (0.55 : ℝ) * x ^ (0.05 : ℝ) * x ^ (0.4 : ℝ) = x := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
    have e : kap X₀ * x = x ^ (0.55 : ℝ) * (x ^ (0.05 : ℝ) * (kap X₀ * x ^ (0.4 : ℝ))) := by
      linear_combination (-(kap X₀)) * e3
    rw [e]
    have : 43 ≤ x ^ (0.05 : ℝ) * (kap X₀ * x ^ (0.4 : ℝ)) := by nlinarith
    nlinarith
  have hκX : kap X₀ * X₀ ≤ kap X₀ * x := mul_le_mul_of_nonneg_left hx hκ0.le
  have a1 := abs_le.mp hr1
  have a2 := abs_le.mp hR
  rw [abs_le]; constructor <;> nlinarith

lemma T0_sub_bounds {x : ℝ} (hy : y ≤ x) :
    |T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y - (x - y)| ≤ 3 * kap X₀ * (x + y) := by
  have hy0 := h.y_ge
  have h1 := h.abs_T0_sub_le (le_trans hy0 hy)
  have h2 := h.abs_T0_sub_le hy0
  have := abs_sub (T0 θ X₀ α γ xp x - x) (T0 θ X₀ α γ xp y - y)
  calc _ = |(T0 θ X₀ α γ xp x - x) - (T0 θ X₀ α γ xp y - y)| := by ring_nf
    _ ≤ |T0 θ X₀ α γ xp x - x| + |T0 θ X₀ α γ xp y - y| := this
    _ ≤ 3 * kap X₀ * x + 3 * kap X₀ * y := add_le_add h1 h2
    _ = _ := by ring

/-- **The `T₀` tail** (Step 3): `σ∫_y^∞ (T₀(x) - T₀(y)) x^{-σ-1} dx ≤ (1 + 6κσ) y^{1-σ}/(σ-1)`,
and the integrand is integrable. -/
theorem tailT_le {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x => (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1)) (Ioi y) ∧
    σ * ∫ x in Ioi y, (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1) ≤
      (1 + 6 * kap X₀ * σ) * y ^ (1 - σ) / (σ - 1) := by
  set κ := kap X₀
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hκ0 : 0 < κ := kappa_pos_aux h.logX
  have hi0 : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hy0
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hy0
  have hv0 : ∫ x in Ioi y, x ^ (-σ) = y ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hy0]
    rw [show -σ + 1 = 1 - σ by ring, show (1 - σ) = -(σ - 1) by ring, div_neg, neg_div, neg_neg]
  have hv1 : ∫ x in Ioi y, x ^ (-σ - 1) = y ^ (-σ) / σ := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hy0]
    rw [show -σ - 1 + 1 = -σ by ring, div_neg, neg_div, neg_neg]
  have hxx : ∀ x ∈ Ioi y, x * x ^ (-σ - 1) = x ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hy0 hx
    rw [Real.rpow_sub_one hx0.ne']; field_simp
  set B : ℝ → ℝ := fun x => (1 + 3 * κ) * x ^ (-σ) + (3 * κ - 1) * y * x ^ (-σ - 1)
  have hiB : IntegrableOn B (Ioi y) := (hi0.const_mul _).add (hi1.const_mul _)
  have hm : AEStronglyMeasurable
      (fun x => (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1)) (volume.restrict (Ioi y)) :=
    ((h.T0_monotone.measurable.sub_const _).mul (measurable_id.pow_const _)).aestronglyMeasurable
  have hpt : ∀ x ∈ Ioi y, |(T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1)| ≤
      (1 + 3 * κ) * x ^ (-σ) + (1 + 3 * κ) * y * x ^ (-σ - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hy0 hx
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have hb := h.T0_sub_bounds (le_of_lt hx)
    have hmon : 0 ≤ T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y :=
      sub_nonneg.mpr (h.T0_monotone (le_of_lt hx))
    rw [abs_mul, abs_of_nonneg hmon, abs_of_nonneg hp, ← hxx x hx]
    have := (abs_le.mp hb).2
    nlinarith
  have hiT : IntegrableOn (fun x => (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1))
      (Ioi y) := by
    refine Integrable.mono' ((hi0.const_mul (1 + 3 * κ)).add (hi1.const_mul ((1 + 3 * κ) * y)))
      hm ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    rw [Real.norm_eq_abs]
    have := hpt x hx
    simpa [mul_assoc] using this
  refine ⟨hiT, ?_⟩
  have hle : ∫ x in Ioi y, (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1) ≤
      ∫ x in Ioi y, B x := by
    refine setIntegral_mono_on hiT hiB measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans hy0 hx
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have hb := h.T0_sub_bounds (le_of_lt hx)
    have := (abs_le.mp hb).2
    simp only [B, ← hxx x hx]
    nlinarith
  have hBv : ∫ x in Ioi y, B x = (1 + 3 * κ) * (y ^ (1 - σ) / (σ - 1)) +
      (3 * κ - 1) * y * (y ^ (-σ) / σ) := by
    simp only [B]
    rw [integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul, integral_const_mul,
      hv0, hv1]
  have hyy : y * y ^ (-σ) = y ^ (1 - σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hy0, Real.rpow_one]
  have hσ1 : 0 < σ - 1 := by linarith
  have hσ0 : 0 < σ := by linarith
  have hyp : 0 ≤ y ^ (1 - σ) := Real.rpow_nonneg hy0.le _
  calc σ * ∫ x in Ioi y, (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1)
      ≤ σ * ((1 + 3 * κ) * (y ^ (1 - σ) / (σ - 1)) + (3 * κ - 1) * y * (y ^ (-σ) / σ)) := by
        rw [← hBv]; exact mul_le_mul_of_nonneg_left hle hσ0.le
    _ = y ^ (1 - σ) * ((1 + 3 * κ) * σ / (σ - 1) + (3 * κ - 1)) := by
        rw [← hyy]; field_simp
    _ ≤ (1 + 6 * κ * σ) * y ^ (1 - σ) / (σ - 1) := by
        rw [mul_div_assoc]
        rw [show (1 + 6 * κ * σ) * y ^ (1 - σ) / (σ - 1) =
          y ^ (1 - σ) * ((1 + 6 * κ * σ) / (σ - 1)) by ring]
        apply mul_le_mul_of_nonneg_left _ hyp
        rw [le_div_iff₀ hσ1]
        have e : ((1 + 3 * κ) * (σ / (σ - 1)) + (3 * κ - 1)) * (σ - 1) =
            (1 + 3 * κ) * σ + (3 * κ - 1) * (σ - 1) := by field_simp
        rw [e]; nlinarith

end LPHyp

end LocalPNT

end
