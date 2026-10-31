module

public import RequestProject.Beurling.LocalPNT.Defs
public import RequestProject.Beurling.Construction.HBSDerive

/-!
# Step 2 of the proof of Theorem 5.24: (HBS) on `[1, y]` from (LP-a)

On `[X₀, y]`, `T₀ - ⌊·⌋ = E_rig + R + {·}`, so (LP-a), the rigid bound (eq. Erig) and
`|R| ≤ 2u^θ log^* u` (Lemma 3.4) give (HBS) on `[1, y]` with `X₀⁻ = Xm`, `η₁ = η₂ = 10⁻³` and the
error profile `ε₁ = hbsEps X₀` of `Construction/HBSEps.lean`. Hence Lemma 5.1 holds on `[1, y]`.
-/

@[expose] public section

open Set Real Oscillation Construction

namespace LocalPNT

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}

lemma rpow_X0_pos (hX : 10 ^ 8 ≤ Real.log X₀) : (0 : ℝ) < X₀ := logX_pos_aux hX

/-- `(log Λ)² ≤ 16 Λ^{1/2}`. -/
lemma log_sq_le_sqrt {Λ : ℝ} (hΛ : 1 ≤ Λ) : Real.log Λ ^ 2 ≤ 16 * Λ ^ (1 / 2 : ℝ) := by
  have h1 : Real.log Λ ≤ Λ ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have h2 : (Λ ^ (1 / 4 : ℝ)) ^ 2 = Λ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc Real.log Λ ^ 2 ≤ (Λ ^ (1 / 4 : ℝ) / (1 / 4)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * Λ ^ (1 / 2 : ℝ) := by rw [div_pow, h2]; ring

/-- `8 (log Λ)²/Λ ≤ 0.013` for `Λ ≥ 10⁸`. -/
lemma eight_logsq_div_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    8 * Real.log Λ ^ 2 / Λ ≤ 0.013 := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 := log_sq_le_sqrt (Λ := Λ) (by linarith)
  have hs : (10 : ℝ) ^ 4 ≤ Λ ^ (1 / 2 : ℝ) := by
    have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ Λ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hΛ (by norm_num)
    rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
      rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num] at this
  have hsq : Λ ^ (1 / 2 : ℝ) * Λ ^ (1 / 2 : ℝ) = Λ := by
    rw [← Real.rpow_add hΛ0]; norm_num
  rw [div_le_iff₀ hΛ0]
  nlinarith

/-- `θ' ≤ 0.51` and `θ' ≥ θ + 0.01`. -/
lemma thetaPrime_bounds (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) :
    θ + 0.01 ≤ thetaPrime θ X₀ ∧ thetaPrime θ X₀ ≤ 0.51 := by
  refine ⟨le_max_left _ _, max_le (by linarith [hθ.2]) ?_⟩
  have := eight_logsq_div_le hX
  linarith

namespace LPHyp

variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma X0_pos : (0 : ℝ) < X₀ := logX_pos_aux h.logX

lemma one_le_X0 : (1 : ℝ) ≤ X₀ := one_le_X_aux h.logX

lemma X0_ge : Real.exp (10 ^ 8) ≤ X₀ := by
  have := Real.exp_log h.X0_pos
  rw [← this]; exact Real.exp_le_exp.mpr h.logX

lemma spacing : Spacing xp :=
  ⟨by have := Real.one_le_exp (sq_nonneg (X₀ : ℝ)); linarith [h.xp_zero], h.xp_succ⟩

lemma X0_le_xp : (X₀ : ℝ) ≤ xp 0 := by
  have h1 := Real.add_one_le_exp ((X₀ : ℝ) ^ 2)
  have h2 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 2 := by nlinarith [h.one_le_X0]
  linarith [h.xp_zero]

lemma osc_X0 : osc θ α γ xp X₀ = 0 :=
  Target.osc_eq_zero_of_le h.spacing h.X0_pos h.X0_le_xp

omit h in
/-- `T₀ = ⌊·⌋` below `X₀`. -/
lemma T0_low {u : ℝ} (hu : u < X₀) : T0 θ X₀ α γ xp u = ⌊u⌋₊ := by
  simp only [T0, Target.target, if_pos hu]

/-- `T₀(u) = u + E_rig(u) + R(u)` for `u ≥ X₀`. -/
lemma T0_high {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    T0 θ X₀ α γ xp u = u + Target.rigidErr X₀ (kap X₀) u + osc θ α γ xp u := by
  simp only [T0, Target.target, if_neg (not_lt.mpr hu), Target.rigidErr, h.osc_X0,
    intervalIntegral.integral_zero]
  ring

lemma Xm_ge_e7 : (10 : ℝ) ^ 7 ≤ Xm := by
  have : (2 * 10 ^ 7 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log h.X0_pos] at this; linarith [h.logX]
  linarith [h.Xm_ge]

lemma Xm_pos : 0 < Xm := lt_of_lt_of_le (by norm_num) h.Xm_ge_e7

/-- `N = ⌊·⌋` below `X₀⁻`. -/
lemma N_low {u : ℝ} (hu : u < Xm) : P.N u = ⌊u⌋₊ := by
  rw [h.lpa_low u hu, LPHyp.T0_low (lt_of_lt_of_le hu h.Xm_le)]

lemma lag_le {u : ℝ} (h1 : Xm ≤ u) (h2 : u ≤ y) :
    |P.N u - T0 θ X₀ α γ xp u| ≤ u ^ thetaPrime θ X₀ :=
  (h.lpa_high u h1 h2).1.trans (h.lpa_high u h1 h2).2

/-- **(HBS)**, the error bound: `|N(v) - ⌊v⌋| ≤ ε₁(v) v` on `[X₀⁻, y]`. -/
lemma hbs_err {v : ℝ} (h1 : Xm ≤ v) (h2 : v ≤ y) :
    |P.N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
  have hX := h.logX
  have hv0 : 0 < v := lt_of_lt_of_le h.Xm_pos h1
  have hv1 : 1 ≤ v := le_trans (by linarith [h.Xm_ge_e7]) h1
  have htp := (thetaPrime_bounds h.theta_mem hX).2
  have hlag := h.lag_le h1 h2
  have p1 : v ^ thetaPrime θ X₀ ≤ v ^ (0.6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)
  have p3 : 1 ≤ v ^ (0.6 : ℝ) := Real.one_le_rpow hv1 (by norm_num)
  have hmin0 : 0 ≤ min (kappaParam (X₀ : ℝ) * v + kappaParam X₀ * X₀ + 1)
      (Rankin.smoothCount X₀ (2 * v) : ℝ) :=
    le_min (by have := kappa_pos_aux hX; have := h.X0_pos; positivity) (Nat.cast_nonneg _)
  rw [hbsEps_mul_self hv0]
  rcases lt_or_ge v X₀ with hlow | hhigh
  · rw [LPHyp.T0_low hlow] at hlag
    rw [abs_le] at hlag ⊢
    constructor <;> nlinarith
  · rw [h.T0_high hhigh] at hlag
    have hκ0 := kappa_pos_aux hX
    have hκ1 : kappaParam (X₀ : ℝ) ≤ 1 := (kappa_le_aux hX).trans (by
      rw [div_le_one (by nlinarith)]; nlinarith)
    have hX1n : 1 ≤ X₀ := by exact_mod_cast h.one_le_X0
    have hr1 := abs_rigidErr_le_fine X₀ hκ0 hX1n hhigh
    have hr2 := Target.abs_rigidErr_le X₀ hκ0 hκ1 hX1n hhigh
    have hrig := le_min hr1 hr2
    have hR := abs_osc_le h.spacing h.alpha_le hv1 (θ := θ) (γ := γ)
    have hls := logStar_le_rpow hv1 (show (0 : ℝ) < 0.05 by norm_num)
    have hbig := rpow_ge_of_half hX (v := v) (by linarith [h.X0_pos])
      (show (0 : ℝ) ≤ 0.05 by norm_num)
    have h55 : 0 < v ^ (0.55 : ℝ) := by positivity
    have hθ2 := h.theta_mem.2
    have p4 : v ^ θ * (logStar v : ℝ) ≤ 3 * v ^ (0.6 : ℝ) := by
      calc v ^ θ * (logStar v : ℝ) ≤ v ^ θ * ((1 / 0.05 + 1) * v ^ (0.05 : ℝ)) := by gcongr
        _ = 21 * v ^ (θ + 0.05) := by rw [Real.rpow_add hv0]; ring
        _ ≤ 21 * v ^ (0.55 : ℝ) := by
            have := Real.rpow_le_rpow_of_exponent_le hv1 (show θ + 0.05 ≤ (0.55 : ℝ) by linarith)
            linarith
        _ ≤ 3 * v ^ (0.6 : ℝ) := by
            rw [show (0.6 : ℝ) = 0.55 + 0.05 by norm_num, Real.rpow_add hv0]
            nlinarith
    have hfl1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0.le
    have hfl2 : v < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
    have e := abs_le.mp hlag
    have a2 := abs_le.mp hR
    have a3 := abs_le.mp hrig
    rw [abs_le]; constructor <;> nlinarith

/-- **(HBS) on `[1, y]`** (Step 2 of the proof of Theorem 5.24). -/
theorem hbs : P.HBS Xm y (1 / 1000) (1 / 1000) (hbsEps X₀) where
  X0m_ge := h.Xm_ge_e7
  eta1_nonneg := by norm_num
  eta1_le := le_rfl
  eta2_nonneg := by norm_num
  eta2_le := le_rfl
  floor_eq := fun v _ h2 _ => h.N_low h2
  err := fun v h1 h2 => h.hbs_err h1 h2
  eta2 := fun v h1 _ => hbsEps_mul_log_le h.logX (by linarith [h.Xm_ge])
  eta1 := fun x K w hw => hbsEps_dyadic_sum_le h.logX K w (fun k hk =>
    ⟨(hw k hk).1, (hw k hk).2.1, by linarith [(hw k hk).2.2.1, h.Xm_ge]⟩)

end LPHyp

end LocalPNT

end
