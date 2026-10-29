module

public import RequestProject.Beurling.LocalPNT.LPa
public import RequestProject.Beurling.LocalPNT.ZBlow

/-!
# Step 7 of the proof of Theorem 5.24: growth of `ζ^♯` on `σ ≥ 1 - 8/Λ`

`ζ^♯ = s/(s-1) + Ê + R̂ + D̂^♯` with (LP-b) (Lemma 4.3, `a = 8`), (LP-c) and Step 1:

  `|ζ^♯(s) - s/(s-1)| ≤ C₈ (1 + κ|s|) e^γ Λ + (1 + 5 X₀^{-0.48}) |s| + 1`

(`norm_zetaSharp_sub_le`), and near the pole `|(s-1) ζ^♯(s) - 1| ≤ 1/2` on `|s - 1| ≤ 1/8`
(Step 6, `near_pole`).
-/

@[expose] public section

open Set Real Complex Construction Decomp

namespace LocalPNT

/-- `C₈ = 2.1 e^8 + 5 e^{Ein(8)}`. -/
noncomputable def C8 : ℝ := 2.1 * Real.exp 8 + 5 * Real.exp (Ein 8)

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `D̂^♯` on `σ ≥ 1 - 8/Λ`: `|D̂^♯(s)| ≤ 5 X₀^{-0.48} |s| + 1`. -/
lemma norm_earlyNoise_le' {s : ℂ} (hs : 1 - 8 / Real.log X₀ ≤ s.re) :
    ‖earlyNoise (lag0 P θ X₀ α γ xp) y s‖ ≤ 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ)) * ‖s‖ + 1 := by
  have hX := h.logX
  have h8 : 8 / Real.log X₀ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
    (by norm_num) hX
  have htp := (thetaPrime_bounds h.theta_mem hX).2
  have hgap : 0.48 ≤ s.re - thetaPrime θ X₀ := by linarith
  have hb := h.norm_earlyNoise_le (s := s) (by linarith)
  have hXm := h.Xm_pos
  have hX0 := h.X0_pos
  have hy0 : 0 < y := lt_of_lt_of_le hX0 h.y_ge
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  have h1 : y ^ (thetaPrime θ X₀ - s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have h2 : Xm ^ (thetaPrime θ X₀ - s.re) ≤ ((X₀ : ℝ) / 2) ^ (-(0.48 : ℝ)) := by
    calc Xm ^ (thetaPrime θ X₀ - s.re) ≤ Xm ^ (-(0.48 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [h.Xm_ge_e7]) (by linarith)
      _ ≤ ((X₀ : ℝ) / 2) ^ (-(0.48 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h.Xm_ge (by norm_num)
  have h3 : ((X₀ : ℝ) / 2) ^ (-(0.48 : ℝ)) = 2 ^ (0.48 : ℝ) * (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by
    rw [Real.div_rpow hX0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have h4 : (2 : ℝ) ^ (0.48 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (0.48 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hXp : 0 ≤ (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by positivity
  have hfrac : ‖s‖ * Xm ^ (thetaPrime θ X₀ - s.re) / (s.re - thetaPrime θ X₀) ≤
      5 * (X₀ : ℝ) ^ (-(0.48 : ℝ)) * ‖s‖ := by
    rw [div_le_iff₀ (by linarith)]
    have hn := norm_nonneg s
    have : Xm ^ (thetaPrime θ X₀ - s.re) ≤ 2 * (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by
      rw [h3] at h2; nlinarith
    have h5 := mul_le_mul_of_nonneg_left this hn
    have h6 : 0 ≤ 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ)) * ‖s‖ := by positivity
    have h7 := mul_le_mul_of_nonneg_left hgap h6
    nlinarith
  linarith

/-- **Growth** (Step 7): `|ζ^♯(s) - s/(s-1)| ≤ C₈ (1 + κ|s|) e^γ Λ + (1 + 5 X₀^{-0.48}) |s| + 1`
on `σ ≥ 1 - 8/Λ`, `s ≠ 1`. -/
theorem norm_zetaSharp_sub_le {s : ℂ} (hs : 1 - 8 / Real.log X₀ ≤ s.re) (hs1 : s ≠ 1) :
    ‖zetaSharp P θ X₀ α γ xp y s - s / (s - 1)‖ ≤
      C8 * (1 + kap X₀ * ‖s‖) * Real.exp Real.eulerMascheroniConstant * Real.log X₀ +
        (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * ‖s‖ + 1 := by
  have hE := lemma_4_3' h.logX (a := 8) (by norm_num) le_rfl hs hs1
  have hR := (lpc (θ := θ) (γ := γ) (by linarith [h.theta_mem.2]) h.logX h.alpha_le h.xp_zero
    h.xp_succ hs).2
  have hD := h.norm_earlyNoise_le' hs
  have e : zetaSharp P θ X₀ α γ xp y s - s / (s - 1) =
      EHat X₀ s + oscHatSum θ α γ xp s + earlyNoise (lag0 P θ X₀ α γ xp) y s := by
    unfold zetaSharp EHat; ring
  rw [e]
  calc _ ≤ ‖EHat X₀ s‖ + ‖oscHatSum θ α γ xp s‖ + ‖earlyNoise (lag0 P θ X₀ α γ xp) y s‖ :=
        norm_add₃_le
    _ ≤ _ := by unfold C8; linarith

/-- **Step 6**: on `|s - 1| ≤ 1/8`, `σ ≥ 1 - 8/Λ`: `|(s-1) ζ^♯(s) - 1| ≤ 4|s - 1|`. -/
theorem near_pole' {s : ℂ} (hs : 1 - 8 / Real.log X₀ ≤ s.re) (hs1 : ‖s - 1‖ ≤ 1 / 8)
    (hs1' : s ≠ 1) :
    ‖(s - 1) * zetaSharp P θ X₀ α γ xp y s - 1‖ ≤ 4 * ‖s - 1‖ := by
  have hX := h.logX
  have hE := EHat_add_one_near_pole hX hs hs1 hs1'
  have hR := (lpc (θ := θ) (γ := γ) (by linarith [h.theta_mem.2]) hX h.alpha_le h.xp_zero
    h.xp_succ hs).1
  have hD := h.norm_earlyNoise_le' hs
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  have e : (s - 1) * zetaSharp P θ X₀ α γ xp y s - 1 =
      (s - 1) * ((EHat X₀ s + 1) + oscHatSum θ α γ xp s +
        earlyNoise (lag0 P θ X₀ α γ xp) y s) := by
    unfold zetaSharp EHat; field_simp; ring
  rw [e, norm_mul]
  have hsn : ‖s‖ ≤ 2 := by
    have := norm_sub_norm_le s 1; simp at this; linarith
  have hX0 := h.X0_pos
  have hsmall1 : Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) ≤ 1 / 100 := by
    have h20 : (20 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀)
      rw [Real.exp_log hX0] at this; linarith
    have : Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) ≤ Real.exp (-5) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h5 : Real.exp (-5) ≤ 1 / 100 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp (5 : ℝ)
      have h25 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      have he := Real.exp_one_gt_d9
      rw [h25]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 5]
    linarith
  have hsmall2 : (X₀ : ℝ) ^ (-(0.48 : ℝ)) ≤ 1 / 100 := by
    have := rpow_ge_of_half hX (v := (X₀ : ℝ)) (by linarith) (show (0 : ℝ) ≤ 0.48 by norm_num)
    rw [Real.rpow_neg hX0.le, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hn := norm_nonneg s
  have hsum : ‖(EHat X₀ s + 1) + oscHatSum θ α γ xp s + earlyNoise (lag0 P θ X₀ α γ xp) y s‖ ≤
      4 := by
    have : ‖(EHat X₀ s + 1) + oscHatSum θ α γ xp s + earlyNoise (lag0 P θ X₀ α γ xp) y s‖ ≤
        ‖EHat X₀ s + 1‖ + ‖oscHatSum θ α γ xp s‖ + ‖earlyNoise (lag0 P θ X₀ α γ xp) y s‖ :=
      norm_add₃_le
    have a1 : ‖s‖ * Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) ≤ 2 * (1 / 100) :=
      mul_le_mul hsn hsmall1 (Real.exp_pos _).le (by norm_num)
    have a2 : 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ)) * ‖s‖ ≤ 5 * (1 / 100) * 2 := by
      have := mul_le_mul hsmall2 hsn hn (by norm_num); nlinarith
    linarith
  calc ‖s - 1‖ * ‖(EHat X₀ s + 1) + oscHatSum θ α γ xp s + earlyNoise (lag0 P θ X₀ α γ xp) y s‖
      ≤ ‖s - 1‖ * 4 := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 4 * ‖s - 1‖ := by ring

/-- **Step 6**: on `|s - 1| ≤ 1/8`, `σ ≥ 1 - 8/Λ`: `|(s-1) ζ^♯(s) - 1| ≤ 1/2`. -/
theorem near_pole {s : ℂ} (hs : 1 - 8 / Real.log X₀ ≤ s.re) (hs1 : ‖s - 1‖ ≤ 1 / 8)
    (hs1' : s ≠ 1) :
    ‖(s - 1) * zetaSharp P θ X₀ α γ xp y s - 1‖ ≤ 1 / 2 := by
  have := h.near_pole' hs hs1 hs1'
  linarith

end LPHyp

end LocalPNT

end
