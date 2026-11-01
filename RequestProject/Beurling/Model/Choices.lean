module

public import RequestProject.Beurling.Model.MarginMine

/-!
# The Model choices of `RealMarginLoc`: `ε = 4·10⁻⁶`, `λ₀ = 1.001`, `j₀ = 1 - ρ_det(X₀)`
-/

@[expose] public section

open Real Construction

namespace BModel

/-! ### The Model choices -/

/-- The slope exponent `ε = 4·10⁻⁶` of (R_H) (`KR.WidthReal.paperWidth_Hc`). -/
noncomputable def epsH : ℝ := 4 / 1000000

/-- `λ₀ = 1.00003` (Proposition 5.33 needs `λ₀ ≤ 1.00003`). -/
noncomputable def lamH : ℝ := 1.00003

/-- The jump of the effective source at `X₀`, `j₀ = T'(X₀⁺) = 1 - ρ_det(X₀)` (§5.1,
"The jump at `X₀`"). -/
noncomputable def jzX (X₀ : ℕ) : ℝ := 1 - Target.rhoDet X₀ (kappaParam X₀) X₀

variable {θ : ℝ} {X₀ : ℕ}

/-- `j₀ = 1 - ρ_det(X₀) ≥ 0` (Lemma 3.3, rigid part, `Model.rhoDet_le`, from (84)). -/
lemma jzX_nonneg (hc : Cond θ X₀) : 0 ≤ jzX X₀ := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hXpos : (0 : ℝ) < X₀ := by linarith
  have h := BModel.rhoDet_le hc.hX hc.hHB (le_refl (X₀ : ℝ))
  have hκ0 := (kappa_facts hc.hX).1
  have hw := window_long hc.hX (le_refl (X₀ : ℝ))
  -- `κ X₀ ≥ (2X₀)^{7/12} ≥ X₀^{1/2} X₀^{1/12} ≥ 3 X₀^{1/2} ≥ 1.5 log X₀`
  have hbig : (531441 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log hXpos] at this; linarith [hc.hX]
  have h12 : (3 : ℝ) ≤ (X₀ : ℝ) ^ ((12 : ℕ)⁻¹ : ℝ) := by
    have := Real.rpow_le_rpow (by norm_num) hbig (show (0 : ℝ) ≤ ((12 : ℕ)⁻¹ : ℝ) by positivity)
    rwa [show (531441 : ℝ) = 3 ^ (12 : ℕ) by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
  have hsplit : (X₀ : ℝ) ^ (7 / 12 : ℝ) =
      (X₀ : ℝ) ^ (1 / 2 : ℝ) * (X₀ : ℝ) ^ ((12 : ℕ)⁻¹ : ℝ) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have h2 : (X₀ : ℝ) ^ (7 / 12 : ℝ) ≤ (2 * X₀) ^ (7 / 12 : ℝ) :=
    Real.rpow_le_rpow hX0 (by linarith) (by norm_num)
  have hlog : Real.log X₀ ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hX0 (by norm_num)
  have hsq0 : 0 ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX0 _
  have hκX : 1.5 * Real.log X₀ ≤ kappaParam X₀ * X₀ := by
    have : 3 * (X₀ : ℝ) ^ (1 / 2 : ℝ) ≤ (X₀ : ℝ) ^ (7 / 12 : ℝ) := by
      rw [hsplit]; nlinarith
    linarith
  have hL : 0 < Real.log X₀ := by linarith [hc.hX]
  have hinv : 1 / (kappaParam X₀ * X₀) ≤ 0.99 / Real.log X₀ := by
    rw [div_le_div_iff₀ (by positivity) hL]
    linarith
  unfold jzX
  linarith

end BModel
