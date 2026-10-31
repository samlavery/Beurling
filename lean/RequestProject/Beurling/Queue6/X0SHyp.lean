module

public import RequestProject.Beurling.Queue6.TNPHyp
public import RequestProject.Beurling.Noise.KRTrueX0

/-!
# The standing hypotheses of Proposition 5.18, step (iii), for the realised system

`KR.X0S.Hyp P H X₀⁻ X₀ Z η₁ η₂ ε₁ θ` for `P = PR θ X₀ ω`, `H = Hc X₀`, `X₀⁻ = Xm X₀`
(`x0sHyp_R`): the fields

* `hX0pos`, `hX0` (`log X₀ ≥ 10⁸`), `hX0e` (`X₀⁻ = X₀ - H(X₀)/2`), `hH0` (`H ≥ 0`);
* `hHg` : **`H(y)⁸ ≤ max(y, X₀⁻/2)`** for `y > 0` (`H(y) ≤ y^{1/8}` for `y ≥ X₀`,
  `InitialRange.capH_le_rpow`; below `X₀`, `H = H(X₀)` and `H(X₀)⁸ ≤ e^{0.008Λ} ≤ X₀⁻/2`)

are proved; the inputs are (HBS) on `[1, Z]`, `X₀⁻ ≤ Z`, `0 ≤ θ ≤ 1/2`, and the window count
`count` (step (iii), second bullet).
-/

@[expose] public section

open Set Real Construction BModel CaplLink QueueMono

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

include θ in
/-- `X₀⁻ = X₀ - H(X₀)/2` for `H = Hc X₀`. -/
lemma Xm_eq_Hc : Xm X₀ = (X₀ : ℝ) - Hc X₀ X₀ / 2 := by
  unfold Xm Hc; rw [max_self]

variable (hc : Cond θ X₀)
include hc

/-- **`H(y)⁸ ≤ max(y, X₀⁻/2)`** for `H = Hc X₀`, `y > 0`. -/
lemma Hc_pow8_le (y : ℝ) (_hy : 0 < y) : Hc X₀ y ^ 8 ≤ max y (Xm X₀ / 2) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  have hX1 := one_lt_of_logX hX0 hX
  rcases le_or_gt (X₀ : ℝ) y with h | h
  · have hHy : Hc X₀ y = capH X₀ y := by unfold Hc; rw [max_eq_left h]
    rw [hHy]
    have h1 := InitialRange.capH_le_rpow hX0 hX h
    have h0 : 0 ≤ capH X₀ y := capH_nonneg _ _
    have hy0 : 0 ≤ y := by linarith
    have h2 : capH X₀ y ^ 8 ≤ (y ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_left₀ h0 h1 8
    have h3 : (y ^ (1 / 8 : ℝ)) ^ 8 = y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    rw [h3] at h2
    exact h2.trans (le_max_left _ _)
  · have hHy : Hc X₀ y = capH X₀ X₀ := by unfold Hc; rw [max_eq_right h.le]
    rw [hHy]
    refine le_trans ?_ (le_max_right _ _)
    have hH1 : 1 ≤ capH X₀ X₀ := capH_ge_one hX0 hX le_rfl
    have hl := log_capH_X0 (hc := hc)
    -- `H(X₀)⁸ ≤ e^{0.008 Λ} ≤ X₀/4 ≤ X₀⁻/2`
    have h8 : capH X₀ X₀ ^ 8 ≤ Real.exp (0.008 * Real.log X₀) := by
      rw [← Real.exp_log (show 0 < capH X₀ X₀ ^ 8 by positivity), Real.log_pow]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    have hXm : (X₀ : ℝ) / 2 ≤ Xm X₀ := by
      have h1 := InitialRange.capH_le_rpow hX0 hX le_rfl
      have h4 := four_capH_le hX0 hX le_rfl
      unfold Xm; linarith
    have hE : Real.exp (0.008 * Real.log X₀) ≤ (X₀ : ℝ) / 4 := by
      have e : (X₀ : ℝ) / 4 = Real.exp (Real.log X₀ - Real.log 4) := by
        rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log (by norm_num)]
      rw [e]
      apply Real.exp_le_exp.mpr
      have : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_lt_d9; push_cast; linarith
      linarith
    linarith

/-- **`KR.X0S.Hyp` for the realised system** (Proposition 5.18, step (iii)): all fields but the
inputs (HBS), `X₀⁻ ≤ Z`, `0 ≤ θ ≤ 1/2` and the window count are proved. -/
theorem x0sHyp_R {ω : JitterΩ} {Z η1 η2 θo Y : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1) (hZ : Xm X₀ ≤ Z) (hθ0 : 0 ≤ θo)
    (hθ1 : θo ≤ 1 / 2)
    (hcount : ∀ y, (X₀ : ℝ) ^ 2 / 2 < y → y ≤ Y →
      ((KR.X0S.Win (PR θ X₀ ω) (Hc X₀) (Xm X₀) y).card : ℝ) ≤
        4.21 * Hc X₀ y / X₀ + 2 * Hc X₀ (y / X₀) + 4 + 2 * (y / X₀) ^ (thetaB θo)) :
    KR.X0S.Hyp (PR θ X₀ ω) (Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θo Y where
  hbs := hbs
  hZ := hZ
  hX0pos := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  hX0 := by have := hc.hX; norm_num at this ⊢; linarith
  hX0e := Xm_eq_Hc (θ := θ)
  hH0 := fun y => by unfold Hc; exact capH_nonneg _ _
  hHg := Hc_pow8_le hc
  hθ0 := hθ0
  hθ1 := hθ1
  count := hcount

end Queue6

end
