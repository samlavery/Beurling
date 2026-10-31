module

public import RequestProject.Beurling.Theorem410Mertens
public import RequestProject.Beurling.ZBIdentity

/-!
# Theorem 4.10 with the concrete base factor

In `Theorem410InputsMertens` the base factor `Z_B` was an arbitrary function, assumed holomorphic
and within `e^{-X₀²/4}` of `Z_∞` on `1/2 ≤ σ ≤ 2`, `|t| ≥ T` (the first statement of Lemma 4.2).
Here `Z_B` is the concrete continuation `ZBcont X₀ κ` of the paper's base factor (identity (15),
`ZBpaper_eq_ZBcont`), and these two assumptions are proved (`lemma_4_2_first_statement`) under
`0 < κ ≤ 1`, `κ T ≥ e^{X₀²/3}` (in the paper `κ Γ₁/2 ≥ e^{0.49 X₀²}/2`).
The resulting refined hypothesis `Theorem21InputsZB` still implies Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor

namespace BaseFactor

lemma twentyfour_le_of_log {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀) : 24 ≤ X₀ := by
  by_contra h
  push_neg at h
  rcases Nat.eq_zero_or_pos X₀ with h0 | h0
  · subst h0; simp at hX; linarith
  · have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < X₀ by exact_mod_cast h0)
    have h2 : (X₀ : ℝ) ≤ 23 := by exact_mod_cast (by omega : X₀ ≤ 23)
    linarith

/-- **Lemma 4.2, first statement, for the concrete `Z_B`**: if `0 < κ ≤ 1`, `κ T ≥ e^{X₀²/3}`
and `X₀ ≥ 24`, then on `1/2 ≤ σ ≤ 2`, `|t| ≥ T` the base factor `Z_B` is holomorphic and
`|Z_B - Z_∞| ≤ e^{-X₀²/4}`. -/
theorem lemma_4_2_first_statement {X₀ : ℕ} (hX : 24 ≤ X₀) {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hT : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T) :
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ (ZBcont X₀ κ) z) ∧
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZBcont X₀ κ z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4))) := by
  have hT0 : 0 < T := by
    by_contra h; push_neg at h
    have := mul_nonpos_of_nonneg_of_nonpos hκ.le h
    linarith [Real.exp_pos ((X₀ : ℝ) ^ 2 / 3)]
  refine ⟨fun z h1 _ h3 => ?_, fun z h1 h2 h3 => ?_⟩
  · refine differentiableAt_ZBcont X₀ hκ (by linarith) ?_
    rintro rfl; simp at h3; linarith
  · exact norm_ZBcont_sub_Zinf_le hX hκ hκ1 h1 h2
      (hT.trans (mul_le_mul_of_nonneg_left h3 hκ.le))

/-- **The paper's heights are large enough.** With the paper's parameters (`θ ≤ 1/2`,
`κ, κ₀ ≥ 1/X₀`, `κ ≤ 1`, `log x ≥ X₀²` since `x ≥ x₁ ≥ e^{X₀²}`), the height
`Γ = κ₀ x^{1-θ}/(2 log x)` of Lemma 4.8 satisfies `κ (Γ - 1/2) ≥ e^{X₀²/3}`. So the condition
`κ T ≥ e^{X₀²/3}` of `lemma_4_2_first_statement` holds with `T = Γ - 1/2`, and the condition
`κ Γ ≥ e^{X₀²/3}` of Lemma 4.8(i) holds as well. -/
theorem paper_height_large {θ κ κ₀ x : ℝ} {X₀ : ℕ} (hθ : θ ≤ 1 / 2) (hX : 24 ≤ X₀)
    (hκ : 1 / (X₀ : ℝ) ≤ κ) (hκ1 : κ ≤ 1) (hκ₀ : 1 / (X₀ : ℝ) ≤ κ₀) (hx0 : 0 < x)
    (hx : (X₀ : ℝ) ^ 2 ≤ Real.log x) :
    Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤
      κ * (κ₀ * x ^ (1 - θ) / (2 * Real.log x ^ 3) - 1 / 2) := by
  have hX' : (24 : ℝ) ≤ X₀ := by exact_mod_cast hX
  set L := Real.log x with hLdef
  have hL : 576 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  have hx1 : 1 ≤ x := by
    by_contra h; push_neg at h
    have := Real.log_nonpos hx0.le h.le; linarith
  -- `x^{1-θ} ≥ e^{L/2}`
  have hxp : Real.exp (L / 2) ≤ x ^ (1 - θ) := by
    have h1 : x ^ (1 / 2 : ℝ) ≤ x ^ (1 - θ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_def_of_pos hx0] at h1
    rw [show L / 2 = Real.log x * (1 / 2) by rw [hLdef]; ring]; exact h1
  -- `κ κ₀ ≥ 1/X₀²`
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hkk : 1 / (X₀ : ℝ) ^ 2 ≤ κ * κ₀ := by
    have := mul_le_mul hκ hκ₀ (by positivity) (le_trans (by positivity) hκ)
    rw [show 1 / (X₀ : ℝ) * (1 / X₀) = 1 / (X₀ : ℝ) ^ 2 by ring] at this; exact this
  -- `L³ ≤ 82944 e^{L/24}` and `X₀² ≤ 24 e^{L/24}`
  have hL3 : L ^ 3 ≤ 82944 * Real.exp (L / 24) := by
    have := Real.pow_div_factorial_le_exp (L / 24) (by positivity) 3
    norm_num [Nat.factorial] at this
    rw [div_pow] at this
    norm_num at this
    linarith
  have hLe : L ≤ 24 * Real.exp (L / 24) := by
    have := Real.add_one_le_exp (L / 24); linarith
  have hE := Real.exp_pos (L / 24)
  have hden : 2 * (X₀ : ℝ) ^ 2 * L ^ 3 ≤ 3981312 * Real.exp (L / 12) := by
    have e : Real.exp (L / 12) = Real.exp (L / 24) * Real.exp (L / 24) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h1 : (X₀ : ℝ) ^ 2 ≤ 24 * Real.exp (L / 24) := hx.trans hLe
    have h2 := mul_le_mul h1 hL3 (by positivity) (by positivity)
    nlinarith
  -- `e^{48} ≥ 8 · 10⁶`
  have h48 : 7962624 ≤ Real.exp (L / 12) := by
    have h1 := Real.pow_div_factorial_le_exp 48 (by norm_num) 6
    norm_num [Nat.factorial] at h1
    have h2 : Real.exp 48 ≤ Real.exp (L / 12) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- main estimate
  have hden0 : 0 < 2 * L ^ 3 := by positivity
  have hmain : 2 * Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * (κ₀ * x ^ (1 - θ) / (2 * L ^ 3)) := by
    have e1 : κ * (κ₀ * x ^ (1 - θ) / (2 * L ^ 3)) = (κ * κ₀) * x ^ (1 - θ) / (2 * L ^ 3) := by
      ring
    rw [e1, le_div_iff₀ hden0]
    have h1 : (1 / (X₀ : ℝ) ^ 2) * Real.exp (L / 2) ≤ (κ * κ₀) * x ^ (1 - θ) :=
      mul_le_mul hkk hxp (Real.exp_pos _).le (le_trans (by positivity) hkk)
    have h2 : 2 * Real.exp ((X₀ : ℝ) ^ 2 / 3) * (2 * L ^ 3) ≤
        (1 / (X₀ : ℝ) ^ 2) * Real.exp (L / 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      have e2 : Real.exp (L / 2) = Real.exp (L / 3) * Real.exp (L / 12) * Real.exp (L / 12) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have h3 : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ Real.exp (L / 3) := Real.exp_le_exp.mpr (by linarith)
      rw [e2]
      have hA := Real.exp_pos ((X₀ : ℝ) ^ 2 / 3)
      have hB := Real.exp_pos (L / 12)
      calc 2 * Real.exp ((X₀ : ℝ) ^ 2 / 3) * (2 * L ^ 3) * (X₀ : ℝ) ^ 2
          = 2 * Real.exp ((X₀ : ℝ) ^ 2 / 3) * (2 * (X₀ : ℝ) ^ 2 * L ^ 3) := by ring
        _ ≤ 2 * Real.exp ((X₀ : ℝ) ^ 2 / 3) * (3981312 * Real.exp (L / 12)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ = Real.exp ((X₀ : ℝ) ^ 2 / 3) * 7962624 * Real.exp (L / 12) := by ring
        _ ≤ Real.exp (L / 3) * Real.exp (L / 12) * Real.exp (L / 12) := by
            apply mul_le_mul_of_nonneg_right _ hB.le
            exact mul_le_mul h3 h48 (by norm_num) (Real.exp_pos _).le
    linarith
  have hone : 1 ≤ Real.exp ((X₀ : ℝ) ^ 2 / 3) := Real.one_le_exp (by positivity)
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  rw [mul_sub]
  nlinarith

end BaseFactor

namespace DesignedZero

/-- **The inputs of Theorem 4.10 with the concrete base factor.** As `Theorem410InputsMertens`,
but `Z_B` is the concrete `ZBcont X₀ κ` (the continuation of the paper's `Z_B`), and the two
assumptions of Lemma 4.2 on `Z_B` are replaced by `0 < κ ≤ 1` and `κ T ≥ e^{X₀²/3}`. -/
def Theorem410InputsZB (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ T κ₀ η : ℝ) (α γ xp a : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    10 ^ 4 ≤ Real.log X₀ ∧ 0 < κ ∧ κ ≤ 1 ∧ Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T ∧
    (∀ k, DesignParams θ (Real.log X₀) κ₀ (α k) (γ k) (xp k)) ∧
    (∀ k, T + 1 / 2 ≤ γ k) ∧
    (∀ k, 0.6 ≤ ‖ZBcont X₀ κ (1 + γ k * I)‖) ∧
    (∀ k, 1 ≤ α k ∧ α k ≤ 2) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k ≤ xp k) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (thetaB θ) A u ∧ Monotone ς ∧
    (∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) ∧
    (∀ k, ∀ τ : ℝ, |τ - γ k| ≤ 1 →
      absorbedBound ς (designRadius (xp k)) (|τ| ^ (1 / (1 - thetaB θ))) ≤ 1 / 16) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (thetaB θ) A u s) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)), ‖Dlt k s‖ ≤ 1 / 16)

theorem Theorem410InputsZB.mertens {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsZB θ F) :
    Theorem410InputsMertens θ F := by
  obtain ⟨X₀, κ, T, κ₀, η, α, γ, xp, a, D, Dlt, A, u, ς, hX, hκ, hκ1, hT, hP, hγT,
    hc, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hB, hdec, hDlt⟩ := h
  obtain ⟨hdiff, hclose⟩ := lemma_4_2_first_statement (twentyfour_le_of_log hX) hκ hκ1 hT
  exact ⟨X₀, T, κ₀, η, α, γ, xp, a, ZBcont X₀ κ, D, Dlt, A, u, ς, hX, hdiff, hclose, hP, hγT,
    hc, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hB, hdec, hDlt⟩

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system with the concrete base factor. -/
def TheoremAInputsZB (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsZB θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the concrete base factor (Lemma 4.2 fully derived). -/
def Theorem21InputsZB : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsZB θ X₀ (P ω)

theorem theorem21InputsMertens_of_ZB (h : Theorem21InputsZB) : Theorem21InputsMertens := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.mertens⟩⟩

/-- The refined hypothesis (concrete base factor) implies Theorem 2.1. -/
theorem theorem21_of_ZB (h : Theorem21InputsZB) : Theorem21 :=
  theorem21_of_mertens (theorem21InputsMertens_of_ZB h)

/-- **Corollary 2.2** from the refined hypothesis with the concrete base factor. -/
theorem corollary_2_2_of_ZB (h : Theorem21InputsZB) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_ZB h)

end
