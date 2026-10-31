module

public import RequestProject.Beurling.Zeros
public import RequestProject.Beurling.Oscillation
public import RequestProject.Beurling.Basic

/-!
# Theorem 2.1(i) from the target error (8) and the lag bound (13)

The paper derives Theorem 2.1(i) from three facts: the target error (8)
`|T(x) - x - R(x)| ≤ C x^θ + 2 x^{θ/2}`, the oscillation bound `|R(x)| ≤ 2 x^θ log* x`
(Lemma 3.4) and the lag bound (13) `|N(x) - T(x)| ≤ x^η`. Here the oscillation `R` is the
concrete sum (1), and its bound is *proved* (`Oscillation.abs_osc_le`); the boundedness of `N_P`
on `[1, X₀)` is also proved (`N_P` is monotone and finite). So only (8) and (13) remain as inputs.

* `BeurlingSystem.N_mono` : `N_P` is non-decreasing;
* `part_i_of_target_error` : Theorem 2.1(i) from (8) and (13) with the concrete `R`;
* `PartIInputs`, `TheoremAInputs'`, `Theorem21Inputs'` : the refined hypothesis in which
  part (i) is replaced by (8) and (13) for the concrete oscillation;
* `theorem21_of_inputs'`, `corollary_2_2_of_inputs'` : the refined hypothesis implies
  Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set BeurlingSystem Oscillation

namespace BeurlingSystem

lemma N_mono (P : BeurlingSystem) : Monotone P.N := by
  intro x y hxy
  unfold N
  exact_mod_cast Set.ncard_le_ncard (fun e (he : P.val e ≤ x) => (he.trans hxy : P.val e ≤ y))
    (P.finite_val_le y)

lemma N_nonneg (P : BeurlingSystem) (x : ℝ) : 0 ≤ P.N x := Nat.cast_nonneg _

end BeurlingSystem

/-- **Theorem 2.1(i)** from the target error (8) and the lag bound (13), with the concrete
oscillation `R = osc θ α γ x⁺` of (1) (`|α_k| ≤ 2`, `x⁺_0 ≥ 1`, `x⁺_{k+1} ≥ exp x⁺_k`).
Here `X₀ > 1` with `X₀^{θ/2} ≥ 2` (true for the paper's `X₀ ≥ e^{10^8}`). -/
theorem part_i_of_target_error {θ C₀ X₀ : ℝ} (P : BeurlingSystem) (T : ℝ → ℝ)
    {α γ xp : ℕ → ℝ} (hθ : 0 < θ) (hX₀ : 1 < X₀) (hX₀θ : 2 ≤ X₀ ^ (θ / 2))
    (hsp : Spacing xp) (hα : ∀ k, |α k| ≤ 2)
    (hE : ∀ x ≥ X₀, |T x - x - osc θ α γ xp x| ≤ C₀ * x ^ θ + 2 * x ^ (θ / 2))
    (hD : ∀ x ≥ X₀, |P.N x - T x| ≤ x ^ lagExponent θ) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ),
      |P.N x - x| ≤ C * x ^ θ + 3 * x ^ θ * (logStar x : ℝ) + x ^ lagExponent θ := by
  refine theorem21_part_i_of_bounds P.N T (osc θ α γ xp) hθ hX₀ hX₀θ hE
    (fun x hx => abs_osc_le hsp hα (by linarith)) hD ⟨P.N X₀, fun x _ hx => ?_⟩
  rw [abs_of_nonneg (P.N_nonneg x)]
  exact P.N_mono hx.le

/-- The inputs for Theorem 2.1(i) for one realised system `P`: a target `T` and an oscillation
`R = osc θ α γ x⁺` (with `|α_k| ≤ 2` and the spacing of the switch-on points) such that the target
error (8) and the lag bound (13) hold for `x ≥ X₀`. -/
def PartIInputs (θ X₀ : ℝ) (P : BeurlingSystem) : Prop :=
  ∃ (T : ℝ → ℝ) (α γ xp : ℕ → ℝ) (C₀ : ℝ), Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧
    (∀ x ≥ X₀, |T x - x - osc θ α γ xp x| ≤ C₀ * x ^ θ + 2 * x ^ (θ / 2)) ∧
    (∀ x ≥ X₀, |P.N x - T x| ≤ x ^ lagExponent θ)

/-- Refined inputs for Theorem 2.1 for one system: the part (i) inputs (8), (13) and the inputs of
Theorem 4.10 for the canonical continuation. -/
def TheoremAInputs' (θ X₀ : ℝ) (P : BeurlingSystem) : Prop :=
  PartIInputs θ X₀ P ∧ ∃ a, θ < a ∧ a < 1 ∧ Theorem410Inputs θ (P.zetaCont 1) a

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21Inputs`, but with part (i) replaced by the
target error (8) and the lag bound (13) (for the concrete oscillation `R` of (1)). -/
def Theorem21Inputs' : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputs' θ X₀ (P ω)

/-- For `X₀ ≥ e^{10^8}` and `θ ≥ 1/4`, `X₀^{θ/2} ≥ 2`. -/
lemma two_le_rpow_of_large {θ X₀ : ℝ} (hθ : 1 / 4 ≤ θ) (hX : Real.exp (10 ^ 8) ≤ X₀) :
    2 ≤ X₀ ^ (θ / 2) := by
  have hX1 : 1 ≤ X₀ := le_trans (Real.one_le_exp (by norm_num)) hX
  calc (2 : ℝ) ≤ Real.exp (10 ^ 8 * (1 / 8)) := by
        have := Real.add_one_le_exp (10 ^ 8 * (1 / 8) : ℝ); norm_num at this ⊢; linarith
    _ = Real.exp (10 ^ 8) ^ (1 / 8 : ℝ) := by rw [← Real.exp_mul]
    _ ≤ X₀ ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (Real.exp_pos _).le hX (by norm_num)
    _ ≤ X₀ ^ (θ / 2) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)

theorem theorem21Inputs_of_inputs' (h : Theorem21Inputs') : Theorem21Inputs := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  refine ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ?_⟩
  obtain ⟨⟨T, α, γ, xp, C₀, hsp, hα, hE, hD⟩, h410⟩ := hP ω hω
  have hX1 : (1 : ℝ) < X₀ := lt_of_lt_of_le (by rw [Real.one_lt_exp_iff]; norm_num) h1
  exact ⟨part_i_of_target_error (P ω) T (by linarith [hθ.1]) hX1
    (two_le_rpow_of_large hθ.1 h1) hsp hα hE hD, h410⟩

/-- The refined hypothesis implies Theorem 2.1. -/
theorem theorem21_of_inputs' (h : Theorem21Inputs') : Theorem21 :=
  theorem21_of_inputs (theorem21Inputs_of_inputs' h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21Inputs'`. -/
theorem corollary_2_2_of_inputs' (h : Theorem21Inputs') : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_inputs' h)

end
