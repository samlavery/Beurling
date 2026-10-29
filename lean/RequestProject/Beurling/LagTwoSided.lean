module

public import RequestProject.Beurling.Theorem410Design

/-!
# The lag bound from the two-sided lag (12) and the queue bound of Theorem 6.6(ii)

In `PartIInputsQueue75` the lag bound `|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` (with the explicit
queue bound `B = queueB` of (75) and the jitter width `H = capH`) is a single hypothesis. In the
paper it is assembled from two separate facts:

* the two-sided lag (12) (Corollary 3.8):
  `-(H/2)(1 + κ₊/log x) - 4 ≤ N_P(x) - T(x) ≤ max Q + (H/2)(1 + κ₊/log x) + 3`
  with `0 ≤ κ₊ ≤ log x`, where `max Q` is the largest queue length up to `x`;
* the queue bound of Theorem 6.6(ii): `0 ≤ max Q ≤ B(x)`.

`PartIInputsLag` takes these two facts as separate hypotheses, and `PartIInputsLag.toQueue75`
assembles the lag bound from them (using `H ≥ 1`, from `capH_conditions`). This gives the
refined hypothesis `Theorem21InputsLag`, which implies Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound Bookkeeping

/-- The inputs of Theorem 2.1(i) as in `PartIInputsQueue75`, with the lag bound replaced by the
two-sided lag (12) (Corollary 3.8), with largest queue `Qmax x` and correction `κ₊(x)`,
`0 ≤ κ₊(x) ≤ log x`, and the queue bound `0 ≤ Qmax x ≤ B(x)` of Theorem 6.6(ii). -/
def PartIInputsLag (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (Qmax κp : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ Qmax x ∧ Qmax x ≤ queueB X₀ x) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ),
      -(capH X₀ x / 2) * (1 + κp x / Real.log x) - 4 ≤
        P.N x - target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x ∧
      P.N x - target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x ≤
        Qmax x + capH X₀ x / 2 * (1 + κp x / Real.log x) + 3)

/-- **The lag bound from (12) and Theorem 6.6(ii)**: `PartIInputsLag` gives
`PartIInputsQueue75`, i.e. `|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` for `x ≥ X₀`. -/
theorem PartIInputsLag.toQueue75 {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hX : 10 ^ 8 ≤ Real.log X₀) (h : PartIInputsLag θ X₀ P) : PartIInputsQueue75 θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, Qmax, κp, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hQ, hκp, hlag⟩ := h
  refine ⟨κ, A, u, α, γ, xp, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, fun x hx => ?_⟩
  have hX0 : (0 : ℝ) < X₀ := by
    rcases (Nat.cast_nonneg X₀ : (0 : ℝ) ≤ X₀).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hLx : 0 < Real.log x := by
    have := Real.log_le_log hX0 hx; linarith
  have hH : 1 ≤ capH X₀ x :=
    le_trans (Real.one_le_exp (by positivity)) (capH_conditions hX0.le hX hx).2.1
  exact abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH
    ((hQ x hx).1.trans (hQ x hx).2) (hQ x hx).2 (hlag x hx).1 (hlag x hx).2

/-- Refined inputs for one system: `PartIInputsLag` and `Theorem410InputsDesign`. -/
def TheoremAInputsLag (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsLag θ X₀ P ∧ Theorem410InputsDesign θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsDesign`, with the lag bound split
into the two-sided lag (12) and the queue bound of Theorem 6.6(ii). -/
def Theorem21InputsLag : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsLag θ X₀ (P ω)

theorem theorem21InputsDesign_of_lag (h : Theorem21InputsLag) : Theorem21InputsDesign := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1.toQueue75 hlog, (hP ω hω).2⟩⟩

/-- The refined hypothesis `Theorem21InputsLag` implies Theorem 2.1. -/
theorem theorem21_of_lag (h : Theorem21InputsLag) : Theorem21 :=
  theorem21_of_design (theorem21InputsDesign_of_lag h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsLag`. -/
theorem corollary_2_2_of_lag (h : Theorem21InputsLag) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_lag h)

end
