module

public import RequestProject.Beurling.Theorem410Base
public import RequestProject.Beurling.Mertens

/-!
# Theorem 4.10 with the Mertens estimates proved

The Mertens estimates `Z_∞(1) ≤ 1.8 log X₀` and `∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀` are proved
in `Mertens` for `log X₀ ≥ 10⁴`. Here they are removed from the hypotheses of Lemma 4.2
(`lemma_4_2_Zinf_of_large`, `lemma_4_2_ZB_of_large`) and from the inputs of Theorem 4.10
(`Theorem410InputsMertens`), and Theorem 2.1 and Corollary 2.2 are derived from the resulting
refined hypothesis `Theorem21InputsMertens`.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor

namespace BaseFactor

/-- **Lemma 4.2, bounds on `Z_∞`**, with the Mertens estimates proved: for `log X₀ ≥ 10⁴`, on
`σ ≥ 1 - δ` with `δ log X₀ ≤ 0.01`, `|Z_∞(s)| ≤ 1.9 log X₀` and `|Z_∞'(s)| ≤ 4 log² X₀`. -/
theorem lemma_4_2_Zinf_of_large {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ * Real.log X₀ ≤ 1 / 100) {s : ℂ} (hσ : 1 - δ ≤ s.re) :
    ‖Zinf X₀ s‖ ≤ 1.9 * Real.log X₀ ∧ ‖deriv (Zinf X₀) s‖ ≤ 4 * Real.log X₀ ^ 2 :=
  lemma_4_2_Zinf (by have := Mertens.three_le_of_log (X₀ := X₀) (by linarith); omega)
    (Mertens.ZinfR_one_le hX) (Mertens.logSum_one_le hX) hδ0 hδ hσ

/-- **Lemma 4.2, bounds on `Z_B`**, with the Mertens estimates proved (`log X₀ ≥ 10⁴`). -/
theorem lemma_4_2_ZB_of_large {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀)
    {ZB : ℂ → ℂ} {T : ℝ}
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ ZB z)
    (hclose : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZB z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4)))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ * Real.log X₀ ≤ 1 / 100) {s : ℂ} (hσ1 : 1 - δ ≤ s.re)
    (hσ2 : s.re ≤ 7 / 4) (ht : T + 1 / 4 ≤ |s.im|) :
    DifferentiableAt ℂ ZB s ∧ ‖ZB s‖ ≤ 2 * Real.log X₀ ∧
      ‖deriv ZB s‖ ≤ 4.01 * Real.log X₀ ^ 2 :=
  lemma_4_2_ZB (by have := Mertens.three_le_of_log (X₀ := X₀) (by linarith); omega)
    (by linarith) (Mertens.ZinfR_one_le hX) (Mertens.logSum_one_le hX) hdiff hclose hδ0 hδ
    hσ1 hσ2 ht

end BaseFactor

namespace DesignedZero

/-- **The inputs of Theorem 4.10 with the Mertens estimates proved.** As
`Theorem410InputsBase`, but the two Mertens estimates are replaced by `log X₀ ≥ 10⁴`. -/
def Theorem410InputsMertens (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (T κ₀ η : ℝ) (α γ xp a : ℕ → ℝ) (ZB : ℂ → ℂ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    10 ^ 4 ≤ Real.log X₀ ∧
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ ZB z) ∧
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZB z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4))) ∧
    (∀ k, DesignParams θ (Real.log X₀) κ₀ (α k) (γ k) (xp k)) ∧
    (∀ k, T + 1 / 2 ≤ γ k) ∧
    (∀ k, 0.6 ≤ ‖ZB (1 + γ k * I)‖) ∧
    (∀ k, 1 ≤ α k ∧ α k ≤ 2) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k ≤ xp k) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (θ / 2) A u ∧ Monotone ς ∧
    (∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) ∧
    (∀ k, ∀ τ : ℝ, |τ - γ k| ≤ 1 →
      absorbedBound ς (designRadius (xp k)) (|τ| ^ (1 / (1 - θ / 2))) ≤ 1 / 16) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)),
      F s = ZB s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) + (Dlt k s + lateNoise D (a k) s) +
        absorbedHat (θ / 2) A u s) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)), ‖Dlt k s‖ ≤ 1 / 16)

theorem Theorem410InputsMertens.base {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsMertens θ F) :
    Theorem410InputsBase θ F := by
  obtain ⟨X₀, T, κ₀, η, α, γ, xp, a, ZB, D, Dlt, A, u, ς, hX, hdiff, hclose, hP, hγT,
    hc, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hB, hdec, hDlt⟩ := h
  have h3 := Mertens.three_le_of_log (X₀ := X₀) (by linarith)
  exact ⟨X₀, T, κ₀, η, α, γ, xp, a, ZB, D, Dlt, A, u, ς, by omega, Mertens.ZinfR_one_le hX,
    Mertens.logSum_one_le hX, hdiff, hclose, hP, hγT, hc, hα, hsp, hγx, hη0, hη, ha, hD, hA,
    hς, hN, hB, hdec, hDlt⟩

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system with the Mertens estimates proved. -/
def TheoremAInputsMertens (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsMertens θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** (Lemma 4.2's bounds, Lemma 4.4(a) and the Mertens
estimates derived). -/
def Theorem21InputsMertens : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsMertens θ X₀ (P ω)

theorem theorem21InputsBase_of_mertens (h : Theorem21InputsMertens) : Theorem21InputsBase := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.base⟩⟩

/-- The refined hypothesis (Mertens estimates proved) implies Theorem 2.1. -/
theorem theorem21_of_mertens (h : Theorem21InputsMertens) : Theorem21 :=
  theorem21_of_base (theorem21InputsBase_of_mertens h)

/-- **Corollary 2.2** from the refined hypothesis with the Mertens estimates proved. -/
theorem corollary_2_2_of_mertens (h : Theorem21InputsMertens) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_mertens h)

end
