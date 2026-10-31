module

public import RequestProject.Beurling.LagTwoSided
public import RequestProject.Beurling.RankinMinorant

/-!
# The absorbed-set growth from the paper's Rankin minorant `ς_*`

In `Theorem410InputsDesign` the absorbed set is controlled by a free exponent `ς` with three
hypotheses: `ς` is monotone, `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}` for `x ≥ 1`, and the uniform growth
`42 log(2 + ℓ) + 5 ≤ ς(ℓ)` for `ℓ ≥ 0`.

Here `ς` is no longer free. Following the proof of Lemma 4.4, the exponent is the explicit Rankin
minorant `ς_*(v) = 0.9 ũ(v) log ũ(v)`, `ũ(v) = v / max(22.6 Λ, 12 (log v)² + 9 log v + 8)` with
`Λ = log X₀` (`RankinMinorant.sigmaStar`). The remaining hypotheses on `A` are those the paper
states:

* `A` is empty at low heights: `#(A ∩ [1, x]) = 0` for `log x ≤ Λ²` (the paper has `A = ∅` for
  `log log x ≤ 2 log Λ + s_H`, `s_H > 0`, which is stronger);
* the Rankin bound `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` above that height (Lemma 6.26, steps (i)
  and (v), as used in the proof of Lemma 4.4).

Monotonicity and the uniform growth are now proved (`RankinMinorant.sigmaExt_monotone`,
`RankinMinorant.sigmaExt_growth`), for `Λ ≥ 10⁸`.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  DesignedZero Target RankinMinorant GoodHeights

/-- **The inputs of Theorem 4.10 with the paper's Rankin minorant**: as `Theorem410InputsDesign`,
with `log X₀ ≥ 10⁸`, and with the free exponent `ς` and its three hypotheses replaced by: `A` is
empty below `log x = (log X₀)²`, and `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` above. -/
def Theorem410InputsRankin (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ T κ₀ η : ℝ) (xp a : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ),
    10 ^ 8 ≤ Real.log X₀ ∧ 1 / 20 ≤ θ ∧ θ ≤ 1 / 2 ∧ 0 < κ ∧ κ ≤ 1 ∧
    Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (∀ k, 1 < xp k) ∧ (∀ k, 2 * Real.log X₀ ≤ Real.log (Real.log (xp k))) ∧
    (∀ k, T + 1 / 2 ≤ heightScale θ κ₀ (xp k)) ∧
    (∀ k, Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * heightScale θ κ₀ (xp k)) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (Dlt k)) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (thetaB θ) A u ∧
    (∀ x ≥ (1 : ℝ), Real.log x ≤ Real.log X₀ ^ 2 → countA A x = 0) ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x))) ∧
    (∀ k, ∀ s ∈ closedBall (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s +
        (∑' j, oscHat θ (designAlpha X₀ κ θ κ₀ Dlt xp j) (designGamma X₀ κ θ κ₀ Dlt xp j)
          (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (thetaB θ) A u s)

/-- The inputs with the Rankin minorant give `Theorem410InputsDesign`, with
`ς = sigmaExt (log X₀)`, i.e. `ς(ℓ) = ς_*(max(ℓ, (log X₀)²))`. -/
theorem Theorem410InputsRankin.toDesign {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsRankin θ F) :
    Theorem410InputsDesign θ F := by
  obtain ⟨X₀, κ, T, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκ, hκ1, hT, hκ₀1, hκ₀2,
    hx1, hLL, hΓT, hΓ, hDd, hpieces, hsp, hη0, hη, ha, hD, hA, hempty, hbound, hdec⟩ := h
  exact ⟨X₀, κ, T, κ₀, η, xp, a, D, Dlt, A, u, sigmaExt (Real.log X₀), by linarith, hθ1, hθ2,
    hκ, hκ1, hT, hκ₀1, hκ₀2, hx1, hLL, hΓT, hΓ, hDd, hpieces, hsp, hη0, hη, ha, hD, hA,
    sigmaExt_monotone hX, le_sigmaExt (countA A) hempty hbound,
    fun ℓ hℓ => sigmaExt_growth hX hℓ, hdec⟩

/-- Refined inputs for one system: `PartIInputsLag` and `Theorem410InputsRankin`. -/
def TheoremAInputsRankin (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsLag θ X₀ P ∧ Theorem410InputsRankin θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsLag`, with the absorbed-set exponent
given by the paper's Rankin minorant `ς_*` (`Theorem410InputsRankin`). -/
def Theorem21InputsRankin : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsRankin θ X₀ (P ω)

theorem theorem21InputsLag_of_rankin (h : Theorem21InputsRankin) : Theorem21InputsLag := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toDesign⟩⟩

/-- The refined hypothesis `Theorem21InputsRankin` implies Theorem 2.1. -/
theorem theorem21_of_rankin (h : Theorem21InputsRankin) : Theorem21 :=
  theorem21_of_lag (theorem21InputsLag_of_rankin h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsRankin`. -/
theorem corollary_2_2_of_rankin (h : Theorem21InputsRankin) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_rankin h)

end
