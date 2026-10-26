module

public import RequestProject.Beurling.Construction.HBSDerive
public import RequestProject.Beurling.Construction.Unadapted

/-!
# The top-level hypothesis without (HBS)

`Theorem21InputsL` is `Theorem21InputsK` with `SparsityInputs` (which bundled (HBS) for the realised
system and the cluster event) replaced by the **cluster event alone**: (HBS) is derived from the
slot data and the cluster event by `sparsityInputs_of_cluster`.
-/

@[expose] public section

open MeasureTheory Set Real Oscillation Absorbed Target CaplLink QueueMono InitialRange
  AbsorbEmpty SlotModel

namespace Construction

/-- **Theorem 2.1, hypothesis on the concrete construction, without adaptedness and without
(HBS).** `Theorem21InputsK` with `SparsityInputs` replaced by the cluster event
`ClusterUpTo P X₀ (4v/(log v)^{11}) (capM1 X₀ v)` for all `v ≥ X₀`. -/
def Theorem21InputsL : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        {k | placedAt (M ω) k}.Infinite ∧
        ∃ a : ℕ → ℝ,
          PartIRestJ θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (θ / 2) n) a (M ω) ∧
          Theorem410RestSp θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (θ / 2) n) a ∧
          ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
            (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsL` implies `Theorem21InputsK`: (HBS) follows from the rest. -/
theorem theorem21InputsK_of_L (h : Theorem21InputsL) : Theorem21InputsK := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hinf, a, hI, hC, hcl⟩ := hP ω hG hω
  exact ⟨hinf, a, hI, hC, sparsityInputs_of_cluster hθ hlog (M ω) ω hω hinf a hI hcl⟩

/-- `Theorem21InputsK` implies `Theorem21InputsL` (the cluster event is part of
`SparsityInputs`), so the two hypotheses are equivalent. -/
theorem theorem21InputsL_of_K (h : Theorem21InputsK) : Theorem21InputsL := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hinf, a, hI, hC, hS⟩ := hP ω hG hω
  obtain ⟨X0m, η1, η2, ε1, -, -, -, hcl⟩ := hS
  exact ⟨hinf, a, hI, hC, hcl⟩

/-- Theorem 2.1 from `Theorem21InputsL`. -/
theorem theorem21_of_L (h : Theorem21InputsL) : Theorem21 :=
  theorem21_of_K (theorem21InputsK_of_L h)

/-- **Corollary 2.2** from `Theorem21InputsL` (no adaptedness, no (HBS) assumed). -/
theorem corollary_2_2_of_L (h : Theorem21InputsL) : ¬ QuestionQ :=
  corollary_2_2_of_K (theorem21InputsK_of_L h)

end Construction

end
