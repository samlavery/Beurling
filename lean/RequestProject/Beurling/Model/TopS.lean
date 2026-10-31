module

public import RequestProject.Beurling.Model.Top
public import RequestProject.Beurling.Zeros48.Inputs

/-!
# Theorem 2.1 with the slot model constructed and Lemma 4.8(ii) derived

`Theorem21InputsS` is `Theorem21InputsQ` without the conjunct `Theorem410RestM` (the pieces of
Lemma 4.8(ii)), which `Zeros48.theorem410RestM_of_inputs` derives from the arrival link, the slot
facts and the Part I data of the constructed model. The remaining conjuncts are the per-window
inputs of Theorem 6.6(ii) (`QueueWindowData`), the cluster bound (`ClusterUpTo`) and the failure
budget (`TableBudget`).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono MeasureTheory

namespace BModel

/-- **Theorem 2.1, hypothesis with the slot model constructed and Lemma 4.8(ii) derived.** -/
def Theorem21InputsS : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ) (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        (constructedModel θ X₀ ω).QueueWindowData ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- **`Theorem21InputsS` implies `Theorem21InputsQ`**, given (84) and the nullity of `𝒩₌`: the
null event is added to the failure events, and off it `Theorem410RestM` is
`Zeros48.theorem410RestM_of_inputs` for the constructed model. -/
theorem theorem21InputsQ_of_S (hHB : ShortIntervalPNT) (hnull : TiesNull)
    (h : Theorem21InputsS) : Theorem21InputsQ := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨ι, hι, E, time, ⟨scale, htab⟩, hP⟩ :=
    hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hHB0 : ShortIntervalPNTFrom X₀ := hx₁.mono ((le_max_right _ _).trans h2)
  set N := tiesEvent θ X₀
  refine ⟨ι ⊕ Unit, inferInstance, Sum.elim E fun _ => Nᶜ, Sum.elim time fun _ => 0,
    ⟨_, tableBudget_add_null htab (hnull θ hθ X₀ hev h1)⟩, fun ω hω hU => ?_⟩
  have hG : ω ∈ goodAll E := by
    simp only [goodAll, mem_iInter] at hω ⊢
    exact fun i => hω (Sum.inl i)
  have hNω : ω ∉ N := by
    simp only [goodAll, mem_iInter] at hω
    simpa using hω (Sum.inr ())
  have hstd : Std θ X₀ ω := ⟨hθ, hlog, hU, hHB0⟩
  have ht : TieFree (constructedModel θ X₀ ω) ω := by
    by_contra hc; exact hNω ⟨hstd, hc⟩
  obtain ⟨hq, hcl⟩ := hP ω hG hU
  rw [constructedModel_eq hstd] at ht hq hcl ⊢
  refine ⟨hq, ?_, hcl⟩
  exact Zeros48.theorem410RestM_of_inputs hθ hev h1 hU (limModel_linked hstd)
    (limModel_slotFacts hstd hev ht) ⟨limModel_T_formula hstd (noCoincidence_of_tieFree ht), hq⟩

/-- Theorem 2.1 from `Theorem21InputsS`, (84) and the nullity of `𝒩₌`. -/
theorem theorem21_of_S (hHB : ShortIntervalPNT) (hnull : TiesNull) (h : Theorem21InputsS) :
    Theorem21 :=
  theorem21_of_Q hHB hnull (theorem21InputsQ_of_S hHB hnull h)

/-- **Corollary 2.2** from `Theorem21InputsS`, (84) and the nullity of `𝒩₌`. -/
theorem corollary_2_2_of_S (hHB : ShortIntervalPNT) (hnull : TiesNull)
    (h : Theorem21InputsS) : ¬ QuestionQ :=
  corollary_2_2_of_Q hHB hnull (theorem21InputsQ_of_S hHB hnull h)

end BModel

end
