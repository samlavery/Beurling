module

public import RequestProject.Beurling.Queue6.TopW
public import RequestProject.Beurling.Queue6.ClusterX

/-!
# Theorem 2.1 / Corollary 2.2 with §6 formalized up to the inputs of §5

With the Cover Bound proved (`coverOn_goodV`, from `RankFull.Config.hcov_window`), Proposition
6.11 holds at every height with no input (`e1X`). `QueueInputsX θ X₀` asks only for

* the two variance inputs of the proof of Lemma 5.22 (`E3CompBound`, `E3S2Bound`);
* Corollary 5.40 in the form of Theorem 6.6 (`R1`, `comp2`), for the good events of the family
  `e3Family` of Lemma 5.22.

* `Theorem21InputsX`, `theorem21InputsS_of_X`, `corollary_2_2_of_X`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink RankFull RankFull.Config

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs of §6**: the variance inputs of Lemma 5.22 and Corollary 5.40. -/
structure QueueInputsX where
  compE3 : E3CompBound θ X₀
  s2E3 : E3S2Bound θ X₀
  R1 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) →
    ∀ n, 0.399 * ((b : ℝ) - max (a : ℝ) X₀) / Real.log b - 2 ≤
      (ellIo θ X₀ a b ω : ℝ) -
        ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
  comp2 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
    ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → ∀ n,
      ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ 1

variable {θ X₀}

/-- **`QueueInputsX` gives `QueueCore`** (`sec5 = e3Family`; `land`, `budget5`, `tbound`
proved). -/
noncomputable def queueCore_of_X (hc : Cond θ X₀) (hev : Even X₀) (Q : QueueInputsX θ X₀) :
    QueueCore θ X₀ where
  land := fun _ _ _ hJ => land_compensator hc hJ
  sec5 := e3Family θ X₀
  budget5 := e3_budget hc Q.compE3 Q.s2E3
  R1 := Q.R1
  comp2 := Q.comp2
  tbound := fun n => tbound_G0 (e3Family θ X₀) hc hev n

/-- **Theorem 2.1, hypothesis with §6 formalized up to the inputs of §5.** -/
def Theorem21InputsX : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsX θ X₀)

/-- **`Theorem21InputsX` implies `Theorem21InputsS`**, given (84). -/
theorem theorem21InputsS_of_X (hHB : ShortIntervalPNT) (h : Theorem21InputsX) :
    Theorem21InputsS := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Q⟩ := hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hHB0 : ShortIntervalPNTFrom X₀ := hx₁.mono ((le_max_right _ _).trans h2)
  have hc : Cond θ X₀ := ⟨hθ, hlog, hHB0⟩
  refine ⟨ιF (e3Family θ X₀), inferInstance, EF θ X₀ (e3Family θ X₀), tF X₀ (e3Family θ X₀),
    ⟨sF (e3Family θ X₀), tableBudget_core hθ hlog hHB0 tiesNull hev h1
      (queueCore_of_X hc hev Q) (e1X hc hev (e3Family θ X₀))⟩, fun ω hω hU => ?_⟩
  exact goodAll_facts (e3Family θ X₀) hθ hlog hev hHB0 hω hU

/-- Theorem 2.1 from `Theorem21InputsX` and (84). -/
theorem theorem21_of_X (hHB : ShortIntervalPNT) (h : Theorem21InputsX) : Theorem21 :=
  theorem21_of_S hHB tiesNull (theorem21InputsS_of_X hHB h)

/-- **Corollary 2.2** from `Theorem21InputsX` and (84). -/
theorem corollary_2_2_of_X (hHB : ShortIntervalPNT) (h : Theorem21InputsX) : ¬ QuestionQ :=
  corollary_2_2_of_S hHB tiesNull (theorem21InputsS_of_X hHB h)

end Queue6

end
