module

public import RequestProject.Beurling.Queue6.TopV
public import RequestProject.Beurling.Queue6.Noise3

/-!
# Theorem 2.1 / Corollary 2.2 with the events E3, E3′ of Lemma 5.22 constructed

The §5 family of Definition 6.8 is now the family `e3Family` of the per-window Freedman events
of Lemma 5.22, and its budget (`budget5`) is proved (`e3_budget`). `QueueInputsW θ X₀` asks for

* the two variance inputs of the proof of Lemma 5.22: `Comp(W) ≤ 50 log(2u)|W|`
  (`E3CompBound`) and eq. (s2) `Comp⁽²⁾(W) ≤ s₂(u)|W|` (`E3S2Bound`);
* Corollary 5.40 in the form of Theorem 6.6 (`R1`, `comp2`) for the good events of this family;
* the Cover Bound (`cover`, `CoverV`).

* `Theorem21InputsW`, `theorem21InputsV_of_W`, `corollary_2_2_of_W`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink RankFull RankFull.Config

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs of §6**: the variance inputs of Lemma 5.22, Corollary 5.40 and the
Cover Bound. -/
structure QueueInputsW where
  compE3 : E3CompBound θ X₀
  s2E3 : E3S2Bound θ X₀
  R1 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) →
    ∀ n, 0.399 * ((b : ℝ) - max (a : ℝ) X₀) / Real.log b - 2 ≤
      (ellIo θ X₀ a b ω : ℝ) -
        ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
  comp2 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
    ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → ∀ n,
      ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ 1
  cover : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n →
    CoverV hc hev (G0 θ X₀ (e3Family θ X₀) (tE1 X₀ n)) n

variable {θ X₀}

/-- **`QueueInputsW` gives `QueueInputsV`**: `sec5 = e3Family`, `budget5` by `e3_budget`. -/
noncomputable def queueInputsV_of_W (hc : Cond θ X₀) (Q : QueueInputsW θ X₀) :
    QueueInputsV θ X₀ where
  sec5 := e3Family θ X₀
  budget5 := e3_budget hc Q.compE3 Q.s2E3
  R1 := Q.R1
  comp2 := Q.comp2
  cover := Q.cover

/-- **Theorem 2.1, hypothesis with §6 and Lemma 5.22 formalized** up to the variance inputs of
Lemma 5.22, Corollary 5.40 and the Cover Bound. -/
def Theorem21InputsW : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsW θ X₀)

/-- `Theorem21InputsW` implies `Theorem21InputsV`, given (84). -/
theorem theorem21InputsV_of_W (hHB : ShortIntervalPNT) (h : Theorem21InputsW) :
    Theorem21InputsV := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Q⟩ := hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono ((le_max_right _ _).trans h2)⟩
  exact ⟨queueInputsV_of_W hc Q⟩

/-- **Corollary 2.2** from `Theorem21InputsW` and (84). -/
theorem corollary_2_2_of_W (hHB : ShortIntervalPNT) (h : Theorem21InputsW) : ¬ QuestionQ :=
  corollary_2_2_of_V hHB (theorem21InputsV_of_W hHB h)

end Queue6

end
