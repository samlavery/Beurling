module

public import RequestProject.Beurling.Queue6.Table6
public import RequestProject.Beurling.Model.TopS
public import RequestProject.Beurling.Model.TiesProof

/-!
# Theorem 2.1 / Corollary 2.2 with §6.1–§6.4 and Theorem 6.6 formalized

`Theorem21InputsT` asks, for each admissible `θ` and every large even `X₀`, only for the inputs
`QueueInputs θ X₀` of §6.3–§6.4 that are results of other sections ((F1)–(F2), Lemma 3.4 on the
good event, Lemma 5.22, Corollary 5.40, the residual inputs of Appendix A (Lemma A.3 `SlotHyp`,
Lemma A.6 (S3)(d), Lemma A.5 + Theorem A.10 for several runs, the Cover Bound) and Proposition
6.11 at the height `X₀/2`; see Queue6/Family.lean). From them the event family of
Definition 6.8 is **constructed** (`EF`), and

* `TableBudget` is **proved** (`tableBudget_EF`: Table 1 per scale, with Theorem 6.6(i) via
  Freedman's inequality, Lemma 6.1 via the landing count, and Proposition 6.11 at `z ≥ X₀` via
  the window model of Appendix A, `eclW_fail`); the adaptedness of the counts is proved
  (Queue6/Adapted6.lean);
* on the good event, `QueueWindowData` (Theorem 6.6(ii), with Lemma 3.9 and Corollary 6.12
  proved for the constructed model) and `ClusterUpTo` are **proved** (`goodAll_facts`).

Hence `Theorem21InputsT ⟹ Theorem21InputsS` (`theorem21InputsS_of_T`) and Corollary 2.2
(`corollary_2_2_of_T`), given (84) (`ShortIntervalPNT`).
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink

namespace Queue6

/-- **Theorem 2.1, hypothesis with §6.1–§6.4 formalized**: the inputs of §6.3–§6.4 from other
sections, for every admissible `θ` and every even `X₀ ≥ max(e^{10⁸}, X_Hux)`. -/
def Theorem21InputsT : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputs θ X₀)

instance (D : Sec5Family) : Countable (ιF D) := by unfold ιF ι0; infer_instance

/-- **`Theorem21InputsT` implies `Theorem21InputsS`**, given (84). -/
theorem theorem21InputsS_of_T (hHB : ShortIntervalPNT) (h : Theorem21InputsT) :
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
  refine ⟨ιF Q.sec5, inferInstance, EF θ X₀ Q.sec5, tF X₀ Q.sec5,
    ⟨sF Q.sec5, tableBudget_EF hθ hlog hHB0 tiesNull hev h1 Q⟩, fun ω hω hU => ?_⟩
  exact goodAll_facts Q.sec5 hθ hlog hev hHB0 hω hU

/-- Theorem 2.1 from `Theorem21InputsT` and (84). -/
theorem theorem21_of_T (hHB : ShortIntervalPNT) (h : Theorem21InputsT) : Theorem21 :=
  theorem21_of_S hHB tiesNull (theorem21InputsS_of_T hHB h)

/-- **Corollary 2.2** from `Theorem21InputsT` and (84). -/
theorem corollary_2_2_of_T (hHB : ShortIntervalPNT) (h : Theorem21InputsT) : ¬ QuestionQ :=
  corollary_2_2_of_S hHB tiesNull (theorem21InputsS_of_T hHB h)

end Queue6

end
