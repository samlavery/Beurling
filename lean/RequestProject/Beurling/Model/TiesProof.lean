module

public import RequestProject.Beurling.Model.MeasIter
public import RequestProject.Beurling.Model.Ties

/-!
# `TiesNull` is a theorem

The paper's claim (§3.4) that the event `𝒩₌` of ties is null, which was the named hypothesis
`TiesNull`, is proved: the construction is measurable stage by stage (`stageMeas`), adapted
(`Model/Stage.lean`), and each tie pattern has probability `0` by the box-uniform landing law of
the latest jitter given the past (`tiesEvent_null`).

Consequently Corollary 2.2 follows from `Theorem21InputsS` and (84) alone
(`corollary_2_2_of_S_HB`).
-/

@[expose] public section

open MeasureTheory Set Construction

namespace BModel

/-- **§3.4: `𝒩₌` is null.** -/
theorem tiesNull : TiesNull := by
  intro θ hθ X₀ _ h1
  have hX : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  by_cases hHB : ShortIntervalPNTFrom X₀
  · have hc : Cond θ X₀ := ⟨hθ, hX, hHB⟩
    exact tiesEvent_null hc (stageMeas hc)
  · have : tiesEvent θ X₀ = ∅ := by
      ext ω
      simp only [tiesEvent, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hs => absurd hs.hHB hHB
    rw [this, measure_empty]

/-- `Theorem21InputsS` implies `Theorem21InputsQ`, given (84). -/
theorem theorem21InputsQ_of_S_HB (hHB : ShortIntervalPNT) (h : Theorem21InputsS) :
    Theorem21InputsQ :=
  theorem21InputsQ_of_S hHB tiesNull h

/-- **Corollary 2.2** from `Theorem21InputsS` and (84). -/
theorem corollary_2_2_of_S_HB (hHB : ShortIntervalPNT) (h : Theorem21InputsS) : ¬ QuestionQ :=
  corollary_2_2_of_S hHB tiesNull h

end BModel

end
