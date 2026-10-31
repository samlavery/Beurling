module

public import RequestProject.Beurling.Model.TBoundGood
public import RequestProject.Beurling.Model.Cluster0
public import RequestProject.Beurling.Queue6.Top

/-!
# Theorem 2.1 / Corollary 2.2 with the landing, cluster-at-`X₀/2`, target-bound and `SlotHyp`
inputs of §6 proved

`QueueInputsU θ X₀` is `Queue6.QueueInputs θ X₀` with the fields

* `land` (Lemma 6.1 / (F1)–(F2): `land_compensator`),
* `tbound` (Lemma 3.4 on the good event, from Lemma 6.26 on `Good(< t)`: `tbound_G0`),
* `slotHyp` (`slotHyp_capH`),
* `cluster0` (Proposition 6.11 at `z = X₀/2`: `cluster0_of`)

**discharged**, and `S3d`, `multi` extended to the height `n = 0` (used by `cluster0`). The
remaining fields are the §5 inputs (`sec5`, `budget5`, `R1`, `comp2`) and the Appendix A inputs
(`S3d` = Lemma A.6 (S3)(d), `multi` = `MultiRunSkeletonBound`, `cover` = `CoverSkeletonBound`).

`S3d` remains in the form `S3dHyp` (on `goodLt` alone) consumed by `Queue6.eclW_fail` /
`tableBudget_EF`; the proved route of round 5 (`skeletonBound_construction_S3`) has a different
form (see the report).
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink RankFull RankFull.Config

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs of §6.3–§6.4**: §5 and Appendix A. -/
structure QueueInputsU where
  sec5 : Sec5Family
  budget5 : ∀ m, ∑' i : {i // sec5.scale i = m},
    jitterMeasure ((sec5.E i)ᶜ ∩ QC (okQ θ X₀) (tq θ X₀) (sec5.time i) ∩
      goodBefore (Sum.elim (E1ev θ X₀) sec5.E) (Sum.elim (tE1 X₀) sec5.time) (sec5.time i)) ≤
    ENNReal.ofReal (1.2 / uS X₀ m ^ 2)
  R1 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ sec5 (tE2 b) → ∀ n,
    0.399 * ((b : ℝ) - max (a : ℝ) X₀) / Real.log b - 2 ≤
      (ellIo θ X₀ a b ω : ℝ) -
        ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
  comp2 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ sec5 (tE2 b) → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ 1
  S3d : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ),
    S3dHyp hc hev (NpZ (zH X₀ n)) (DmaxZ (zH X₀ n)) (smaxZ (zH X₀ n)) (AtopZ X₀ (zH X₀ n))
  multi : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), ∀ k ∈ gridW X₀ n,
    MultiRunSkeletonBound jitterMeasure
      (G0 θ X₀ sec5 (tE1 X₀ n) ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) (r0At (zH X₀ n))
      (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n)) (EuZ X₀ (zH X₀ n))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
        (gwin (zH X₀ n) k)) E l)
  cover : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n →
    ∀ j, ∀ k ∈ gridW X₀ n, ∀ r < r0At (zH X₀ n), ∀ C ∈ CSet r j, ∀ lab ex s4,
      ExOK C ex → ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound jitterMeasure
          (G0 θ X₀ sec5 (tE1 X₀ n) ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) r
          (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n))
          (EuZ X₀ (zH X₀ n)) (zH X₀ n) (fun i => tauSlot (capH X₀) X₀ i) (exExcess ex)
          (r - C.card) l (fun ω => cfgSkelCount (DpZ X₀ (zH X₀ n)) (r0At (zH X₀ n)) 0 0
            (tailOf (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k))
            (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k)) r C lab ex s4)

variable {θ X₀}

/-- **`QueueInputsU` gives `QueueInputs`**: `land`, `tbound`, `slotHyp`, `cluster0` are proved. -/
noncomputable def queueInputs_of_U (hc : Cond θ X₀) (hev : Even X₀) (Q : QueueInputsU θ X₀) :
    QueueInputs θ X₀ where
  land := fun m i j hJ => land_compensator hc hJ
  sec5 := Q.sec5
  budget5 := Q.budget5
  R1 := Q.R1
  comp2 := Q.comp2
  tbound := fun n => tbound_G0 Q.sec5 hc hev n
  slotHyp := slotHyp_capH (Nat.cast_nonneg _) hc.hX
  cluster0 := cluster0_of hc hev Q.sec5 (Q.S3d hc hev 0) (Q.multi hc hev 0)
  S3d := fun hc' hev' n _ => Q.S3d hc' hev' n
  multi := fun hc' hev' n _ => Q.multi hc' hev' n
  cover := Q.cover

/-- **Theorem 2.1, hypothesis with §6 formalized up to §5 and Appendix A.** -/
def Theorem21InputsU : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsU θ X₀)

/-- `Theorem21InputsU` implies `Theorem21InputsT`, given (84). -/
theorem theorem21InputsT_of_U (hHB : ShortIntervalPNT) (h : Theorem21InputsU) :
    Theorem21InputsT := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Q⟩ := hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono ((le_max_right _ _).trans h2)⟩
  exact ⟨queueInputs_of_U hc hev Q⟩

/-- **Corollary 2.2** from `Theorem21InputsU` and (84). -/
theorem corollary_2_2_of_U (hHB : ShortIntervalPNT) (h : Theorem21InputsU) : ¬ QuestionQ :=
  corollary_2_2_of_T hHB (theorem21InputsT_of_U hHB h)

end Queue6
