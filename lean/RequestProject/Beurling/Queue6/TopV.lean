module

public import RequestProject.Beurling.Queue6.ClusterV
public import RequestProject.Beurling.Model.TopU

/-!
# Theorem 2.1 / Corollary 2.2 with §6 formalized up to §5 and the Cover Bound

`QueueInputsV θ X₀` asks only for

* the §5 inputs: the family `sec5` (Lemma 5.22 events), its budget `budget5` (Lemma 5.22), and
  Corollary 5.40 in the form of Theorem 6.6 (`R1`, `comp2`);
* the Cover Bound `cover` (Lemmas 6.17–6.19, `CoverSkeletonBound`) at the heights `z_n ≥ X₀`,
  with `A = A_top(z_n) = 1.8 log(2z_n + 2) exp(2.21/Λ + 10⁻⁶)` (`CoverV`).

Everything else of §6 is proved: the landing compensator (`land_compensator`), the target bound
(`tbound_G0`), `SlotHyp` (`slotHyp_capH`), and Proposition 6.11 at every height (`e1V`), with
Lemma A.6 (S3)(d) proved on `Good(< t(E1(z)))` for the position-cut law (`s3dV_sure`: Lemma
5.1(iv) up to `2z + 2` from `hbs_local`, the slot count (F1) above `2z + 2`) and the skeleton
bound for all run structures (`skeletonBound_all`, so `MultiRunSkeletonBound` is not an input).

* `Theorem21InputsV`, `theorem21InputsS_of_V`, `corollary_2_2_of_V`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink RankFull RankFull.Config

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs of §6**: §5 and the Cover Bound. -/
structure QueueInputsV where
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
  cover : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n →
    CoverV hc hev (G0 θ X₀ sec5 (tE1 X₀ n)) n

variable {θ X₀}

/-- **`QueueInputsV` gives `QueueCore`**: `land` and `tbound` are proved. -/
noncomputable def queueCore_of_V (hc : Cond θ X₀) (hev : Even X₀) (Q : QueueInputsV θ X₀) :
    QueueCore θ X₀ where
  land := fun _ _ _ hJ => land_compensator hc hJ
  sec5 := Q.sec5
  budget5 := Q.budget5
  R1 := Q.R1
  comp2 := Q.comp2
  tbound := fun n => tbound_G0 Q.sec5 hc hev n

/-- **Theorem 2.1, hypothesis with §6 formalized up to §5 and the Cover Bound.** -/
def Theorem21InputsV : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsV θ X₀)

/-- **`Theorem21InputsV` implies `Theorem21InputsS`**, given (84). -/
theorem theorem21InputsS_of_V (hHB : ShortIntervalPNT) (h : Theorem21InputsV) :
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
  have hE1 := e1V hc hev Q.sec5 (Q.cover hc hev)
  refine ⟨ιF Q.sec5, inferInstance, EF θ X₀ Q.sec5, tF X₀ Q.sec5,
    ⟨sF Q.sec5, tableBudget_core hθ hlog hHB0 tiesNull hev h1 (queueCore_of_V hc hev Q) hE1⟩,
    fun ω hω hU => ?_⟩
  exact goodAll_facts Q.sec5 hθ hlog hev hHB0 hω hU

/-- Theorem 2.1 from `Theorem21InputsV` and (84). -/
theorem theorem21_of_V (hHB : ShortIntervalPNT) (h : Theorem21InputsV) : Theorem21 :=
  theorem21_of_S hHB tiesNull (theorem21InputsS_of_V hHB h)

/-- **Corollary 2.2** from `Theorem21InputsV` and (84). -/
theorem corollary_2_2_of_V (hHB : ShortIntervalPNT) (h : Theorem21InputsV) : ¬ QuestionQ :=
  corollary_2_2_of_S hHB tiesNull (theorem21InputsS_of_V hHB h)

end Queue6

end
