module

public import RequestProject.Beurling.Construction.Realised

/-!
# The adaptedness of the failure events is not needed by the top-level deduction

In `Theorem21InputsJ` (and `Theorem21InputsSp`) the failure events `E i` are assumed to be
adapted (`FailureAdapted`: `E i` is `F_{t(E i)}`-measurable). The only place where this was used
in the deduction of Theorem 2.1 is the probability budget of Lemma 6.10, through the
measurability of the good event `G = ⋂ E`. That measurability is not needed: for a probability
measure, `1 = μ(univ) ≤ μ(G) + μ(Gᶜ)` holds for every set by subadditivity.

* `ofReal_one_sub_le_of_compl`: `μ(Gᶜ) ≤ c ⟹ μ(G) ≥ 1 - c` for **any** set `G`.
* `goodAll_prob_ge_firstFailure'`, `goodAll_prob_ge_table'`: Lemma 6.10 (first failure and the
  per-scale bounds of Table 1) **without** adaptedness.
* `Theorem21InputsK`: `Theorem21InputsJ` without the condition `FailureAdapted`;
  `theorem21_of_K`, `corollary_2_2_of_K`.
* `theorem21InputsK_of_J`: `Theorem21InputsJ ⟹ Theorem21InputsK` (so `K` is a weaker hypothesis).

In the paper the adaptedness is used to *prove* the per-event bounds of Table 1 (conditioning on
`F_{t(E)}`); those bounds remain a hypothesis (`TableBudget`), so adaptedness would only be needed
again in a proof of them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex Metric Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize CaplLink
  QueueBound LagSplit SlotModel Decomp QueueMono Bookkeeping

namespace Construction

section Budget

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- **`μ(G) ≥ 1 - μ(Gᶜ)` for an arbitrary set** (no measurability): for a probability measure,
`μ(Gᶜ) ≤ c` gives `μ(G) ≥ 1 - c`. -/
lemma ofReal_one_sub_le_of_compl {μ : Measure Ω} [IsProbabilityMeasure μ] (G : Set Ω) {c : ℝ}
    (hc : 0 ≤ c) (h : μ Gᶜ ≤ ENNReal.ofReal c) : ENNReal.ofReal (1 - c) ≤ μ G := by
  have hsub : (1 : ENNReal) ≤ μ G + μ Gᶜ := by
    calc (1 : ENNReal) = μ univ := measure_univ.symm
      _ = μ (G ∪ Gᶜ) := by rw [union_compl_self]
      _ ≤ μ G + μ Gᶜ := measure_union_le _ _
  calc ENNReal.ofReal (1 - c) = ENNReal.ofReal 1 - ENNReal.ofReal c := ENNReal.ofReal_sub _ hc
    _ = 1 - ENNReal.ofReal c := by rw [ENNReal.ofReal_one]
    _ ≤ 1 - μ Gᶜ := tsub_le_tsub_left h _
    _ ≤ μ G := tsub_le_iff_right.mpr hsub

/-- **Lemma 6.10 by first failure, without adaptedness**: if
`∑_E P(Eᶜ ∩ Good(< t(E))) ≤ c`, then `P(G) ≥ 1 - c`. -/
theorem goodAll_prob_ge_firstFailure' [Countable ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ι → Set Ω} {time : ι → ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hsum : ∑' i, μ ((E i)ᶜ ∩ goodBefore E time (time i)) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (1 - c) ≤ μ (goodAll E) :=
  ofReal_one_sub_le_of_compl _ hc ((measure_mono (compl_goodAll_subset_firstFailure E time)).trans
    ((measure_iUnion_le _).trans hsum))

/-- **Lemma 6.10 from the per-scale bounds of Table 1, without adaptedness**:
`P(G) ≥ 1 - 1.5/log X₀`. -/
theorem goodAll_prob_ge_table' [Countable ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ι → Set Ω} {time : ι → ℕ} {X₀ : ℝ} (hX0 : 0 < X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    {scale : ι → ℕ} (htab : TableBudget μ X₀ E time scale) :
    ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ (goodAll E) := by
  have hΛ0 : 0 < Real.log X₀ := by linarith
  refine goodAll_prob_ge_firstFailure' (time := time) (by positivity) ?_
  exact (tsum_le_of_scale (f := fun i => μ ((E i)ᶜ ∩ goodBefore E time (time i))) scale _
    htab).trans (budget_sum_le hX0 hX)

end Budget

/-- **Theorem 2.1, hypothesis on the concrete construction, without adaptedness of the failure
events.** `Theorem21InputsJ` with the condition `FailureAdapted jitterFiltration E time` removed.
The failure events `E`, their times and scales are only required to satisfy the per-scale bounds
of Table 1 (`TableBudget`). -/
def Theorem21InputsK : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        {k | placedAt (M ω) k}.Infinite ∧
        ∃ a : ℕ → ℝ,
          PartIRestJ θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (thetaB θ) n) a (M ω) ∧
          Theorem410RestSp θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (thetaB θ) n) a ∧
          SparsityInputs X₀ (realisedSystem (M ω) (capH X₀) ω)

/-- `Theorem21InputsK` is weaker than `Theorem21InputsJ`. -/
theorem theorem21InputsK_of_J (h : Theorem21InputsJ) : Theorem21InputsK := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, -, htab, hP⟩ := hX X₀ hev h1 h2
  exact ⟨M, ι, hι, E, time, htab, hP⟩

/-- **`Theorem21InputsK` gives `Theorem21InputsFixP`**: as `theorem21InputsSp_of_J` followed by
`theorem21InputsFixP_of_sp`, with the probability budget from `goodAll_prob_ge_table'` (no
adaptedness). -/
theorem theorem21InputsFixP_of_K (h : Theorem21InputsK) : Theorem21InputsFixP := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, ⟨scale, htab⟩, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (Real.exp_pos _) h1
  refine ⟨fun ω => realisedSystem (M ω) (capH X₀) ω, ι, E,
    goodAll_prob_ge_table' hX0 hlog htab, fun ω hG hω => ?_⟩
  obtain ⟨hinf, a, hI, hC, hS⟩ := hP ω hG hω
  obtain ⟨hT, hq, κp, hκp, hland, hinit⟩ := hI
  obtain ⟨hpieces, ha⟩ := hC
  obtain ⟨X0m, η1, η2, ε1, hX0m, hX0mX, hHBS, hcl⟩ := hS
  have hTlow : ∀ x : ℝ, x < X₀ → (M ω).T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hok := realisedOK_of (M ω) hω hlog hTlow hinf
  let R : GreedyRun X₀ := ⟨M ω, capH X₀, ω, hTlow⟩
  have C' : AbsorbedCoupling (realisedSystem (M ω) (capH X₀) ω) R.M R.H R.U
      (realisedA (M ω) (capH X₀) ω) (realisedLatest (M ω) (capH X₀) ω) := realisedCoupling hok
  have h626 := lemma626_construction C' hlog hθ.1 (by linarith [hθ.2]) rfl hω hHBS hX0m hX0mX hcl
  have hrank := rankinA_construction C' hlog rfl hω hHBS hX0m
  exact ⟨realisedA (M ω) (capH X₀) ω, fun n => solveU (thetaB θ) n, a, M ω,
    realisedLatest (M ω) (capH X₀) ω,
    ⟨realisedU_spec hok hω hlog hTlow (by linarith [hθ.1]) (by linarith [hθ.2]), C'.locFin,
      h626,
      hT, hq, κp, hκp, hland, hinit⟩, ⟨C'.rule, hpieces, ha, hrank⟩⟩

/-- Theorem 2.1 from `Theorem21InputsK`. -/
theorem theorem21_of_K (h : Theorem21InputsK) : Theorem21 :=
  theorem21_of_dec (theorem21InputsDec_of_fixP (theorem21InputsFixP_of_K h))

/-- **Corollary 2.2** from `Theorem21InputsK` (no adaptedness of the failure events). -/
theorem corollary_2_2_of_K (h : Theorem21InputsK) : ¬ QuestionQ :=
  corollary_2_2_of_dec (theorem21InputsDec_of_fixP (theorem21InputsFixP_of_K h))

end Construction

end
