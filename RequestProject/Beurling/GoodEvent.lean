module

public import Mathlib

/-!
# Assembling the good event by a union bound

The good event `G` of the random construction is an intersection of finitely many events `E_i`
(the landing counts of Lemma 6.1, the Freedman bounds (73), …), each failing with probability at
most `ε_i`. If `∑ ε_i ≤ c`, then `P(G) ≥ 1 - c`, which is the form
`ENNReal.ofReal (1 - 1.5 / log X₀) ≤ μ G` used in the statement of Theorem 2.1.

* `GoodEvent.measure_iInter_ge` : `ofReal (1 - c) ≤ μ (⋂ i ∈ s, E i)` for a finite family.
* `GoodEvent.measure_iInter_ge_countable` : the same for a countable family with
  `∑' ε_i ≤ c`.
-/

@[expose] public section

open MeasureTheory

namespace GoodEvent

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `ofReal (1 - c) ≤ μ A` as soon as `μ Aᶜ ≤ ofReal c`, `A` measurable. -/
lemma ofReal_one_sub_le {A : Set Ω} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c)
    (h : μ Aᶜ ≤ ENNReal.ofReal c) : ENNReal.ofReal (1 - c) ≤ μ A := by
  have hcompl : μ A = 1 - μ Aᶜ := by
    have := prob_compl_eq_one_sub (μ := μ) hA.compl
    rw [compl_compl] at this; exact this
  rw [hcompl]
  calc ENNReal.ofReal (1 - c) = ENNReal.ofReal 1 - ENNReal.ofReal c :=
        ENNReal.ofReal_sub _ hc
    _ = 1 - ENNReal.ofReal c := by rw [ENNReal.ofReal_one]
    _ ≤ 1 - μ Aᶜ := tsub_le_tsub_left h _

/-- **Union bound for the good event (finite family)**: if each `E i`, `i ∈ s`, is measurable
and fails with probability at most `ε i ≥ 0`, and `∑_{i ∈ s} ε i ≤ c`, then
`P(⋂_{i ∈ s} E i) ≥ 1 - c`. -/
theorem measure_iInter_ge (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (ε : ι → ℝ) (hε0 : ∀ i ∈ s, 0 ≤ ε i) (hε : ∀ i ∈ s, μ (E i)ᶜ ≤ ENNReal.ofReal (ε i))
    {c : ℝ} (hc : ∑ i ∈ s, ε i ≤ c) :
    ENNReal.ofReal (1 - c) ≤ μ (⋂ i ∈ s, E i) := by
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg hε0) hc
  apply ofReal_one_sub_le (Finset.measurableSet_biInter s hE) hc0
  rw [Set.compl_iInter₂]
  calc μ (⋃ i ∈ s, (E i)ᶜ) ≤ ∑ i ∈ s, μ (E i)ᶜ := measure_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (ε i) := Finset.sum_le_sum hε
    _ = ENNReal.ofReal (∑ i ∈ s, ε i) := (ENNReal.ofReal_sum_of_nonneg hε0).symm
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hc

/-- **Union bound for the good event (countable family)**: if each `E i` is measurable and fails
with probability at most `ε i ≥ 0`, `ε` is summable and `∑' ε i ≤ c`, then
`P(⋂ i, E i) ≥ 1 - c`. -/
theorem measure_iInter_ge_countable [Countable ι] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (ε : ι → ℝ) (hε0 : ∀ i, 0 ≤ ε i) (hsum : Summable ε)
    (hε : ∀ i, μ (E i)ᶜ ≤ ENNReal.ofReal (ε i)) {c : ℝ} (hc : ∑' i, ε i ≤ c) :
    ENNReal.ofReal (1 - c) ≤ μ (⋂ i, E i) := by
  have hc0 : 0 ≤ c := le_trans (tsum_nonneg hε0) hc
  apply ofReal_one_sub_le (MeasurableSet.iInter hE) hc0
  rw [Set.compl_iInter]
  calc μ (⋃ i, (E i)ᶜ) ≤ ∑' i, μ (E i)ᶜ := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (ε i) := ENNReal.tsum_le_tsum hε
    _ = ENNReal.ofReal (∑' i, ε i) := (ENNReal.ofReal_tsum_of_nonneg hε0 hsum).symm
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hc

end GoodEvent

end
