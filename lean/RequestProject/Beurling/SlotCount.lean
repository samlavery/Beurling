module

public import RequestProject.Beurling.Theorem410Rankin

/-!
# Counting continuous-slot starts and the two-sided lag (12) from the slot structure

Section 3.4: between consecutive continuous-slot starts, `T` gains exactly one unit of continuous
mass. Hence (the proof of Corollary 3.8) an interval `I` contains at most `∫_I T'_cont + 1`
continuous-slot starts.

* `SlotCount.card_le_of_unit_gaps` : if `F` is monotone and any two points `s < t` of a finite set
  `S ⊆ [a, b]` satisfy `F t - F s ≥ 1`, then `#S ≤ F b - F a + 1`;
* `SlotCount.card_le_of_slope` : with the slope bound `F b - F a ≤ c (b - a)`, `#S ≤ c (b - a) + 1`;
* `SlotCount.two_sided_lag_of_slots` : **Corollary 3.8** from Lemma 3.6 and the slot structure:
  the landing errors `E±` are bounded by the numbers of continuous-slot starts in the windows of
  length `ℓ±` next to `x`, which gives (12) when `c ℓ± ≤ (H/2)(1 + κ₊/log x) + ε`, `ε ≤ 1/2`;
* `PartIInputsSlots` : the inputs `PartIInputsLag` with (12) replaced by this slot-level data
  (`SlotData`), and `theorem21_of_slots`, `corollary_2_2_of_slots` (combined with
  `Theorem410InputsRankin`).
-/

@[expose] public section

open Finset Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound

namespace SlotCount

/-- **At most `F b - F a + 1` unit-gap points in `[a, b]`.** If `F` is monotone and any two points
`s < t` of `S` satisfy `F t - F s ≥ 1`, and `S ⊆ [a, b]`, then `#S ≤ F b - F a + 1`. -/
theorem card_le_of_unit_gaps (F : ℝ → ℝ) (hF : Monotone F) (S : Finset ℝ) {a b : ℝ}
    (hab : a ≤ b) (hS : ∀ s ∈ S, a ≤ s ∧ s ≤ b)
    (hgap : ∀ s ∈ S, ∀ t ∈ S, s < t → 1 ≤ F t - F s) :
    (S.card : ℝ) ≤ F b - F a + 1 := by
  induction S using Finset.induction_on_max generalizing b with
  | h0 => simp only [card_empty, Nat.cast_zero]; linarith [hF hab]
  | step t S' hlt ih =>
    have htS' : t ∉ S' := fun h => lt_irrefl t (hlt t h)
    rw [card_insert_of_notMem htS']
    push_cast
    have ht := hS t (mem_insert_self t S')
    rcases S'.eq_empty_or_nonempty with h | hne
    · subst h; simp only [card_empty, Nat.cast_zero]
      linarith [hF hab]
    · set m := S'.max' hne
      have hm : m ∈ S' := max'_mem S' hne
      have ham : a ≤ m := (hS m (mem_insert_of_mem hm)).1
      have ih' := ih ham (fun s hs => ⟨(hS s (mem_insert_of_mem hs)).1, le_max' S' s hs⟩)
        (fun s hs t' ht' hst => hgap s (mem_insert_of_mem hs) t' (mem_insert_of_mem ht') hst)
      have hg := hgap m (mem_insert_of_mem hm) t (mem_insert_self t S') (hlt m hm)
      linarith [hF ht.2]

/-- **At most `c (b - a) + 1` continuous-slot starts in `[a, b]`**, under the slope bound
`F b - F a ≤ c (b - a)` for the continuous mass `F` (the bound on `T'_cont`). -/
theorem card_le_of_slope (F : ℝ → ℝ) (hF : Monotone F) (S : Finset ℝ) {a b c : ℝ}
    (hab : a ≤ b) (hS : ∀ s ∈ S, a ≤ s ∧ s ≤ b)
    (hgap : ∀ s ∈ S, ∀ t ∈ S, s < t → 1 ≤ F t - F s) (hc : F b - F a ≤ c * (b - a)) :
    (S.card : ℝ) ≤ c * (b - a) + 1 := by
  linarith [card_le_of_unit_gaps F hF S hab hS hgap]

/-- **Corollary 3.8 (two-sided lag) from Lemma 3.6 and the slot structure.** Let `x ∈ J_j`, so
`T(x) ∈ [j + ϑ, j + 1 + ϑ)`, `ϑ ∈ (0, 1/2]`. Write `N(x) = V_j - C + E₊ - E₋` with
`V_j = j + 1 + Q_j` (Lemma 3.6), `0 ≤ C ≤ A_j`, `Q_j - A_j ≥ -1`. The primes counted by `E₊`
(resp. `E₋`) were placed at distinct continuous-slot starts in `[x, x + ℓ₊]` (resp.
`[x - ℓ₋, x]`); continuous-slot starts are one unit of continuous mass `F` apart, and
`F` has slope at most `c` on these windows. If `c ℓ± ≤ W + ε` with `W = (H/2)(1 + κ₊/log x)` and
`ε ≤ 1/2`, then `-W - 4 ≤ N(x) - T(x) ≤ Q_max + W + 3`. -/
theorem two_sided_lag_of_slots {x j T N Q A C Ep Em ϑ W ε Qmax c lp lm : ℝ}
    (F : ℝ → ℝ) (hF : Monotone F) (Sp Sm : Finset ℝ)
    (hN : N = (j + 1 + Q) - C + Ep - Em) (hT1 : j + ϑ ≤ T) (hT2 : T < j + 1 + ϑ)
    (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1 / 2) (hC0 : 0 ≤ C) (hCA : C ≤ A) (hQA : -1 ≤ Q - A)
    (hQ : Q ≤ Qmax)
    (hlp : 0 ≤ lp) (hlm : 0 ≤ lm)
    (hSp : ∀ s ∈ Sp, x ≤ s ∧ s ≤ x + lp) (hSm : ∀ s ∈ Sm, x - lm ≤ s ∧ s ≤ x)
    (hgapp : ∀ s ∈ Sp, ∀ t ∈ Sp, s < t → 1 ≤ F t - F s)
    (hgapm : ∀ s ∈ Sm, ∀ t ∈ Sm, s < t → 1 ≤ F t - F s)
    (hcp : F (x + lp) - F x ≤ c * lp) (hcm : F x - F (x - lm) ≤ c * lm)
    (hEp0 : 0 ≤ Ep) (hEp : Ep ≤ Sp.card) (hEm0 : 0 ≤ Em) (hEm : Em ≤ Sm.card)
    (hWp : c * lp ≤ W + ε) (hWm : c * lm ≤ W + ε) (hε : ε ≤ 1 / 2) :
    -W - 4 ≤ N - T ∧ N - T ≤ Qmax + W + 3 := by
  have hp := card_le_of_slope F hF Sp (by linarith) hSp hgapp (c := c) (by simpa using hcp)
  have hm := card_le_of_slope F hF Sm (by linarith) hSm hgapm (c := c) (by simpa using hcm)
  simp only [add_sub_cancel_left, sub_sub_cancel] at hp hm
  exact Bookkeeping.two_sided_lag hN hT1 hT2 hϑ0 hϑ hC0 hCA hQA hEp0 (by linarith) hEm0
    (by linarith) hε hQ

end SlotCount

open SlotCount

/-- The slot-level data behind (12) at one height `x` (proof of Corollary 3.8): the slot index `j`
with `T(x) ∈ [j + ϑ, j + 1 + ϑ)`, the queue `Q_j ≤ Q_max(x)`, the arrivals `A_j`, the composites
`C = C((x, s_{j+1}))`, the landing errors `E±` with the continuous-slot starts `S±` of the slots
whose primes they count, the continuous mass `F` with slope at most `c` on the windows of
lengths `ℓ±`, and the decomposition `N(x) = (j + 1 + Q_j) - C + E₊ - E₋` (Lemma 3.6). -/
def SlotData (N T Qmax W : ℝ) (x : ℝ) : Prop :=
  ∃ (j Q A C Ep Em ϑ ε c lp lm : ℝ) (F : ℝ → ℝ) (Sp Sm : Finset ℝ),
    Monotone F ∧ N = (j + 1 + Q) - C + Ep - Em ∧ j + ϑ ≤ T ∧ T < j + 1 + ϑ ∧
    0 < ϑ ∧ ϑ ≤ 1 / 2 ∧ 0 ≤ C ∧ C ≤ A ∧ -1 ≤ Q - A ∧ Q ≤ Qmax ∧ 0 ≤ lp ∧ 0 ≤ lm ∧
    (∀ s ∈ Sp, x ≤ s ∧ s ≤ x + lp) ∧ (∀ s ∈ Sm, x - lm ≤ s ∧ s ≤ x) ∧
    (∀ s ∈ Sp, ∀ t ∈ Sp, s < t → 1 ≤ F t - F s) ∧
    (∀ s ∈ Sm, ∀ t ∈ Sm, s < t → 1 ≤ F t - F s) ∧
    F (x + lp) - F x ≤ c * lp ∧ F x - F (x - lm) ≤ c * lm ∧
    0 ≤ Ep ∧ Ep ≤ Sp.card ∧ 0 ≤ Em ∧ Em ≤ Sm.card ∧
    c * lp ≤ W + ε ∧ c * lm ≤ W + ε ∧ ε ≤ 1 / 2

theorem SlotData.two_sided {N T Qmax W x : ℝ} (h : SlotData N T Qmax W x) :
    -W - 4 ≤ N - T ∧ N - T ≤ Qmax + W + 3 := by
  obtain ⟨j, Q, A, C, Ep, Em, ϑ, ε, c, lp, lm, F, Sp, Sm, hF, hN, hT1, hT2, hϑ0, hϑ, hC0, hCA,
    hQA, hQ, hlp, hlm, hSp, hSm, hgp, hgm, hcp, hcm, hEp0, hEp, hEm0, hEm, hWp, hWm, hε⟩ := h
  exact two_sided_lag_of_slots F hF Sp Sm hN hT1 hT2 hϑ0 hϑ hC0 hCA hQA hQ hlp hlm hSp hSm hgp hgm
    hcp hcm hEp0 hEp hEm0 hEm hWp hWm hε

/-- The inputs of Theorem 2.1(i) as in `PartIInputsLag`, with the two-sided lag (12) replaced by
the slot-level data of the proof of Corollary 3.8 (`SlotData`) at every height `x ≥ X₀`. -/
def PartIInputsSlots (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (α γ xp : ℕ → ℝ) (Qmax κp : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ Qmax x ∧ Qmax x ≤ queueB X₀ x) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), SlotData (P.N x)
      (target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x) (Qmax x)
      (capH X₀ x / 2 * (1 + κp x / Real.log x)) x)

/-- The slot-level data give the two-sided lag (12), hence `PartIInputsLag`. -/
theorem PartIInputsSlots.toLag {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (h : PartIInputsSlots θ X₀ P) : PartIInputsLag θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, Qmax, κp, hκ, hκ1, hsp, hα, hxp, hAu, hρ, hQ, hκp, hslot⟩ := h
  refine ⟨κ, A, u, α, γ, xp, Qmax, κp, hκ, hκ1, hsp, hα, hxp, hAu, hρ, hQ, hκp, fun x hx => ?_⟩
  have := (hslot x hx).two_sided
  constructor
  · have h1 := this.1
    have e : -(capH X₀ x / 2) * (1 + κp x / Real.log x) =
        -(capH X₀ x / 2 * (1 + κp x / Real.log x)) := by ring
    rw [e]; exact h1
  · exact this.2

/-- Refined inputs for one system: `PartIInputsSlots` and `Theorem410InputsRankin`. -/
def TheoremAInputsSlots (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlots θ X₀ P ∧ Theorem410InputsRankin θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsRankin`, with the two-sided lag (12)
replaced by the slot-level data of the proof of Corollary 3.8. -/
def Theorem21InputsSlots : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsSlots θ X₀ (P ω)

theorem theorem21InputsRankin_of_slots (h : Theorem21InputsSlots) : Theorem21InputsRankin := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1.toLag, (hP ω hω).2⟩⟩

/-- The refined hypothesis `Theorem21InputsSlots` implies Theorem 2.1. -/
theorem theorem21_of_slots (h : Theorem21InputsSlots) : Theorem21 :=
  theorem21_of_rankin (theorem21InputsRankin_of_slots h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsSlots`. -/
theorem corollary_2_2_of_slots (h : Theorem21InputsSlots) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_slots h)

end
