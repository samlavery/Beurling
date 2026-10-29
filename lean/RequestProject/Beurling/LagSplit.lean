module

public import RequestProject.Beurling.SlotCount

/-!
# Proposition 4.1 with the paper's split at `x = X₀ + 2H(x)`

The paper states the two-sided lag (12) (Corollary 3.8) only for `x ≥ X₀ + 2H(x)`. On the initial
range `X₀ ≤ x < X₀ + 2H(x)` the proof of Proposition 4.1 runs the accounting of Corollary 3.8 with
`j := j₀ - 1` and obtains the weaker bound

  `|D(x)| ≤ B(X₀) + (H(X₀)/2)(1 + κ₊/log X₀) + 5`

(constant `5` instead of `3`, and everything evaluated at `X₀`).

In `PartIInputsSlots` the slot data of Corollary 3.8 was assumed at every `x ≥ X₀`. Here it is
assumed only where the paper proves it, and the initial range carries the paper's weaker bound:

* `LagSplit.lag_rpow_of_queue` : `|D| ≤ B(x) + 3H(x) + 3` implies `|D| ≤ x^η` for `x ≥ X₀`, with the
  explicit `B = queueB` and `H = capH` (the numerical part of Proposition 4.1);
* `LagSplit.lag_rpow_initial` : the initial-range bound implies `|D(x)| ≤ x^η` for `x ≥ X₀`;
* `PartIInputsSlotsSplit` : the inputs `PartIInputsSlots` with the slot data only for
  `x ≥ X₀ + 2H(x)` and the initial-range bound on `[X₀, X₀ + 2H(x))`;
* `PartIInputsSlotsSplit.toTarget` : **Proposition 4.1** `|D(x)| ≤ x^η` for all `x ≥ X₀`, i.e.
  `PartIInputsTarget`;
* `theorem21_of_split`, `corollary_2_2_of_split` : Theorem 2.1 and Corollary 2.2 from the refined
  hypothesis `Theorem21InputsSplit`.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound Bookkeeping
  SlotCount

namespace LagSplit

/-- **Proposition 4.1, numerical part, with the explicit `B` and `H`.** For `log X₀ ≥ 10⁸`,
`x ≥ X₀`, `θ ∈ [1/4, 1/2 - 10⁻⁴]`: if `|D| ≤ B(x) + 3H(x) + 3` then `|D| ≤ x^η`. -/
theorem lag_rpow_of_queue {θ X₀ x D : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
    (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hD : |D| ≤ queueB X₀ x + 3 * capH X₀ x + 3) : |D| ≤ x ^ lagExponent θ := by
  obtain ⟨hM, hstd, hraise⟩ := capH_conditions hX0 hX hx
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
  have hX0' : 0 < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hx0 : 0 < x := lt_of_lt_of_le hX0' hx
  have hlogL : 2 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    linarith
  have hH1 : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
  have hBH : queueB X₀ x ≤ capH X₀ x :=
    queueBound_le_H (queueBound75_cap_le hX0 hX hx) hM hstd hlogL (by linarith)
  exact lag_le_rpow hx0 (by linarith) hH1 hBH (by linarith)
    (lagExponent_ge (by linarith) hθ2) hD

/-- **Proposition 4.1 on the initial range.** For `log X₀ ≥ 10⁸`, `x ≥ X₀` and
`0 ≤ κ₊ ≤ log X₀`, the bound `|D| ≤ B(X₀) + (H(X₀)/2)(1 + κ₊/log X₀) + 5` implies `|D| ≤ x^η`. -/
theorem lag_rpow_initial {θ X₀ x D κ : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
    (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ Real.log X₀)
    (hD : |D| ≤ queueB X₀ X₀ + capH X₀ X₀ / 2 * (1 + κ / Real.log X₀) + 5) :
    |D| ≤ x ^ lagExponent θ := by
  obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX le_rfl
  have hH1 : 1 ≤ capH X₀ X₀ := le_trans (Real.one_le_exp (by positivity)) hstd
  have hLX : 0 < Real.log X₀ := by linarith
  have hk1 : κ / Real.log X₀ ≤ 1 := (div_le_one hLX).mpr hκ
  have hk0 : 0 ≤ κ / Real.log X₀ := div_nonneg hκ0 hLX.le
  have hD' : |D| ≤ queueB X₀ X₀ + 3 * capH X₀ X₀ + 3 := by nlinarith
  have hX0' : 0 < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hη : 0 ≤ lagExponent θ := by
    have := lagExponent_ge (θ := θ) (by linarith) hθ2; linarith
  exact (lag_rpow_of_queue hθ1 hθ2 hX0 hX le_rfl hD').trans
    (Real.rpow_le_rpow hX0'.le hx hη)

/-- **The accounting of Corollary 3.8 on the initial range** (proof of Proposition 4.1, with
`j := j₀ - 1`). The data are those of `two_sided_lag_of_slots`, except that the landing slack is
only `ε ≤ 5/2` (it covers the variation of `H` across `[X₀, X₀ + 2H]`). Then
`-W - 5 ≤ N - T ≤ Q_max + W + 5`, i.e. the constant `5` of the proof of Proposition 4.1. -/
theorem initial_lag_of_slots {x j T N Q A C Ep Em ϑ W ε Qmax c lp lm : ℝ}
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
    (hWp : c * lp ≤ W + ε) (hWm : c * lm ≤ W + ε) (hε : ε ≤ 5 / 2) :
    -W - 5 ≤ N - T ∧ N - T ≤ Qmax + W + 5 := by
  have hp := card_le_of_slope F hF Sp (by linarith) hSp hgapp (c := c) (by simpa using hcp)
  have hm := card_le_of_slope F hF Sm (by linarith) hSm hgapm (c := c) (by simpa using hcm)
  simp only [add_sub_cancel_left, sub_sub_cancel] at hp hm
  constructor <;> linarith

end LagSplit

open LagSplit

/-- The inputs of Theorem 2.1(i) with **the paper's split in Proposition 4.1**. As
`PartIInputsSlots`, except that the slot data of Corollary 3.8 (`SlotData`, giving (12)) is assumed
only for `x ≥ X₀ + 2H(x)`, where the paper states (12). On the initial range
`X₀ ≤ x < X₀ + 2H(x)` only the bound of the proof of Proposition 4.1 is assumed:
`|N_P(x) - T(x)| ≤ B(X₀) + (H(X₀)/2)(1 + κ₊(X₀)/log X₀) + 5`. -/
def PartIInputsSlotsSplit (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (Qmax κp : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ Qmax x ∧ Qmax x ≤ queueB X₀ x) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x → SlotData (P.N x)
      (target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x) (Qmax x)
      (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x| ≤
        queueB X₀ X₀ + capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀) + 5)

/-- **Proposition 4.1 (the lag bound (13)) with the paper's split**: the split inputs give
`|N_P(x) - T(x)| ≤ x^η` for every `x ≥ X₀`, hence `PartIInputsTarget`. -/
theorem PartIInputsSlotsSplit.toTarget {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000) (hX : 10 ^ 8 ≤ Real.log X₀)
    (h : PartIInputsSlotsSplit θ X₀ P) : PartIInputsTarget θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, Qmax, κp, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hQ, hκp, hslot,
    hinit⟩ := h
  have hX1 : (1 : ℝ) ≤ X₀ := by
    by_contra hc; push_neg at hc
    have : Real.log X₀ ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc.le
    linarith
  have hW : AbsorbedWindowHyp (θ / 2) X₀ A u :=
    ⟨by linarith, by linarith, hX1, fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2, hAfin⟩
  refine ⟨κ, countA A, absorbedDensityCap (θ / 2) A u, α, γ, xp, hκ, hκ1, hsp, hα, hxp,
    fun x hx => absorbed_target_error_cap hW (by linarith) hρ hx, fun x hx => ?_⟩
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · -- late range: (12) from the slot data, then the queue bound and the numerical part
    have hLx : 0 < Real.log x := by
      have := Real.log_le_log (by linarith) hx; linarith
    obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
    have hH : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
    have h12 := (hslot x hx hlate).two_sided
    have e : -(capH X₀ x / 2 * (1 + κp x / Real.log x)) =
        -(capH X₀ x / 2) * (1 + κp x / Real.log x) := by ring
    rw [e] at h12
    exact lag_rpow_of_queue hθ1 hθ2 hX0 hX hx
      (abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH
        ((hQ x hx).1.trans (hQ x hx).2) (hQ x hx).2 h12.1 h12.2)
  · -- initial range: the bound of the proof of Proposition 4.1
    exact lag_rpow_initial hθ1 hθ2 hX0 hX hx (hκp X₀ le_rfl).1 (hκp X₀ le_rfl).2
      (hinit x hx hearly)

/-- Refined inputs for one system: `PartIInputsSlotsSplit` and `Theorem410InputsRankin`. -/
def TheoremAInputsSplit (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotsSplit θ X₀ P ∧ Theorem410InputsRankin θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsSlots`, with the slot data of
Corollary 3.8 only for `x ≥ X₀ + 2H(x)` and the paper's weaker bound on the initial range. -/
def Theorem21InputsSplit : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsSplit θ X₀ (P ω)

theorem theorem21InputsZB48_of_split (h : Theorem21InputsSplit) : Theorem21InputsZB48 := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.toTarget hθ.1 hθ.2 hlog, (hP ω hω).2.toDesign.toCount.toZB48⟩⟩

/-- The refined hypothesis `Theorem21InputsSplit` implies Theorem 2.1. -/
theorem theorem21_of_split (h : Theorem21InputsSplit) : Theorem21 :=
  theorem21_of_ZB48 (theorem21InputsZB48_of_split h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsSplit`. -/
theorem corollary_2_2_of_split (h : Theorem21InputsSplit) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_split h)

end
