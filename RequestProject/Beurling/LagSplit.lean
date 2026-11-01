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
* `LagSplit.lagMax`, `LagSplit.subPow_lagMax` : the lag bound
  `D_max(x) = B(x) + 3H(x) + B(X₀) + 3H(X₀) + 5`, which is `x^{o(1)}`;
* `PartIInputsSlotsSplit.toTarget` : **Proposition 4.1** `|D(x)| ≤ D_max(x)` for all `x ≥ X₀`, i.e.
  `PartIInputsTarget`;
* `theorem21_of_split`, `corollary_2_2_of_split` : Theorem 2.1 and Corollary 2.2 from the refined
  hypothesis `Theorem21InputsSplit`.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound Bookkeeping
  SlotCount

namespace LagSplit

/-- **The lag bound `D_max`** (eq. (La)): `B(x) + 3H(x) + B(X₀) + 3H(X₀) + 5`, which bounds both
`B(x) + 3H(x) + 3` (from (12) and the queue bound) and the initial-range bound
`B(X₀) + (H(X₀)/2)(1 + κ₊/log X₀) + 5` of the proof of Proposition 4.1. -/
noncomputable def lagMax (X₀ x : ℝ) : ℝ :=
  queueB X₀ x + 3 * capH X₀ x + (queueB X₀ X₀ + 3 * capH X₀ X₀ + 5)

/-- **`D_max = x^{o(1)}`** (for `ℓ ≥ ℓ_std`, `H = H_std = e^{8ℓ²}` and `B ≤ 17 L² H_std^{1/2}`). -/
theorem subPow_lagMax {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    SubPow (lagMax X₀) X₀ := by
  have hX1 : 1 ≤ X₀ := by
    by_contra hc; push_neg at hc; linarith [Real.log_nonpos hX0 hc.le]
  have h1 := subPow_lag hX1 (B := queueB X₀) (H := capH X₀) (M₁ := capM1 X₀)
    (fun x hx => queueBound75_cap_le hX0 hX hx) (fun x hx => (capH_conditions hX0 hX hx).1)
    (fun x hx => le_trans (Real.one_le_exp (by positivity)) (capH_conditions hX0 hX hx).2.1)
    (subPow_capH hX0 hX)
  refine (h1.add (subPow_const (queueB X₀ X₀ + 3 * capH X₀ X₀ + 2) hX1)).mono le_rfl
    fun x _ => ?_
  unfold lagMax; linarith

/-- `8 (log Λ)² ≤ Λ/4` for `Λ ≥ 10⁸`. -/
lemma eight_log_sq_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : 8 * Real.log Λ ^ 2 ≤ Λ / 4 := by
  have hΛ0 : 0 < Λ := by linarith
  set q := Λ ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hΛ0 _
  have hq4 : q ^ 4 = Λ := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hl := Real.log_le_rpow_div hΛ0.le (show (0 : ℝ) < 1 / 4 by norm_num)
  rw [← hq] at hl
  have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hsq : Real.log Λ ^ 2 ≤ 16 * q ^ 2 := by nlinarith
  have hq2 : 1000 ≤ q ^ 2 := by nlinarith [sq_nonneg (q ^ 2 - 1000)]
  nlinarith

/-- **`D_max` beyond the switch-on** (eq. (Dmaxstd)): for `log log y ≥ 2Λ - 1` (the standard
regime, `H = H_std`, `B ≤ 17 L² H_std^{1/2}`), `D_max(y) ≤ e^{8ℓ² + Λ + 2}`, `ℓ = log log y`. -/
theorem lagMax_le_std {X₀ y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hy : X₀ ≤ y)
    (hℓ : 2 * Real.log X₀ - 1 ≤ Real.log (Real.log y)) :
    lagMax X₀ y ≤ Real.exp (8 * Real.log (Real.log y) ^ 2 + Real.log X₀ + 2) := by
  set Λ := Real.log X₀ with hΛ
  set ℓ := Real.log (Real.log y) with hℓdef
  obtain ⟨hLy, -, hl0⟩ := logs_of_ge hX0 hX hy
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : Real.log Λ ≤ Λ / 100 := by
    have := eight_log_sq_le hX
    have h1 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
    nlinarith
  -- the standard regime at `y`
  have hs : sHroot < capS X₀ y := by
    unfold capS; rw [← hΛ, ← hℓdef]; linarith [sHroot_mem.2]
  have h4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hstd : 7.5 * Λ + Real.log 4 ≤ 4 * ℓ ^ 2 := by nlinarith
  obtain ⟨hM, hH⟩ := capH_eq_std hX0 hX hy hs hstd
  -- `B(y) ≤ 34 M̄₁ L² ≤ 17 e^{4ℓ²} e^{2ℓ} ≤ e^{8ℓ²}`
  have hB : queueB X₀ y ≤ Real.exp (8 * ℓ ^ 2) := by
    have h1 := queueBound75_cap_le hX0 hX hy
    have hL : Real.log y = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hL2 : Real.log y ^ 2 = Real.exp (2 * ℓ) := by
      rw [hL, ← Real.exp_nat_mul]; norm_num
    have h2 : 34 * capM1 X₀ y * Real.log y ^ 2 ≤ 17 * Real.exp (4 * ℓ ^ 2 + 2 * ℓ) := by
      rw [hL2, Real.exp_add]
      have := Real.exp_pos (2 * ℓ)
      nlinarith
    have h3 : 17 * Real.exp (4 * ℓ ^ 2 + 2 * ℓ) ≤ Real.exp (8 * ℓ ^ 2) := by
      have he : (17 : ℝ) ≤ Real.exp 3 := by
        have h5 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have := Real.exp_one_gt_d9
        rw [h5]
        calc (17 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) this.le 3
      calc 17 * Real.exp (4 * ℓ ^ 2 + 2 * ℓ) ≤ Real.exp 3 * Real.exp (4 * ℓ ^ 2 + 2 * ℓ) :=
            mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = Real.exp (4 * ℓ ^ 2 + 2 * ℓ + 3) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (8 * ℓ ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    unfold queueB; linarith
  -- the constants at `X₀`: `B(X₀) + 3H(X₀) + 5 ≤ e^Λ`
  have hC : queueB X₀ X₀ + 3 * capH X₀ X₀ + 5 ≤ Real.exp Λ := by
    obtain ⟨hM0, hstd0, hr0⟩ := capH_conditions hX0 hX le_rfl
    have hH0 : 0 < capH X₀ X₀ := lt_of_lt_of_le (Real.exp_pos _) hstd0
    have h8 := eight_log_sq_le hX
    have hHle : capH X₀ X₀ ≤ Real.exp (Λ / 2) := by
      rw [← Real.exp_log hH0, Real.exp_le_exp]
      linarith
    have hM1 : capM1 X₀ X₀ ≤ Real.exp (Λ / 4) := by
      have h0 := capM1_pos hX0 hX (le_refl X₀)
      have e : Real.exp (Λ / 2) = Real.exp (Λ / 4) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have := hM0.trans (hHle.trans e.le)
      nlinarith [Real.exp_pos (Λ / 4)]
    have hB0 := queueBound75_cap_le hX0 hX (le_refl X₀)
    have hB0' : queueB X₀ X₀ ≤ 34 * Real.exp (Λ / 4) * Λ ^ 2 := by
      unfold queueB
      have := mul_le_mul_of_nonneg_right hM1 (show 0 ≤ 34 * Λ ^ 2 by positivity)
      nlinarith
    -- `34 Λ² ≤ e^{Λ/4}`
    have hΛe : 34 * Λ ^ 2 ≤ Real.exp (Λ / 4) := by
      have h1 := Real.pow_div_factorial_le_exp (Λ / 4) (by positivity) 3
      simp [Nat.factorial] at h1
      nlinarith
    have he1 : Real.exp (Λ / 4) * Real.exp (Λ / 4) = Real.exp (Λ / 2) := by
      rw [← Real.exp_add]; ring_nf
    have he3 : 4 * Real.exp (Λ / 2) + 5 ≤ Real.exp Λ := by
      have e : Real.exp Λ = Real.exp (Λ / 2) * Real.exp (Λ / 2) := by
        rw [← Real.exp_add]; ring_nf
      have h1 : 10 ≤ Real.exp (Λ / 2) := by
        have := Real.add_one_le_exp (Λ / 2); linarith
      rw [e]; nlinarith
    have hq : queueB X₀ X₀ ≤ Real.exp (Λ / 2) := by
      have := mul_le_mul_of_nonneg_left hΛe (Real.exp_pos (Λ / 4)).le
      nlinarith
    linarith
  have hE : Real.exp (8 * ℓ ^ 2 + Λ + 2) = Real.exp (8 * ℓ ^ 2) * Real.exp Λ * Real.exp 2 := by
    rw [← Real.exp_add, ← Real.exp_add]
  have he2 : (5 : ℝ) ≤ Real.exp 2 := by
    have h5 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_gt_d9
    rw [h5]
    calc (5 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) this.le 2
  set P := Real.exp (8 * ℓ ^ 2) with hP
  set Q := Real.exp Λ with hQ
  have h1 : 1 ≤ P := Real.one_le_exp (by positivity)
  have h2 : 1 ≤ Q := Real.one_le_exp hΛ0.le
  have hPQ1 : P ≤ P * Q := le_mul_of_one_le_right (by linarith) h2
  have hPQ2 : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) h1
  have hPQ : 5 * (P * Q) ≤ P * Q * Real.exp 2 := by
    have := mul_le_mul_of_nonneg_left he2 (show 0 ≤ P * Q by positivity); linarith
  have hlag : lagMax X₀ y ≤ 4 * P + Q := by
    unfold lagMax; rw [hH]; linarith
  rw [hE]; linarith

/-- **Proposition 4.1, numerical part, with the explicit `B` and `H`.** For `log X₀ ≥ 10⁸`,
`x ≥ X₀`, `θ ∈ [10⁻⁴, 1/2 - 10⁻⁴]`: if `|D| ≤ B(x) + 3H(x) + 3` then `|D| ≤ x^η`. -/
theorem lag_rpow_of_queue {θ X₀ x D : ℝ} (hθ1 : 1 / 10000 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
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
theorem lag_rpow_initial {θ X₀ x D κ : ℝ} (hθ1 : 1 / 10000 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
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
  exact (lag_rpow_of_queue (by linarith) hθ2 hX0 hX le_rfl hD').trans
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
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + winH X₀ (u a) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (winH X₀) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ Qmax x ∧ Qmax x ≤ queueB X₀ x) ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x → SlotData (P.N x)
      (target X₀ κ (countA A) (absorbedDensityCap (winH X₀) A u) (osc θ α γ xp) x) (Qmax x)
      (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (winH X₀) A u) (osc θ α γ xp) x| ≤
        queueB X₀ X₀ + capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀) + 5)

/-- **`D_max = O(e^{8ℓ²})`** on `[X₀, ∞)` (`ℓ = log log x`): eq. (Dmaxstd) in the standard regime
`ℓ ≥ 2Λ - 1`, and `D_max = x^{o(1)}` below it. -/
theorem lagMax_le_exp {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    ∃ c : ℝ, ∀ x ≥ X₀, lagMax X₀ x ≤ c * Real.exp (8 * Real.log (Real.log x) ^ 2) := by
  obtain ⟨C, hC⟩ := subPow_lagMax hX0 hX (1 / 2) (by norm_num)
  set Λ := Real.log X₀ with hΛ
  refine ⟨max (Real.exp (Λ + 2)) (|C| * Real.exp (Real.exp (2 * Λ) / 2)), fun x hx => ?_⟩
  have hX1 : 1 < X₀ := by
    by_contra hc; push_neg at hc; linarith [Real.log_nonpos hX0 hc]
  have hx0 : 0 < x := by linarith
  have he1 : 1 ≤ Real.exp (8 * Real.log (Real.log x) ^ 2) := Real.one_le_exp (by positivity)
  have hm0 : 0 ≤ max (Real.exp (Λ + 2)) (|C| * Real.exp (Real.exp (2 * Λ) / 2)) :=
    le_trans (Real.exp_pos _).le (le_max_left _ _)
  by_cases hℓ : 2 * Λ - 1 ≤ Real.log (Real.log x)
  · have h1 := lagMax_le_std hX0 hX hx hℓ
    have e : Real.exp (8 * Real.log (Real.log x) ^ 2 + Λ + 2) =
        Real.exp (Λ + 2) * Real.exp (8 * Real.log (Real.log x) ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push_neg at hℓ
    have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hLx : Real.log x < Real.exp (2 * Λ) := by
      have := (Real.log_lt_iff_lt_exp hL0).mp hℓ
      exact this.trans (Real.exp_lt_exp.mpr (by linarith))
    have hsq : x ^ (1 / 2 : ℝ) ≤ Real.exp (Real.exp (2 * Λ) / 2) := by
      rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp]; linarith
    have h1 := hC x hx
    have h2 : C * x ^ (1 / 2 : ℝ) ≤ |C| * Real.exp (Real.exp (2 * Λ) / 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg C))
    calc lagMax X₀ x ≤ max (Real.exp (Λ + 2)) (|C| * Real.exp (Real.exp (2 * Λ) / 2)) :=
          h1.trans (h2.trans (le_max_right _ _))
      _ ≤ _ := le_mul_of_one_le_right hm0 he1

/-- `PartIInputsTarget` with the lag bound `D_max = lagMax X₀` (eq. (La)) explicit. -/
def PartIInputsTargetLag (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (cntA rhoA : ℝ → ℝ) (α γ xp : ℕ → ℝ), 0 < κ ∧ κ ≤ 1 ∧ Spacing xp ∧
    (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ x ≥ (X₀ : ℝ), |cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u| ≤ 2 * Absorbed.winH X₀ x) ∧
    (∀ x ≥ (X₀ : ℝ), |P.N x - target X₀ κ cntA rhoA (osc θ α γ xp) x| ≤ lagMax X₀ x)

/-- **Proposition 4.1 (the lag bound (La)) with the paper's split**: the split inputs give
`|N_P(x) - T(x)| ≤ D_max(x)` for every `x ≥ X₀`. -/
theorem PartIInputsSlotsSplit.toTargetLag {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hXw : 10 ^ 8 ≤ Real.log X₀)
    (h : PartIInputsSlotsSplit θ X₀ P) : PartIInputsTargetLag θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, Qmax, κp, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hQ, hκp, hslot,
    hinit⟩ := h
  have hX := hXw
  have hX1 : (1 : ℝ) ≤ X₀ := by
    by_contra hc; push_neg at hc
    have : Real.log X₀ ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc.le
    linarith
  have hW : AbsorbedWindowHyp (winH X₀) X₀ A u :=
    ⟨winH_isWin hXw, hX1, fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2, hAfin⟩
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  refine ⟨κ, countA A, absorbedDensityCap (winH X₀) A u, α, γ, xp, hκ, hκ1, hsp, hα,
    hxp, fun x hx => absorbed_target_error_cap hW (by linarith) hρ hx, fun x hx => ?_⟩
  have hB0 : 0 ≤ queueB X₀ X₀ := (hQ X₀ le_rfl).1.trans (hQ X₀ le_rfl).2
  have hBx : 0 ≤ queueB X₀ x := (hQ x hx).1.trans (hQ x hx).2
  have hH0 : 0 ≤ capH X₀ X₀ := le_trans (Real.exp_pos _).le (le_max_left _ _)
  have hHx : 0 ≤ capH X₀ x := le_trans (Real.exp_pos _).le (le_max_left _ _)
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · -- late range: (12) from the slot data and the queue bound
    have hLx : 0 < Real.log x := by
      have := Real.log_le_log (by linarith) hx; linarith
    obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
    have hH : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
    have h12 := (hslot x hx hlate).two_sided
    have e : -(capH X₀ x / 2 * (1 + κp x / Real.log x)) =
        -(capH X₀ x / 2) * (1 + κp x / Real.log x) := by ring
    rw [e] at h12
    have := abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH
        ((hQ x hx).1.trans (hQ x hx).2) (hQ x hx).2 h12.1 h12.2
    unfold lagMax; linarith
  · -- initial range: the bound of the proof of Proposition 4.1
    have h1 := hinit x hx hearly
    have hLX : 0 < Real.log X₀ := by linarith
    have hk1 : κp X₀ / Real.log X₀ ≤ 1 := (div_le_one hLX).mpr (hκp X₀ le_rfl).2
    have hk0 : 0 ≤ κp X₀ / Real.log X₀ := div_nonneg (hκp X₀ le_rfl).1 hLX.le
    have : capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀) ≤ 3 * capH X₀ X₀ := by nlinarith
    unfold lagMax; linarith

/-- **Proposition 4.1 (the lag bound (La)) with the paper's split**, in the form
`PartIInputsTarget` (`D_max = x^{o(1)}`). -/
theorem PartIInputsSlotsSplit.toTarget {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hXw : 10 ^ 8 ≤ Real.log X₀)
    (h : PartIInputsSlotsSplit θ X₀ P) : PartIInputsTarget θ X₀ P := by
  obtain ⟨κ, cntA, rhoA, α, γ, xp, hκ, hκ1, hsp, hα, hxp, hA, hD⟩ := h.toTargetLag hXw
  exact ⟨κ, cntA, rhoA, α, γ, xp, lagMax X₀, hκ, hκ1, hsp, hα, hxp, hA, hD,
    subPow_lagMax (Nat.cast_nonneg _) hXw⟩

/-- Refined inputs for one system: `PartIInputsSlotsSplit` and `Theorem410InputsRankin`. -/
def TheoremAInputsSplit (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotsSplit θ X₀ P ∧ Theorem410InputsRankin θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsSlots`, with the slot data of
Corollary 3.8 only for `x ≥ X₀ + 2H(x)` and the paper's weaker bound on the initial range. -/
def Theorem21InputsSplit : Prop :=
  ∃ XHux : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) (1 / 2 - 1 / 10000), ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsSplit θ X₀ (P ω)

theorem theorem21InputsZB48_of_split (h : Theorem21InputsSplit) : Theorem21InputsZB48 := by
  obtain ⟨XHux, hX⟩ := h
  refine ⟨XHux, fun θ hθ X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX θ hθ X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.toTarget hlog, (hP ω hω).2.toDesign.toCount.toZB48⟩⟩

/-- The refined hypothesis `Theorem21InputsSplit` implies Theorem 2.1. -/
theorem theorem21_of_split (h : Theorem21InputsSplit) : Theorem21 :=
  theorem21_of_ZB48 (theorem21InputsZB48_of_split h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsSplit`. -/
theorem corollary_2_2_of_split (h : Theorem21InputsSplit) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_split h)

end
