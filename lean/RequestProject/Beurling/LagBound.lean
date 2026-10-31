module

public import RequestProject.Beurling.Bookkeeping
public import RequestProject.Beurling.Theorem410Lemma48

/-!
# The lag bound (13) from the queue bound (Proposition 4.1)

* `Bookkeeping.abs_lag_le_of_two_sided` : the two-sided lag (12) with `max Q ≤ B` gives
  `|D| ≤ B + 3H + 3`.
* `Bookkeeping.lag_bound` : **Proposition 4.1**: if `|D| ≤ B + 3H + 3`, where the queue bound
  satisfies `B ≤ 34 M₁ L²` (75), the jitter width satisfies `H ≥ M₁²`, `H ≥ H_std = e^{8ℓ²}` and
  `log H - log H_std ≤ 10⁻⁶ L` (Theorem 6.23(c)), then `|D(x)| ≤ x^η`, `η = min(θ, 1/2 - θ)/2`,
  for `θ ∈ [1/20, 1/2 - 10⁻⁴]` and `log x ≥ 10⁸ - 1`.
* `PartIInputsQueue` : the inputs of Theorem 2.1(i) with the lag bound (13) replaced by the bound
  `|N_P - T| ≤ B + 3H + 3` (from (12) and the queue bound, Theorem 6.6) and the size conditions on
  `B` and `H`; `PartIInputsQueue.toTarget` derives `PartIInputsTarget`.
* `corollary_2_2_of_queue` : Corollary 2.2 from the corresponding refined hypothesis
  `Theorem21InputsQueue`.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation

namespace Bookkeeping

/-- The two-sided lag (12), `-(H/2)(1 + κ₊/log x) - 4 ≤ D ≤ max Q + (H/2)(1 + κ₊/log x) + 3`, with
`max Q ≤ B`, `0 ≤ B`, `H ≥ 1` and `0 ≤ κ₊ ≤ log x`, gives `|D| ≤ B + 3H + 3` (the form used in the
proof of Proposition 4.1). -/
theorem abs_lag_le_of_two_sided {D Qmax B H κp Lx : ℝ} (hLx : 0 < Lx) (hκ0 : 0 ≤ κp)
    (hκ : κp ≤ Lx) (hH : 1 ≤ H) (hB0 : 0 ≤ B) (hQB : Qmax ≤ B)
    (hlo : -(H / 2) * (1 + κp / Lx) - 4 ≤ D) (hhi : D ≤ Qmax + H / 2 * (1 + κp / Lx) + 3) :
    |D| ≤ B + 3 * H + 3 := by
  have h1 : κp / Lx ≤ 1 := (div_le_one hLx).mpr hκ
  have h0 : 0 ≤ κp / Lx := div_nonneg hκ0 hLx.le
  rw [abs_le]; constructor <;> nlinarith

/-- **Proposition 4.1 (the lag bound (13))**. Let `θ ∈ [1/20, 1/2 - 10⁻⁴]`, `η = min(θ, 1/2 - θ)/2`
and `X > 0` with `log X ≥ 10⁸ - 1`. Suppose that for `x ≥ X` the lag satisfies `|D(x)| ≤ B(x) + 3H(x) + 3`
(by (12) and the queue bound, Theorem 6.6), where the queue bound satisfies
`B(x) ≤ 34 M₁(x) L²` ((75), `L = log x`), and the jitter width satisfies `H ≥ M₁²`,
`H ≥ H_std = exp(8ℓ²)` (`ℓ = log L`) and `log H - 8ℓ² ≤ 10⁻⁶ L` (Theorem 6.23(c)).
Then `|D(x)| ≤ x^η` for all `x ≥ X`. -/
theorem lag_bound {θ X : ℝ} (hθ1 : 1 / 20 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
    (hX0 : 0 < X) (hX : 10 ^ 8 - 1 ≤ Real.log X) (D B H M₁ : ℝ → ℝ)
    (hB : ∀ x ≥ X, B x ≤ 34 * M₁ x * Real.log x ^ 2)
    (hM : ∀ x ≥ X, M₁ x ^ 2 ≤ H x)
    (hstd : ∀ x ≥ X, Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ H x)
    (hraise : ∀ x ≥ X, Real.log (H x) - 8 * Real.log (Real.log x) ^ 2 ≤ 1e-6 * Real.log x)
    (hD : ∀ x ≥ X, |D x| ≤ B x + 3 * H x + 3) :
    ∀ x ≥ X, |D x| ≤ x ^ lagExponent θ := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hX0 hx
  have hL : 10 ^ 8 - 1 ≤ Real.log x := hX.trans (Real.log_le_log hX0 hx)
  have hlogL : 2 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    linarith
  have hH1 : 1 ≤ H x := le_trans (Real.one_le_exp (by positivity)) (hstd x hx)
  have hBH : B x ≤ H x :=
    queueBound_le_H (hB x hx) (hM x hx) (hstd x hx) hlogL (by linarith)
  exact lag_le_rpow hx0 hL hH1 hBH (by linarith [hraise x hx])
    (lagExponent_ge (by linarith) hθ2) (hD x hx)

end Bookkeeping

open Bookkeeping

/-- The inputs for Theorem 2.1(i) with the concrete target (6), where the lag bound (13) is
replaced by its inputs in Proposition 4.1: for `x ≥ X₀`,

* `|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` (from the two-sided lag (12) and the queue bound,
  Theorem 6.6);
* `B(x) ≤ 34 M₁(x) (log x)²` (75);
* `H(x) ≥ M₁(x)²`, `H(x) ≥ H_std(x) = exp(8 (log log x)²)` and
  `log H(x) - log H_std(x) ≤ 10⁻⁶ log x` (Section 2.2, Theorem 6.23(c));

together with the absorbed part of the target error, as in `PartIInputsTarget`. -/
def PartIInputsQueue (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (cntA rhoA : ℝ → ℝ) (α γ xp : ℕ → ℝ) (B H M₁ : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ x ≥ (X₀ : ℝ), |cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u| ≤ 2 * x ^ (thetaB θ)) ∧
    (∀ x ≥ (X₀ : ℝ), B x ≤ 34 * M₁ x * Real.log x ^ 2) ∧
    (∀ x ≥ (X₀ : ℝ), M₁ x ^ 2 ≤ H x) ∧
    (∀ x ≥ (X₀ : ℝ), Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ H x) ∧
    (∀ x ≥ (X₀ : ℝ), Real.log (H x) - 8 * Real.log (Real.log x) ^ 2 ≤ 1e-6 * Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ),
      |P.N x - target X₀ κ cntA rhoA (osc θ α γ xp) x| ≤ B x + 3 * H x + 3)

/-- Proposition 4.1 turns `PartIInputsQueue` into `PartIInputsTarget`. -/
theorem PartIInputsQueue.toTarget {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hθ1 : 1 / 20 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000) (hX : 10 ^ 8 - 1 ≤ Real.log X₀)
    (h : PartIInputsQueue θ X₀ P) : PartIInputsTarget θ X₀ P := by
  obtain ⟨κ, cntA, rhoA, α, γ, xp, B, H, M₁, hκ, hκ1, hsp, hα, hxp, hA, hB, hM, hstd, hraise,
    hD⟩ := h
  have hX0 : (0 : ℝ) < X₀ := by
    rcases (Nat.cast_nonneg X₀ : (0 : ℝ) ≤ X₀).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  exact ⟨κ, cntA, rhoA, α, γ, xp, hκ, hκ1, hsp, hα, hxp, hA,
    lag_bound hθ1 hθ2 hX0 hX _ B H M₁ hB hM hstd hraise hD⟩

/-- Refined inputs for one system: `PartIInputsQueue` and the inputs of Theorem 4.10 with the
heights chosen by Lemma 4.8. -/
def TheoremAInputsQueue (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsQueue θ X₀ P ∧ Theorem410InputsZB48 θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the lag bound (13) replaced by its inputs in
Proposition 4.1. -/
def Theorem21InputsQueue : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsQueue θ X₀ (P ω)

theorem theorem21InputsZB48_of_queue (h : Theorem21InputsQueue) : Theorem21InputsZB48 := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 - 1 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this; linarith
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.toTarget hθ.1 hθ.2 hlog, (hP ω hω).2⟩⟩

/-- The refined hypothesis with the lag bound replaced by its inputs implies Theorem 2.1. -/
theorem theorem21_of_queue (h : Theorem21InputsQueue) : Theorem21 :=
  theorem21_of_ZB48 (theorem21InputsZB48_of_queue h)

/-- **Corollary 2.2** from the refined hypothesis with the lag bound (13) replaced by its inputs
in Proposition 4.1. -/
theorem corollary_2_2_of_queue (h : Theorem21InputsQueue) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_queue h)

end
