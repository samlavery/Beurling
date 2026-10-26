module

public import RequestProject.Beurling.PartICapl
public import RequestProject.Beurling.Lemma51NatFull

/-!
# The queue bound (75): the explicit `B(x)` and its size

Theorem 6.6(ii) bounds the queue at the slots `s_j ∈ [x, 2x)` of a dyadic scale `x` by

  `B(x) := 4 M₁ L² / c' + 16 M₁ L / 3 + 4 √(M₁ L (K_d + 4)) + 8 M₁ L (L/Λ + 1) + K_d + 9`  (75)

with `c' = 0.15`, `K_d = 3`, `Λ = log X₀` and `L = log(2x + 12 log x + 2)`. The paper then uses
`B(x) ≤ 5 M₁ L² / c' ≤ 34 M₁ L²`.

* `queueBound75` : the right side of (75);
* `queueBound75_le` : `B ≤ 5 M₁ L²/c' ≤ 34 M₁ L²` for `c' = 0.15`, `K_d = 3`, `M₁ ≥ 1`,
  `L ≥ 10⁸`, `Λ ≥ 10⁸`;
* `queueBound75_cap_le` : with `M₁ = M̄₁` of Theorem 6.23 and `L = log(2x + 12 log x + 2)`,
  `B(x) ≤ 34 M̄₁ (log x)²` for `x ≥ X₀`, `log X₀ ≥ 10⁸`;
* `PartIInputsQueue75`, `Theorem21InputsQueue75` : the hypothesis of `PartICapl` with the queue
  bound function `B` **fixed to the explicit `B(x)` of (75)**, so that the size condition
  `B ≤ 34 M̄₁ L²` is no longer assumed; `corollary_2_2_of_queue75` derives Corollary 2.2.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink

namespace QueueBound

/-- The queue bound `B(x)` of (75), as a function of `M₁`, `L`, `Λ`, `c'` and `K_d`. -/
noncomputable def queueBound75 (M1 L Λ c' Kd : ℝ) : ℝ :=
  4 * M1 * L ^ 2 / c' + 16 * M1 * L / 3 + 4 * Real.sqrt (M1 * L * (Kd + 4)) +
    8 * M1 * L * (L / Λ + 1) + Kd + 9

/-- **The size of the queue bound (75)**: for `c' = 0.15`, `K_d = 3`, `M₁ ≥ 1`, `L ≥ 10⁸` and
`Λ ≥ 10⁸`, `B ≤ 5 M₁ L² / c' ≤ 34 M₁ L²`. -/
theorem queueBound75_le {M1 L Λ : ℝ} (hM : 1 ≤ M1) (hL : 10 ^ 8 ≤ L) (hΛ : 10 ^ 8 ≤ Λ) :
    queueBound75 M1 L Λ 0.15 3 ≤ 5 * M1 * L ^ 2 / 0.15 ∧
      5 * M1 * L ^ 2 / 0.15 ≤ 34 * M1 * L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hML : 1 ≤ M1 * L := by nlinarith
  have hsq : Real.sqrt (M1 * L * (3 + 4)) ≤ 7 * (M1 * L) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hLΛ : L / Λ ≤ L / 10 ^ 8 := div_le_div_of_nonneg_left hL0.le (by norm_num) hΛ
  have hM0 : 0 < M1 := by linarith
  have h1 : 8 * M1 * L * (L / Λ) ≤ 8 * M1 * L * (L / 10 ^ 8) :=
    mul_le_mul_of_nonneg_left hLΛ (by positivity)
  have hMLL : M1 * L * 10 ^ 8 ≤ M1 * L * L := mul_le_mul_of_nonneg_left hL (by positivity)
  constructor
  · unfold queueBound75
    have e : 8 * M1 * L * (L / Λ + 1) = 8 * M1 * L * (L / Λ) + 8 * M1 * L := by ring
    rw [e]
    have e2 : 8 * M1 * L * (L / 10 ^ 8) = 8 / 10 ^ 8 * (M1 * L * L) := by ring
    rw [e2] at h1
    have e3 : 4 * M1 * L ^ 2 / 0.15 = 80 / 3 * (M1 * L * L) := by ring
    have e4 : 5 * M1 * L ^ 2 / 0.15 = 100 / 3 * (M1 * L * L) := by ring
    rw [e3, e4]
    have hu : 16 * M1 * L / 3 = 16 / 3 * (M1 * L) := by ring
    have hv : 8 * M1 * L * (L / Λ) + 8 * M1 * L = 8 * M1 * L * (L / Λ) + 8 * (M1 * L) := by ring
    rw [hu, hv]
    generalize M1 * L * L = w at *
    generalize 8 * M1 * L * (L / Λ) = t at *
    generalize √(M1 * L * (3 + 4)) = q at *
    generalize M1 * L = u at *
    norm_num at *
    linarith
  · have : (0 : ℝ) ≤ M1 * L ^ 2 := by positivity
    rw [div_le_iff₀ (by norm_num)]
    nlinarith

/-- `M̄₁ ≥ 1` (for `log X₀ ≥ 10⁸`, `x ≥ X₀`). -/
lemma one_le_capM1 {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    1 ≤ capM1 X₀ x := by
  obtain ⟨-, -, h3⟩ := logs_of_ge hX0 hX hx
  unfold capM1 BSCert.Capl.Mbar1 BSCert.Capl.rbar0
  rw [ell_eq]
  have hr : 0 ≤ Real.exp (Real.log (Real.log x)) / (3 * Real.log (Real.log x)) + 4 := by
    positivity
  set r := Real.exp (Real.log (Real.log x)) / (3 * Real.log (Real.log x)) + 4
  set c := Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ x))
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have : 0 ≤ r * Real.sqrt c := mul_nonneg hr (Real.sqrt_nonneg _)
  have : 0 ≤ r * (r + 1) / 2 := by positivity
  simp only
  linarith

/-- `L = log(2x + 12 log x + 2)` lies between `log x` and `log x + 1.4`, for `log x ≥ 10⁸`. -/
lemma logL_bounds {x : ℝ} (hx0 : 0 < x) (hx : 10 ^ 8 ≤ Real.log x) :
    Real.log x ≤ Real.log (2 * x + 12 * Real.log x + 2) ∧
      Real.log (2 * x + 12 * Real.log x + 2) ≤ Real.log x + 1.4 := by
  have hx1 : 1 + 10 ^ 8 ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  have hlin := Lemma51Nat.log_le_lin hx0
  constructor
  · exact Real.log_le_log hx0 (by linarith)
  · have h3 : 2 * x + 12 * Real.log x + 2 ≤ 4 * x := by linarith
    calc Real.log (2 * x + 12 * Real.log x + 2) ≤ Real.log (4 * x) :=
          Real.log_le_log (by linarith) h3
      _ = Real.log 4 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ Real.log x + 1.4 := by
          have : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
          have := Real.log_two_lt_d9
          linarith

/-- **(75) at the scale `x`, with `M₁ = M̄₁`**: `B(x) ≤ 34 M̄₁ (log x)²`, where
`B(x) = queueBound75 M̄₁ (log(2x + 12 log x + 2)) (log X₀) 0.15 3`. -/
theorem queueBound75_cap_le {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) :
    queueBound75 (capM1 X₀ x) (Real.log (2 * x + 12 * Real.log x + 2)) (Real.log X₀) 0.15 3 ≤
      34 * capM1 X₀ x * Real.log x ^ 2 := by
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
  have hxpos : 0 < x := by
    by_contra hc; push_neg at hc
    have : x = 0 ∨ x < 0 := by rcases hc.lt_or_eq with h | h <;> [right; left] <;> assumption
    have hX0' : X₀ = 0 := le_antisymm (hx.trans hc) hX0
    rw [hX0', Real.log_zero] at hX; norm_num at hX
  obtain ⟨hL1, hL2⟩ := logL_bounds hxpos h1
  have hM := one_le_capM1 hX0 hX hx
  obtain ⟨hB, -⟩ := queueBound75_le hM (h1.trans hL1) hX
  refine hB.trans ?_
  set L := Real.log x
  set L' := Real.log (2 * x + 12 * Real.log x + 2)
  have hLL : L' ^ 2 ≤ 1.0001 * L ^ 2 := by nlinarith
  have hM0 : 0 ≤ capM1 X₀ x := by linarith
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hLL hM0]

end QueueBound

open QueueBound

/-- The explicit queue bound of (75) at height `x`, with `M₁ = M̄₁(log X₀, s(x))`,
`L = log(2x + 12 log x + 2)`, `Λ = log X₀`, `c' = 0.15` and `K_d = 3`. -/
noncomputable def queueB (X₀ x : ℝ) : ℝ :=
  queueBound75 (capM1 X₀ x) (Real.log (2 * x + 12 * Real.log x + 2)) (Real.log X₀) 0.15 3

/-- The inputs of Theorem 2.1(i) as in `PartIInputsCapl`, with the queue bound **fixed to the
explicit `B(x)` of (75)**: the only remaining queue input is the lag bound
`|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` (Theorem 6.6 with Corollary 3.8). -/
def PartIInputsQueue75 (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (α γ xp : ℕ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ),
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x| ≤
        queueB X₀ x + 3 * capH X₀ x + 3)

/-- The size estimate `B(x) ≤ 34 M̄₁ L²` of (75) turns `PartIInputsQueue75` into
`PartIInputsCapl`. -/
theorem PartIInputsQueue75.toCapl {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hX : 10 ^ 8 ≤ Real.log X₀) (h : PartIInputsQueue75 θ X₀ P) : PartIInputsCapl θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, hκ, hκ1, hsp, hα, hxp, hAu, hρ, hD⟩ := h
  exact ⟨κ, A, u, α, γ, xp, queueB X₀, hκ, hκ1, hsp, hα, hxp, hAu, hρ,
    fun x hx => queueBound75_cap_le (Nat.cast_nonneg _) hX hx, hD⟩

/-- Refined inputs for one system: `PartIInputsQueue75` and the inputs of Theorem 4.10. -/
def TheoremAInputsQueue75 (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsQueue75 θ X₀ P ∧ Theorem410InputsZB48 θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the queue bound fixed to the explicit `B(x)` of
(75). -/
def Theorem21InputsQueue75 : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsQueue75 θ X₀ (P ω)

theorem theorem21InputsCapl_of_queue75 (h : Theorem21InputsQueue75) : Theorem21InputsCapl := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1.toCapl hlog, (hP ω hω).2⟩⟩

/-- The refined hypothesis with the explicit queue bound (75) implies Theorem 2.1. -/
theorem theorem21_of_queue75 (h : Theorem21InputsQueue75) : Theorem21 :=
  theorem21_of_capl (theorem21InputsCapl_of_queue75 h)

/-- **Corollary 2.2** from the refined hypothesis with the explicit queue bound (75). -/
theorem corollary_2_2_of_queue75 (h : Theorem21InputsQueue75) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_queue75 h)

end
