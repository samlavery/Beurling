module

public import RequestProject.Beurling.LagBound
public import RequestProject.Beurling.AbsorbedTargetError

/-!
# Theorem 2.1(i) with the concrete absorbed density and the queue bound

`PartIInputsConcrete` is `PartIInputsQueue` with the absorbed count and density made concrete:
the target (6) uses `#(A ∩ [1, x])` and the capped smoothed density `ρ̄_A` of the absorbed set
`A` (`Absorbed.absorbedDensityCap`, with `h(u) = u^{θ/2}`). The absorbed part of the target error
is then proved (Lemma 3.4, `Absorbed.absorbed_target_error_cap`) from

* the window structure: `u_a + u_a^{θ/2} = a` and `u_a ≥ X₀` for `a ∈ A`;
* the density bound `ρ_A(v) ≤ (log v)^{-4}` for `v ≥ X₀` (Lemma 6.27(a)).

`corollary_2_2_of_concrete` derives Corollary 2.2 from the corresponding hypothesis
`Theorem21InputsConcrete`.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed

/-- The inputs for Theorem 2.1(i) with the concrete absorbed density: as `PartIInputsQueue`, but
with `cntA = #(A ∩ [1, x])` and `rhoA = ρ̄_A` for an absorbed set `A` with windows `[u_a, a]`,
`u_a + u_a^{θ/2} = a`, `u_a ≥ X₀`, whose smoothed density satisfies `ρ_A(v) ≤ (log v)^{-4}`
(Lemma 6.27(a)). -/
def PartIInputsConcrete (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (B H M₁ : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), B x ≤ 34 * M₁ x * Real.log x ^ 2) ∧
    (∀ x ≥ (X₀ : ℝ), M₁ x ^ 2 ≤ H x) ∧
    (∀ x ≥ (X₀ : ℝ), Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ H x) ∧
    (∀ x ≥ (X₀ : ℝ), Real.log (H x) - 8 * Real.log (Real.log x) ^ 2 ≤ 1e-6 * Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ),
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x| ≤
        B x + 3 * H x + 3)

/-- Lemma 3.4 (absorbed part) turns `PartIInputsConcrete` into `PartIInputsQueue`. -/
theorem PartIInputsConcrete.toQueue {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2) (hX : 3 ≤ Real.log X₀)
    (h : PartIInputsConcrete θ X₀ P) : PartIInputsQueue θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, B, H, M₁, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hB, hM, hstd,
    hraise, hD⟩ := h
  have hX1 : (1 : ℝ) ≤ X₀ := by
    by_contra hc; push_neg at hc
    have : Real.log X₀ ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc.le
    linarith
  have hW : AbsorbedWindowHyp (θ / 2) X₀ A u :=
    ⟨by linarith, by linarith, hX1, fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2, hAfin⟩
  exact ⟨κ, countA A, absorbedDensityCap (θ / 2) A u, α, γ, xp, B, H, M₁, hκ, hκ1, hsp, hα, hxp,
    fun x hx => absorbed_target_error_cap hW hX hρ hx, hB, hM, hstd, hraise, hD⟩

/-- Refined inputs for one system: `PartIInputsConcrete` and the inputs of Theorem 4.10 with the
heights chosen by Lemma 4.8. -/
def TheoremAInputsConcrete (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsConcrete θ X₀ P ∧ Theorem410InputsZB48 θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the lag bound replaced by its inputs in
Proposition 4.1 and the absorbed part of the target error replaced by the inputs of Lemma 3.4. -/
def Theorem21InputsConcrete : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsConcrete θ X₀ (P ω)

theorem theorem21InputsQueue_of_concrete (h : Theorem21InputsConcrete) : Theorem21InputsQueue := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.toQueue hθ.1 (by linarith [hθ.2]) (by linarith), (hP ω hω).2⟩⟩

/-- The concrete refined hypothesis implies Theorem 2.1. -/
theorem theorem21_of_concrete (h : Theorem21InputsConcrete) : Theorem21 :=
  theorem21_of_queue (theorem21InputsQueue_of_concrete h)

/-- **Corollary 2.2** from the refined hypothesis with the lag bound (13) replaced by its inputs
in Proposition 4.1 and the absorbed target error by the inputs of Lemma 3.4. -/
theorem corollary_2_2_of_concrete (h : Theorem21InputsConcrete) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_concrete h)

end
