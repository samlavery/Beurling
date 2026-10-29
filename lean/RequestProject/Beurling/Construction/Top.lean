module

public import RequestProject.Beurling.Construction.Sparsity
public import RequestProject.Beurling.Construction.Budget

/-!
# Theorem 2.1 / Corollary 2.2 without Lemma 6.26 and the Rankin bound for `A` as inputs

`Theorem21InputsSp` is `Theorem21InputsFix` with the following inputs **removed** (they are now
proved, `lemma626_construction`, `rankinA_construction`, `goodAll_prob_ge_table`):

* Lemma 6.26, `#(A ∩ [v, v + v^{θ/2}]) ≤ v^{θ/2} (log v)^{-4}`;
* the Rankin bound `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` for `log x > (log X₀)²`;
* the union bound `∑_E P(Eᶜ) ≤ 1.5/log X₀`: it is replaced by the per-scale bounds of Table 1 on
  the good events, `∑_{E at scale 2^m X₀} P(Eᶜ ∩ Good(< t(E))) ≤ 1.0001 (log X₀ + m log 2)^{-2} +
  3.2 (2^m X₀)^{-2}` (`TableBudget`), from which Lemma 6.10 is proved (first failure and
  summation).

In their place it takes the data they are proved from:

* the coupling of `A` with the construction (`AbsorbedCoupling`): the origin of each realised prime
  (rational, or decided at a slot of the greedy run with jitter width `H = max(H_std, M̄₁²)` and
  the jitters `ω`), `A ⊆` the absorbed set (5) for the latest-prime map, and the latest-prime map
  being the latest prime in the decision order (this also contains the former input
  `A ⊆ absorbedRule …`);
* (HBS) for the realised system, with `log X₀⁻ ≥ 100` and `X₀⁻ ≥ X₀/2 + 1`;
* the cluster event at every `v ≥ X₀` (`ClusterUpTo`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex Metric Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize CaplLink
  QueueBound LagSplit SlotModel Decomp QueueMono Bookkeeping

namespace Construction

/-- `PartIRest` without Lemma 6.26. -/
def PartIRestSp (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ)
    (M : SlotModel X₀) : Prop :=
  (∀ n ∈ A, (X₀ : ℝ) ≤ u n ∧ u n + u n ^ (θ / 2) = n) ∧
    (∀ x, M.T x = target X₀ (kappaParam X₀) (countA A) (absorbedDensityCap (θ / 2) A u)
      (osc θ (designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x) ∧
    M.QueueWindowData ∧
    ∃ κp : ℝ → ℝ,
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (P.N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)

/-- `Theorem410Rest` without the absorbed-set rule (now part of the coupling) and without the
Rankin bound for `A`: the pieces of `D̂_{<a_k}` and the construction scales. -/
def Theorem410RestSp (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ)
    (a : ℕ → ℝ) : Prop :=
  (∀ k, Lemma48PiecesCount X₀ (heightScale θ kappa0Param (switchOn X₀ k))
      (earlyOf P θ X₀ (kappaParam X₀) A u
        (designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (switchOn X₀) a k)) ∧
    (∀ k, 0 < a k ∧ a k ≤ switchOn X₀ k ∧ switchOn X₀ k ≤ (1 + 1 / 1000) * a k)

/-- (HBS) for the realised system at every height and the cluster event at every height. -/
def SparsityInputs (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (X0m η1 η2 : ℝ) (ε1 : ℝ → ℝ), 100 ≤ Real.log X0m ∧ (X₀ : ℝ) / 2 + 1 ≤ X0m ∧
    (∀ z, P.HBS X0m z η1 η2 ε1) ∧
    ∀ v ≥ (X₀ : ℝ), ClusterUpTo P X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- **Theorem 2.1, hypothesis on the concrete construction, without Lemma 6.26 and the Rankin
bound for `A`.** As `Theorem21InputsFix`, with those two inputs replaced by the coupling of `A`
with the construction, (HBS) and the cluster event, and with the probability budget replaced by
the per-scale bounds of Table 1. -/
def Theorem21InputsSp : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (P : JitterΩ → BeurlingSystem) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      FailureAdapted jitterFiltration E time ∧
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ∃ (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ) (M : SlotModel X₀) (latest : ℝ → ℝ),
          PartIRestSp θ X₀ (P ω) A u a M ∧ Theorem410RestSp θ X₀ (P ω) A u a ∧
          Nonempty (AbsorbedCoupling (P ω) M (capH X₀) ω A latest) ∧
          SparsityInputs X₀ (P ω)

/-- **`Theorem21InputsSp` gives `Theorem21InputsFixP`**: Lemma 6.26 and the Rankin bound for
`A` are derived (`lemma626_construction`, `rankinA_construction`), and the probability budget of
Lemma 6.10 follows from the per-scale bounds of Table 1 by first failure and summation
(`goodAll_prob_ge_table`). -/
theorem theorem21InputsFixP_of_sp (h : Theorem21InputsSp) : Theorem21InputsFixP := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨P, ι, hι, E, time, hE, ⟨scale, htab⟩, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (Real.exp_pos _) h1
  refine ⟨P, ι, E, goodAll_prob_ge_table jitterFiltration hE hX0 hlog htab, fun ω hG hω => ?_⟩
  obtain ⟨A, u, a, M, latest, hI, hC, ⟨C⟩, X0m, η1, η2, ε1, hX0m, hX0mX, hHBS, hcl⟩ :=
    hP ω hG hω
  obtain ⟨hAu, hT, hq, κp, hκp, hland, hinit⟩ := hI
  obtain ⟨hpieces, ha⟩ := hC
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C' : AbsorbedCoupling (P ω) R.M R.H R.U A latest := C
  have h626 := lemma626_construction C' hlog hθ.1 (by linarith [hθ.2]) rfl hω hHBS hX0m hX0mX hcl
  have hrank := rankinA_construction C' hlog rfl hω hHBS hX0m
  exact ⟨A, u, a, M, latest, ⟨hAu, C'.locFin, h626, hT, hq, κp, hκp, hland, hinit⟩,
    ⟨C.rule, hpieces, ha, hrank⟩⟩

/-- Theorem 2.1 from `Theorem21InputsSp`. -/
theorem theorem21_of_sp (h : Theorem21InputsSp) : Theorem21 :=
  theorem21_of_dec (theorem21InputsDec_of_fixP (theorem21InputsFixP_of_sp h))

/-- **Corollary 2.2** from `Theorem21InputsSp`. -/
theorem corollary_2_2_of_sp (h : Theorem21InputsSp) : ¬ QuestionQ :=
  corollary_2_2_of_dec (theorem21InputsDec_of_fixP (theorem21InputsFixP_of_sp h))

end Construction

end
