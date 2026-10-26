module

public import RequestProject.Beurling.Theorem410ZB
public import RequestProject.Beurling.Lemma48ii
public import RequestProject.Beurling.AbsorbedGrowth

/-!
# The bounds at the chosen heights from Lemma 4.8

In `Theorem410InputsZB` the two bounds at the chosen heights `γ_k`, `|Z_B(1 + iγ_k)| ≥ 0.6` and
`|D̂_{<a_k}| ≤ 1/16` on the disc of radius `δ_k` around `1 + iγ_k`, were assumed. In the paper they
come from the choice rule of Lemma 4.8 (`γ_k` is a point of the set `S_k` of good heights in
`[Γ_k, 2Γ_k]` whenever `S_k ≠ ∅`) and the fact that `S_k ≠ ∅` (Lemma 4.8). Here
`Theorem410InputsZB48` replaces the two bounds by

* the choice rule (`ChoiceRule`),
* `κ Γ_k ≥ e^{X₀²/3}`, `D̂_{<a_k}` entire, and
* the inputs of the proof of Lemma 4.8(ii) for `f = D̂_{<a_k}` (`Lemma48Pieces`): the
  decomposition into the Dirichlet sum over the residual elements, a pointwise bounded part and the
  `ρ̄_A` part, with the counting hypotheses and the numerical condition;

and derives the two bounds (`Theorem410InputsZB48.toZB`), hence Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  GoodHeights Finset

namespace GoodHeights

/-- `γ` is a good height in `[Γ, 2Γ]` for `Z_B` and `f` (the set `S_k` of Lemma 4.8). -/
def GoodHeight (X₀ : ℕ) (κ : ℝ) (f : ℂ → ℂ) (Γ γ : ℝ) : Prop :=
  γ ∈ Set.Icc Γ (2 * Γ) ∧ 0.6 ≤ ‖ZBcont X₀ κ (1 + γ * I)‖ ∧
    ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16

/-- The choice rule of Lemma 4.8: `γ` is a good height whenever one exists. -/
def ChoiceRule (X₀ : ℕ) (κ : ℝ) (f : ℂ → ℂ) (Γ γ : ℝ) : Prop :=
  (∃ γ', GoodHeight X₀ κ f Γ γ') → GoodHeight X₀ κ f Γ γ

/-- The inputs of the proof of Lemma 4.8(ii) for `f` at height `Γ` (see
`lemma_4_8_ii_L2_of_pieces`, with `C = 100`). -/
def Lemma48Pieces (X₀ : ℕ) (Γ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (p : ℂ → ℂ) (w : ℝ → ℝ) (m J : ℕ) (X η M c α β : ℝ) (n : Fin m → ℝ),
    Measurable p ∧ Measurable w ∧ 2 ≤ X ∧ 0 ≤ η ∧ η ≤ 1 / 8 ∧ Monotone n ∧
    (∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X) ∧
    (∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5) ∧
    (∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤ 1.02 * N) ∧
    0 < M ∧ (∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), ‖p z‖ ≤ M) ∧
    0 ≤ α ∧ α ≤ β ∧ 0 < c ∧ (∀ u ∈ Set.Icc α β, |w u| ≤ c) ∧
    1 ≤ (β - α) * (Γ + 1 / 2) ∧
    (∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) +
      (p z + ∫ u in Set.Icc α β, (w u : ℂ) * cexp ((1 - z) * u))) ∧
    25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      (Real.sqrt ((Γ + 1 / 2) / 2) * M +
        2 * Real.sqrt (1 + Real.log ((β - α) * (Γ + 1 / 2))) * c * Real.exp (β / 4)) ≤
      100 * (X₀ : ℝ) ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ

/-- **Lemma 4.8 (a good height exists)** from the inputs of the proof of part (ii). -/
theorem exists_goodHeight {X₀ : ℕ} (hX₀ : Real.exp 100 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hP : Lemma48Pieces X₀ Γ f) : ∃ γ, GoodHeight X₀ κ f Γ γ := by
  obtain ⟨p, w, m, J, X, η, M, c, α, β, n, hp, hw, hX, hη0, hη, hmono, hrange, hwin, hcount,
    hM, hpM, hα, hαβ, hc, hwc, hL, hdec, hnum⟩ := hP
  have h := lemma_4_8_ZB_of_pieces hX₀ hκ hκ1 hΓ hf hp hw hX hη0 hη hmono hrange hwin hcount
    hM hpM hα hαβ hc hwc hL hdec hnum
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  have hpos : (0 : ENNReal) < ENNReal.ofReal (0.018 * Γ) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨γ, hγ⟩ := nonempty_of_measure_ne_zero (lt_of_lt_of_le hpos h).ne'
  exact ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩

lemma exp_100_le_of_log {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀) : Real.exp 100 ≤ X₀ := by
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra h; push_neg at h
    have : (X₀ : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hX; linarith
  rw [← Real.exp_log hX0]; exact Real.exp_le_exp.mpr (by linarith)

end GoodHeights

namespace DesignedZero

/-- **The inputs of Theorem 4.10 with the heights chosen by Lemma 4.8.** As `Theorem410InputsZB`,
but the two bounds at the chosen heights are replaced by the choice rule of Lemma 4.8 and the
inputs of the proof of Lemma 4.8(ii) for `D̂_{<a_k}` (`Dlt k`), at the heights `Γ_k`; and the
`1/16` requirement on the absorbed set is replaced by the growth condition
`δ_k ℓ + 2 log(2 + ℓ) + 5 ≤ ς(ℓ)` for `0 ≤ ℓ ≤ log(γ_k + 1)/(1 - θ/2)`
(`Absorbed.absorbedBound_le_of_growth`). -/
def Theorem410InputsZB48 (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ T κ₀ η : ℝ) (α γ xp a Γ : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℕ) (u : ℕ → ℝ) (ς : ℝ → ℝ),
    10 ^ 4 ≤ Real.log X₀ ∧ 0 < κ ∧ κ ≤ 1 ∧ Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T ∧
    (∀ k, DesignParams θ (Real.log X₀) κ₀ (α k) (γ k) (xp k)) ∧
    (∀ k, T + 1 / 2 ≤ γ k) ∧
    (∀ k, Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ k) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48Pieces X₀ (Γ k) (Dlt k)) ∧
    (∀ k, ChoiceRule X₀ κ (Dlt k) (Γ k) (γ k)) ∧
    (∀ k, 1 ≤ α k ∧ α k ≤ 2) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k ≤ xp k) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (θ / 2) A u ∧ Monotone ς ∧
    (∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) ∧
    (∀ k, ∀ ℓ ∈ Set.Icc 0 (Real.log (γ k + 1) / (1 - θ / 2)),
      designRadius (xp k) * ℓ + 2 * Real.log (2 + ℓ) + 5 ≤ ς ℓ) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (θ / 2) A u s)

/-- The two bounds at the chosen heights follow from Lemma 4.8, and the `1/16` requirement from
the growth condition. -/
theorem Theorem410InputsZB48.toZB {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsZB48 θ F) :
    Theorem410InputsZB θ F := by
  obtain ⟨X₀, κ, T, κ₀, η, α, γ, xp, a, Γ, D, Dlt, A, u, ς, hX, hκ, hκ1, hT, hP, hγT, hΓ,
    hDd, hpieces, hrule, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hgrowth, hdec⟩ := h
  have hgood : ∀ k, GoodHeight X₀ κ (Dlt k) (Γ k) (γ k) := fun k =>
    hrule k (exists_goodHeight (exp_100_le_of_log hX) hκ hκ1 (hΓ k) (hDd k) (hpieces k))
  have hB : ∀ k, ∀ τ : ℝ, |τ - γ k| ≤ 1 →
      absorbedBound ς (designRadius (xp k)) (|τ| ^ (1 / (1 - θ / 2))) ≤ 1 / 16 := by
    intro k τ hτ
    have hγ2 := (hP k).γ_ge
    have hθ := (hP k).θ_le
    have hτ' := abs_le.mp hτ
    have hτ1 : 1 ≤ τ := by linarith
    rw [abs_of_pos (by linarith : (0 : ℝ) < τ)]
    have hp : 0 < 1 - θ / 2 := by linarith
    have hY : 1 ≤ τ ^ (1 / (1 - θ / 2)) := Real.one_le_rpow hτ1 (by positivity)
    have hδ := ((hP k).radius_bounds).1.le
    refine Absorbed.absorbedBound_le_of_growth hς hδ hY fun ℓ hℓ => hgrowth k ℓ ⟨hℓ.1, ?_⟩
    refine hℓ.2.trans ?_
    rw [Real.log_rpow (by linarith), div_eq_mul_inv, one_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.log_le_log (by linarith) (by linarith)
  refine ⟨X₀, κ, T, κ₀, η, α, γ, xp, a, D, Dlt, A, u, ς, hX, hκ, hκ1, hT, hP, hγT,
    fun k => (hgood k).2.1, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hB, hdec, ?_⟩
  intro k s hs
  apply (hgood k).2.2 s
  have hr := (hP k).radius_bounds
  exact closedBall_subset_closedBall (by linarith [hr.2.1]) hs

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system, with the heights chosen by Lemma 4.8. -/
def TheoremAInputsZB48 (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsZB48 θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the heights chosen by Lemma 4.8. -/
def Theorem21InputsZB48 : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsZB48 θ X₀ (P ω)

theorem theorem21InputsZB_of_ZB48 (h : Theorem21InputsZB48) : Theorem21InputsZB := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toZB⟩⟩

/-- The refined hypothesis (heights chosen by Lemma 4.8) implies Theorem 2.1. -/
theorem theorem21_of_ZB48 (h : Theorem21InputsZB48) : Theorem21 :=
  theorem21_of_ZB (theorem21InputsZB_of_ZB48 h)

/-- **Corollary 2.2** from the refined hypothesis with the heights chosen by Lemma 4.8. -/
theorem corollary_2_2_of_ZB48 (h : Theorem21InputsZB48) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_ZB48 h)

end
