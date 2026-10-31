module

public import RequestProject.Beurling.Theorem410Absorbed
public import RequestProject.Beurling.BaseFactor

/-!
# Theorem 4.10 with the bounds of Lemma 4.2 derived

The hypotheses of Lemma 4.6 on `Z_B` (holomorphy on the disc, `|Z_B| ≤ 2 log X₀`,
`|Z_B'| ≤ 4.01 log² X₀`) are derived from Lemma 4.2 (`BaseFactor.lemma_4_2_ZB`): `Z_B` is
holomorphic and within `e^{-X₀²/4}` of `Z_∞ = ∏_{p<X₀}(1 - p^{-s})^{-1}` on
`1/2 ≤ σ ≤ 2`, `|t| ≥ T`, and the Mertens estimates hold. Together with
`Theorem410Absorbed` (Lemma 4.4(a) from the weight bounds, and `|Z_B| ≥ 1/2` from
Lemma 4.8(i)), this gives `Theorem410InputsBase`, and from it Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor

namespace DesignedZero

/-- The numerical parameters of Lemma 4.6 (the hypotheses not involving `Z_B`). -/
structure DesignParams (θ Λ κ₀ α γ x : ℝ) : Prop where
  θ_ge : 1 / 20 ≤ θ
  θ_le : θ ≤ 1 / 2
  Λ_ge : 10 ≤ Λ
  κ_ge : Real.exp (-Λ) ≤ κ₀
  κ_le : κ₀ ≤ 1 / 4
  one_lt_x : 1 < x
  loglog_ge : 2 * Λ ≤ Real.log (Real.log x)
  α_pos : 0 < α
  γ_ge : 2 ≤ γ
  αγ_eq : α * γ = κ₀ * x ^ (1 - θ) / Real.log x ^ 3

lemma DesignParams.radius_bounds {θ Λ κ₀ α γ x : ℝ} (h : DesignParams θ Λ κ₀ α γ x) :
    0 < designRadius x ∧ designRadius x ≤ 1 / 10 ^ 6 ∧ designRadius x * Λ ≤ 1 / 10 ^ 5 := by
  have hL : 0 < Real.log x := Real.log_pos h.one_lt_x
  have hbig := large_L h.Λ_ge hL h.loglog_ge
  have hLL : 20 ≤ Real.log (Real.log x) := by linarith [h.loglog_ge, h.Λ_ge]
  have hδ0 : 0 < designRadius x := by unfold designRadius; positivity
  have hΛ := h.Λ_ge
  have hδΛ3 : designRadius x * Λ ^ 3 ≤ 9 / 10 ^ 4 := by
    unfold designRadius
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hL (by norm_num)]
    nlinarith
  have hδΛ2 : designRadius x * Λ ^ 2 ≤ 1 / 10 ^ 4 := by
    have : designRadius x * Λ ^ 2 * 10 ≤ designRadius x * Λ ^ 3 := by
      rw [show designRadius x * Λ ^ 3 = designRadius x * Λ ^ 2 * Λ by ring]
      exact mul_le_mul_of_nonneg_left hΛ (by positivity)
    nlinarith
  have hδΛ : designRadius x * Λ ≤ 1 / 10 ^ 5 := by
    have : designRadius x * Λ * 10 ≤ designRadius x * Λ ^ 2 := by
      rw [show designRadius x * Λ ^ 2 = designRadius x * Λ * Λ by ring]
      exact mul_le_mul_of_nonneg_left hΛ (by positivity)
    nlinarith
  refine ⟨hδ0, ?_, hδΛ⟩
  have : designRadius x * 10 ≤ designRadius x * Λ := mul_le_mul_of_nonneg_left hΛ hδ0.le
  nlinarith

/-- **Lemma 4.2 gives the hypotheses of Lemma 4.6 on `Z_B`** (except `|Z_B| ≥ 1/2`). -/
theorem DesignParams.toLemma46HypPre {θ κ₀ α γ x : ℝ} {X₀ : ℕ}
    (h : DesignParams θ (Real.log X₀) κ₀ α γ x) (hX : 2 ≤ X₀)
    (hM1 : ZinfR X₀ 1 ≤ 1.8 * Real.log X₀) (hM2 : logSum X₀ 1 ≤ 1.01 * Real.log X₀)
    {ZB : ℂ → ℂ} {T : ℝ}
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ ZB z)
    (hclose : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZB z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4)))
    (hγT : T + 1 / 2 ≤ γ) :
    Lemma46HypPre θ (Real.log X₀) κ₀ α γ x ZB := by
  obtain ⟨hδ0, hδ, hδΛ⟩ := h.radius_bounds
  have key : ∀ s ∈ closedBall (1 + γ * I) (designRadius x),
      DifferentiableAt ℂ ZB s ∧ ‖ZB s‖ ≤ 2 * Real.log X₀ ∧
        ‖deriv ZB s‖ ≤ 4.01 * Real.log X₀ ^ 2 := by
    intro s hs
    have hd : ‖s - (1 + γ * I)‖ ≤ designRadius x := by rwa [mem_closedBall, dist_eq_norm] at hs
    have hre := Complex.abs_re_le_norm (s - (1 + γ * I))
    have him := Complex.abs_im_le_norm (s - (1 + γ * I))
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im,
      Complex.one_im, Complex.mul_im] at hre him
    norm_num at hre him
    have hσ1 : 1 - designRadius x ≤ s.re := by linarith [(abs_le.mp (hre.trans hd)).1]
    have hσ2 : s.re ≤ 7 / 4 := by linarith [(abs_le.mp (hre.trans hd)).2]
    have ht : T + 1 / 4 ≤ |s.im| := by
      have := (abs_le.mp (him.trans hd)).1
      have hγ0 : 0 ≤ γ := by linarith [h.γ_ge]
      calc T + 1 / 4 ≤ s.im := by linarith
        _ ≤ |s.im| := le_abs_self _
    exact lemma_4_2_ZB hX h.Λ_ge hM1 hM2 hdiff hclose hδ0.le (by linarith) hσ1 hσ2 ht
  exact ⟨h.θ_ge, h.θ_le, h.Λ_ge, h.κ_ge, h.κ_le, h.one_lt_x, h.loglog_ge, h.α_pos, h.γ_ge,
    h.αγ_eq, fun s hs => (key s hs).1, fun s hs => (key s hs).2.2, fun s hs => (key s hs).2.1⟩

/-- **The inputs of Theorem 4.10 with Lemma 4.2's bounds derived.** As
`Theorem410InputsAbsorbed`, but the bounds on `Z_B` in the hypotheses of Lemma 4.6 are replaced
by the inputs of Lemma 4.2: `Λ = log X₀`, the Mertens estimates
`Z_∞(1) ≤ 1.8 log X₀` and `∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀`, and `Z_B` holomorphic and within
`e^{-X₀²/4}` of `Z_∞` on `1/2 ≤ σ ≤ 2`, `|t| ≥ T`, with `γ_k ≥ T + 1/2`. -/
def Theorem410InputsBase (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (T κ₀ η : ℝ) (α γ xp a : ℕ → ℝ) (ZB : ℂ → ℂ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    2 ≤ X₀ ∧ ZinfR X₀ 1 ≤ 1.8 * Real.log X₀ ∧ logSum X₀ 1 ≤ 1.01 * Real.log X₀ ∧
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ ZB z) ∧
    (∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZB z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4))) ∧
    (∀ k, DesignParams θ (Real.log X₀) κ₀ (α k) (γ k) (xp k)) ∧
    (∀ k, T + 1 / 2 ≤ γ k) ∧
    (∀ k, 0.6 ≤ ‖ZB (1 + γ k * I)‖) ∧
    (∀ k, 1 ≤ α k ∧ α k ≤ 2) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k ≤ xp k) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (thetaB θ) A u ∧ Monotone ς ∧
    (∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) ∧
    (∀ k, ∀ τ : ℝ, |τ - γ k| ≤ 1 →
      absorbedBound ς (designRadius (xp k)) (|τ| ^ (1 / (1 - thetaB θ))) ≤ 1 / 16) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)),
      F s = ZB s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) + (Dlt k s + lateNoise D (a k) s) +
        absorbedHat (thetaB θ) A u s) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)), ‖Dlt k s‖ ≤ 1 / 16)

theorem Theorem410InputsBase.absorbed {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsBase θ F) :
    Theorem410InputsAbsorbed θ F := by
  obtain ⟨X₀, T, κ₀, η, α, γ, xp, a, ZB, D, Dlt, A, u, ς, hX, hM1, hM2, hdiff, hclose, hP, hγT,
    hc, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hB, hdec, hDlt⟩ := h
  exact ⟨Real.log X₀, κ₀, η, α, γ, xp, a, ZB, D, Dlt, A, u, ς,
    fun k => (hP k).toLemma46HypPre hX hM1 hM2 hdiff hclose (hγT k), hc, hα, hsp, hγx, hη0, hη,
    ha, hD, hA, hς, hN, hB, hdec, hDlt⟩

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system: part (i) with the concrete target (6), and the inputs of
Theorem 4.10 with Lemma 4.2's bounds and Lemma 4.4(a) derived (`Theorem410InputsBase`). -/
def TheoremAInputsBase (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsBase θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis (Lemma 4.2's bounds and Lemma 4.4(a) derived).** -/
def Theorem21InputsBase : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsBase θ X₀ (P ω)

theorem theorem21InputsAbsorbed_of_base (h : Theorem21InputsBase) : Theorem21InputsAbsorbed := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.absorbed⟩⟩

/-- The refined hypothesis (Lemma 4.2's bounds and Lemma 4.4(a) derived) implies Theorem 2.1. -/
theorem theorem21_of_base (h : Theorem21InputsBase) : Theorem21 :=
  theorem21_of_absorbed (theorem21InputsAbsorbed_of_base h)

/-- **Corollary 2.2** from the refined hypothesis (Lemma 4.2's bounds and Lemma 4.4(a)
derived). -/
theorem corollary_2_2_of_base (h : Theorem21InputsBase) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_base h)

end
