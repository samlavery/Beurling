module

public import RequestProject.Beurling.Theorem410Paper
public import RequestProject.Beurling.AbsorbedPart

/-!
# Theorem 4.10 with the concrete absorbed part and Lemma 4.8(i) at the centre

This file links the weight bounds (i)–(iv) after (14) to the inputs of Theorem 4.10:

* the absorbed part in the decomposition (14) is the concrete series
  `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))` (`Absorbed.absorbedHat`), and Lemma 4.4(a)
  (`|Ê_A| ≤ 1/16` on each disc) is **derived** from the weight bounds, the counting bound
  `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}` (Rankin, Lemma 6.26) and partial summation
  (`Absorbed.norm_absorbedHat_le`), given that the explicit bound `absorbedBound` is `≤ 1/16`
  at the heights of the disc;
* the hypothesis `|Z_B| ≥ 1/2` of Lemma 4.6 on the disc is **derived** from Lemma 4.8(i),
  `|Z_B(1 + iγ_k)| ≥ 0.6`, and the derivative bound `|Z_B'| ≤ 4.01 Λ²`, as in the proof of
  Theorem 4.10 (`Lemma46HypPre.toLemma46Hyp`).
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed

namespace DesignedZero

/-- The hypotheses of Lemma 4.6 except the lower bound `|Z_B| ≥ 1/2` on the disc. -/
structure Lemma46HypPre (θ Λ κ₀ α γ x : ℝ) (ZB : ℂ → ℂ) : Prop where
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
  diff : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), DifferentiableAt ℂ ZB s
  deriv_le : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), ‖deriv ZB s‖ ≤ 4.01 * Λ ^ 2
  norm_le : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), ‖ZB s‖ ≤ 2 * Λ

/-- **Lemma 4.8(i) gives the hypothesis of Lemma 4.6.** If `|Z_B(1 + iγ)| ≥ 0.6`, then
`|Z_B| ≥ 0.59 ≥ 1/2` on the disc `|s - (1 + iγ)| ≤ δ_k`, since `δ_k · 4.01 Λ² ≤ 0.01`. -/
theorem Lemma46HypPre.toLemma46Hyp {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}
    (h : Lemma46HypPre θ Λ κ₀ α γ x ZB) (hc : 0.6 ≤ ‖ZB (1 + γ * I)‖) :
    Lemma46Hyp θ Λ κ₀ α γ x ZB := by
  have hL : 0 < Real.log x := Real.log_pos h.one_lt_x
  have hbig := large_L h.Λ_ge hL h.loglog_ge
  have hLL : 20 ≤ Real.log (Real.log x) := by linarith [h.loglog_ge, h.Λ_ge]
  have hδ0 : 0 < designRadius x := by unfold designRadius; positivity
  have hδΛ3 : designRadius x * Λ ^ 3 ≤ 9 / 10 ^ 4 := by
    unfold designRadius
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hL (by norm_num)]
    nlinarith
  have hΛ := h.Λ_ge
  have hδΛ2 : designRadius x * Λ ^ 2 ≤ 1 / 10 ^ 4 := by
    have : designRadius x * Λ ^ 2 * 10 ≤ designRadius x * Λ ^ 3 := by
      rw [show designRadius x * Λ ^ 3 = designRadius x * Λ ^ 2 * Λ by ring]
      exact mul_le_mul_of_nonneg_left hΛ (by positivity)
    nlinarith
  refine ⟨h.θ_ge, h.θ_le, h.Λ_ge, h.κ_ge, h.κ_le, h.one_lt_x, h.loglog_ge, h.α_pos, h.γ_ge,
    h.αγ_eq, h.diff, h.deriv_le, fun s hs => ?_, h.norm_le⟩
  have hc0 : (1 + γ * I) ∈ closedBall (1 + γ * I) (designRadius x) :=
    mem_closedBall_self hδ0.le
  have hlip := (convex_closedBall _ _).norm_image_sub_le_of_norm_deriv_le h.diff h.deriv_le
    hc0 hs
  have hd : ‖s - (1 + γ * I)‖ ≤ designRadius x := by
    rwa [mem_closedBall, dist_eq_norm] at hs
  have h1 : 4.01 * Λ ^ 2 * ‖s - (1 + γ * I)‖ ≤ 4.01 * (designRadius x * Λ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4.01 * Λ ^ 2 by positivity)
    linarith
  have h2 := norm_sub_norm_le (ZB (1 + γ * I)) (ZB s)
  rw [norm_sub_rev] at hlip
  linarith

/-- **The inputs of Theorem 4.10 with the concrete absorbed part.** As `Theorem410InputsPaper`,
but:

* the hypothesis `|Z_B| ≥ 1/2` of Lemma 4.6 is replaced by Lemma 4.8(i) at the centre,
  `|Z_B(1 + iγ_k)| ≥ 0.6`;
* the absorbed part in the decomposition (14) is `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))`,
  with weights `w_a` for `b = θ/2`, and Lemma 4.4(a) is replaced by its inputs: the counting bound
  `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}` with `ς` nondecreasing, and `absorbedBound ≤ 1/16` at every
  height `τ` with `|τ - γ_k| ≤ 1` (with `δ = δ_k`). -/
def Theorem410InputsAbsorbed (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (Λ κ₀ η : ℝ) (α γ xp a : ℕ → ℝ) (ZB : ℂ → ℂ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    (∀ k, Lemma46HypPre θ Λ κ₀ (α k) (γ k) (xp k) ZB) ∧
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

/-- **Lemma 4.4(a) on the discs.** On `|s - (1 + iγ_k)| ≤ δ_k`, `|Ê_A(s)| ≤ 1/16`. -/
theorem norm_absorbedHat_le_disc {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}
    (hH : Lemma46Hyp θ Λ κ₀ α γ x ZB) (hα : α ≤ 2) {A : Set ℝ} {u : ℝ → ℝ} {ς : ℝ → ℝ}
    (hA : AbsorbedHyp (thetaB θ) A u) (hς : Monotone ς)
    (hN : ∀ y ≥ 1, countA A y ≤ y * Real.exp (-ς (Real.log y)))
    (hB : ∀ τ : ℝ, |τ - γ| ≤ 1 → absorbedBound ς (designRadius x) (|τ| ^ (1 / (1 - thetaB θ))) ≤
      1 / 16)
    {s : ℂ} (hs : s ∈ closedBall (1 + γ * I) (designRadius x)) :
    ‖absorbedHat (thetaB θ) A u s‖ ≤ 1 / 16 := by
  have hδ := hH.δ_le
  have hδ0 := hH.δ_pos
  have hd : ‖s - (1 + γ * I)‖ ≤ designRadius x := by rwa [mem_closedBall, dist_eq_norm] at hs
  have hre := Complex.abs_re_le_norm (s - (1 + γ * I))
  have him := Complex.abs_im_le_norm (s - (1 + γ * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.one_im, Complex.mul_im] at hre him
  norm_num at hre him
  have hσ1 : 1 - designRadius x ≤ s.re := by linarith [(abs_le.mp (hre.trans hd)).1]
  have hσ2 : s.re ≤ 2 := by linarith [(abs_le.mp (hre.trans hd)).2]
  have ht1 : |s.im - γ| ≤ 1 := by linarith
  have hγ := hH.γ_ge_log hα
  have hL := hH.L_ge_big
  have ht : 2 ≤ |s.im| := by
    have := (abs_le.mp ht1).1
    rw [abs_of_nonneg (by linarith)]; linarith
  exact ((norm_absorbedHat_le hA hς hN hδ0.le (by linarith) hσ1 hσ2 ht).2).trans (hB _ ht1)

/-- The concrete-absorbed-part inputs give the paper-form inputs of Theorem 4.10: Lemma 4.4(a)
follows from the weight bounds and partial summation, and the hypothesis `|Z_B| ≥ 1/2` of
Lemma 4.6 from Lemma 4.8(i). -/
theorem Theorem410InputsAbsorbed.paper {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsAbsorbed θ F) :
    Theorem410InputsPaper θ F := by
  obtain ⟨Λ, κ₀, η, α, γ, xp, a, ZB, D, Dlt, A, u, ς, hPre, hc, hα, hsp, hγx, hη0, hη, ha, hD,
    hA, hς, hN, hB, hdec, hDlt⟩ := h
  have hH : ∀ k, Lemma46Hyp θ Λ κ₀ (α k) (γ k) (xp k) ZB := fun k => (hPre k).toLemma46Hyp (hc k)
  exact ⟨Λ, κ₀, η, α, γ, xp, a, ZB, D, Dlt, fun k => absorbedHat (thetaB θ) A u, hH, hα, hsp, hγx,
    hη0, hη, ha, hD, hdec, hDlt,
    fun k s hs => norm_absorbedHat_le_disc (hH k) (hα k).2 hA hς hN (hB k) hs⟩

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system: part (i) with the concrete target (6), and the inputs of
Theorem 4.10 with the concrete absorbed part (`Theorem410InputsAbsorbed`). -/
def TheoremAInputsAbsorbed (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsAbsorbed θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis (absorbed part concrete)**: as `Theorem21InputsPaper`,
with Lemma 4.4(a) reduced to the weight bounds plus the counting bound on `A`, and the lower
bound on `Z_B` reduced to Lemma 4.8(i) at the centre. -/
def Theorem21InputsAbsorbed : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsAbsorbed θ X₀ (P ω)

theorem theorem21InputsPaper_of_absorbed (h : Theorem21InputsAbsorbed) : Theorem21InputsPaper := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.paper⟩⟩

/-- The refined hypothesis (absorbed part concrete) implies Theorem 2.1. -/
theorem theorem21_of_absorbed (h : Theorem21InputsAbsorbed) : Theorem21 :=
  theorem21_of_paper (theorem21InputsPaper_of_absorbed h)

/-- **Corollary 2.2** from the refined hypothesis (absorbed part concrete). -/
theorem corollary_2_2_of_absorbed (h : Theorem21InputsAbsorbed) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_absorbed h)

end
