module

public import RequestProject.Beurling.QueueBound75

/-!
# The counting inputs of Lemma 4.8(ii) from the short-interval count of `B`

In `Lemma48Pieces` (the inputs of the proof of Lemma 4.8(ii), used by Theorem 4.10) two counting
hypotheses on the residual elements `n_i` were assumed:

* a window `[n_i, n_i + 2]` holds at most `2 (n_i + 2)^η + 5` of them, and
* a dyadic block `(N, 2N]` holds at most `1.02 N` of them.

In the paper both come from one fact: for `X₀⁻ ≤ u ≤ v` the elements of `B` in `[u, v]` number
`D(v) - D(u-) + ∫_{[u,v]} T'_cont`, with `T'_cont ≤ 1.01` and `|D(x)| ≤ x^η`. Here that fact is
the single hypothesis

  `#{i : u ≤ n_i ≤ v} ≤ v^η + u^η + 1.01 (v - u) + 1`   for `X ≤ u ≤ v`

(with one unit of slack), and both counting bounds are derived from it, for `X ≥ 10⁴` and
`0 ≤ η ≤ 1/8` (`Lemma48PiecesCount.toPieces`). This gives the refined hypothesis
`Theorem21InputsCount` (with the queue bound (75) fixed as in `Theorem21InputsQueue75`), which
implies Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  GoodHeights Finset

namespace GoodHeights

/-- For `2N ≥ 10⁴` and `η ≤ 1/8`: `2 (2N)^η + 1 ≤ 0.01 N`. -/
lemma two_rpow_add_one_le {N η : ℝ} (hN : 10 ^ 4 ≤ 2 * N) (hη : η ≤ 1 / 8) :
    2 * (2 * N) ^ η + 1 ≤ 0.01 * N := by
  have h1 : (1 : ℝ) ≤ 2 * N := by linarith
  have hle : (2 * N) ^ η ≤ (2 * N) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hη
  set y := (2 * N) ^ (1 / 8 : ℝ) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by linarith) _
  have hy8 : y ^ 8 = 2 * N := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hy3 : 3 ≤ y := by
    by_contra h; push_neg at h
    have : y ^ 8 < 3 ^ 8 := pow_lt_pow_left₀ h hy0 (by norm_num)
    nlinarith
  have h7 : 3 ^ 6 * y ^ 2 ≤ y ^ 8 := by
    have : (3 : ℝ) ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ (by norm_num) hy3 6
    nlinarith [sq_nonneg y]
  nlinarith

/-- The inputs of the proof of Lemma 4.8(ii) for `f` at height `Γ`, as in `Lemma48Pieces`, with the
two counting hypotheses replaced by the short-interval count of the residual elements
(`#{i : u ≤ n_i ≤ v} ≤ v^η + u^η + 1.01 (v - u) + 1` for `X ≤ u ≤ v`) and `X ≥ 10⁴`. -/
def Lemma48PiecesCount (X₀ : ℕ) (Γ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (p : ℂ → ℂ) (w : ℝ → ℝ) (m J : ℕ) (X η M c α β : ℝ) (n : Fin m → ℝ),
    Measurable p ∧ Measurable w ∧ 10 ^ 4 ≤ X ∧ 0 ≤ η ∧ η ≤ 1 / 8 ∧ Monotone n ∧
    (∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X) ∧
    (∀ u v : ℝ, X ≤ u → u ≤ v →
      ((univ.filter (fun k => u ≤ n k ∧ n k ≤ v)).card : ℝ) ≤
        v ^ η + u ^ η + 1.01 * (v - u) + 1) ∧
    0 < M ∧ (∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), ‖p z‖ ≤ M) ∧
    0 ≤ α ∧ α ≤ β ∧ 0 < c ∧ (∀ u ∈ Set.Icc α β, |w u| ≤ c) ∧
    1 ≤ (β - α) * (Γ + 1 / 2) ∧
    (∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) +
      (p z + ∫ u in Set.Icc α β, (w u : ℂ) * cexp ((1 - z) * u))) ∧
    25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      (Real.sqrt ((Γ + 1 / 2) / 2) * M +
        2 * Real.sqrt (1 + Real.log ((β - α) * (Γ + 1 / 2))) * c * Real.exp (β / 4)) ≤
      100 * (X₀ : ℝ) ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ

/-- **The two counting bounds of Lemma 4.8(ii)** from the short-interval count. -/
theorem Lemma48PiecesCount.toPieces {X₀ : ℕ} {Γ : ℝ} {f : ℂ → ℂ}
    (h : Lemma48PiecesCount X₀ Γ f) : Lemma48Pieces X₀ Γ f := by
  obtain ⟨p, w, m, J, X, η, M, c, α, β, n, hp, hw, hX, hη0, hη, hmono, hrange, hcnt,
    hM, hpM, hα, hαβ, hc, hwc, hL, hdec, hnum⟩ := h
  refine ⟨p, w, m, J, X, η, M, c, α, β, n, hp, hw, by linarith, hη0, hη, hmono, hrange,
    ?_, ?_, hM, hpM, hα, hαβ, hc, hwc, hL, hdec, hnum⟩
  · -- windows of length 2
    intro i
    have hXi := (hrange i).1
    have h1 := hcnt (n i) (n i + 2) hXi (by linarith)
    have h2 : n i ^ η ≤ (n i + 2) ^ η :=
      Real.rpow_le_rpow (by linarith) (by linarith) hη0
    linarith
  · -- dyadic blocks
    intro N hN
    by_cases hNX : 2 * N < X
    · have : univ.filter (fun k => N < n k ∧ n k ≤ 2 * N) = ∅ := by
        apply Finset.filter_false_of_mem
        intro k _ hk
        linarith [(hrange k).1, hk.2]
      rw [this]; simp; linarith
    · push_neg at hNX
      set u := max N X
      have hsub : univ.filter (fun k => N < n k ∧ n k ≤ 2 * N) ⊆
          univ.filter (fun k => u ≤ n k ∧ n k ≤ 2 * N) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact ⟨max_le hk.1.le (hrange k).1, hk.2⟩
      have hc1 : ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
          ((univ.filter (fun k => u ≤ n k ∧ n k ≤ 2 * N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hu1 : N ≤ u := le_max_left _ _
      have hu2 : X ≤ u := le_max_right _ _
      have hu3 : u ≤ 2 * N := max_le (by linarith) hNX
      have h1 := hcnt u (2 * N) hu2 hu3
      have h2 : u ^ η ≤ (2 * N) ^ η := Real.rpow_le_rpow (by linarith) hu3 hη0
      have h3 := two_rpow_add_one_le (N := N) (by linarith) hη
      nlinarith

end GoodHeights

namespace DesignedZero

/-- **The inputs of Theorem 4.10, with the counting inputs of Lemma 4.8(ii) reduced to the
short-interval count**: as `Theorem410InputsZB48`, with `Lemma48Pieces` replaced by
`Lemma48PiecesCount`. -/
def Theorem410InputsCount (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ T κ₀ η : ℝ) (α γ xp a Γ : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    10 ^ 4 ≤ Real.log X₀ ∧ 0 < κ ∧ κ ≤ 1 ∧ Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T ∧
    (∀ k, DesignParams θ (Real.log X₀) κ₀ (α k) (γ k) (xp k)) ∧
    (∀ k, T + 1 / 2 ≤ γ k) ∧
    (∀ k, Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ k) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (Γ k) (Dlt k)) ∧
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

theorem Theorem410InputsCount.toZB48 {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsCount θ F) :
    Theorem410InputsZB48 θ F := by
  obtain ⟨X₀, κ, T, κ₀, η, α, γ, xp, a, Γ, D, Dlt, A, u, ς, hX, hκ, hκ1, hT, hP, hγT, hΓ,
    hDd, hpieces, hrule, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN, hgrowth, hdec⟩ := h
  exact ⟨X₀, κ, T, κ₀, η, α, γ, xp, a, Γ, D, Dlt, A, u, ς, hX, hκ, hκ1, hT, hP, hγT, hΓ,
    hDd, fun k => (hpieces k).toPieces, hrule, hα, hsp, hγx, hη0, hη, ha, hD, hA, hς, hN,
    hgrowth, hdec⟩

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system: Part I with the queue bound (75) fixed
(`PartIInputsQueue75`), and the inputs of Theorem 4.10 with the counting inputs reduced to the
short-interval count (`Theorem410InputsCount`). -/
def TheoremAInputsCount (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsQueue75 θ X₀ P ∧ Theorem410InputsCount θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsQueue75`, with the inputs of
Theorem 4.10 as in `Theorem410InputsCount`. -/
def Theorem21InputsCount : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsCount θ X₀ (P ω)

theorem theorem21InputsQueue75_of_count (h : Theorem21InputsCount) : Theorem21InputsQueue75 := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toZB48⟩⟩

/-- The refined hypothesis `Theorem21InputsCount` implies Theorem 2.1. -/
theorem theorem21_of_count (h : Theorem21InputsCount) : Theorem21 :=
  theorem21_of_queue75 (theorem21InputsQueue75_of_count h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsCount`. -/
theorem corollary_2_2_of_count (h : Theorem21InputsCount) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_count h)

end
