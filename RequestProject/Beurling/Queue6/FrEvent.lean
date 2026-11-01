module

public import RequestProject.Beurling.Queue6.Freedman6

/-!
# The event `Fr(I)` and Theorem 6.6(i), for abstract adapted counts

For a physical window `I ∈ 𝓘_x` the proof of Theorem 6.6(i) uses, in slot order `k` (the prime
decided at relative slot `k + 1`):

* `Xt k` : the truncated count `X̃_q(I) = min(X⁽¹⁾_q(I), 2M₁) ∈ [0, 2M₁]`, `ℱ_{k+1}`-measurable;
* `Ind2 k` : the indicator of `X⁽²⁾_q(I) ≥ 1`, `ℱ_{k+1}`-measurable;
* `ℓI` : the random integer `ℓ_jit(I)`.

`Queue6.FrEvent` is the event `Fr(I)` of §6.3 ((a) for `ℓ_jit(I) ≤ K`, `K = K₀ + 5`, with
`v_ℓ = 2M₁(ℓ + K_d)`, `K_d = 3`, and (b)), with `λ` arbitrary (`λ = 4L` in the paper).

`Queue6.frEvent_fail` (**Theorem 6.6(i)**, one window): if, almost surely on a set `G` (the good
event `Good(< t(I))`), R1′ bounds the compensator, `∑_k E[X̃_k | ℱ_k] ≤ ℓ_jit(I)(1 - c'/L) + K_d`,
and the `q²`-compensator is at most `1` (Corollary 5.40 with `s₂|I| ≤ 1`), then
`P(Fr(I)ᶜ ∩ G) ≤ (K + 2) e^{-λ}` for `λ ≥ 30`. The paper states `(K₀ + 7) e^{-λ}`, which is
the same bound with `K = K₀ + 5`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

namespace Queue6

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- **The event `Fr(I)`** (§6.3): (a) if `ℓ_jit(I) ≤ K`, then
`∑_{k<N} (X̃_k - E[X̃_k | ℱ_k]) ≤ √(2 v_ℓ λ) + (4/3) M₁ λ` with `v_ℓ = 2M₁(ℓ + 3)`; and
(b) `#{q : X⁽²⁾_q(I) ≥ 1} ≤ λ`. -/
def FrEvent (ℱ : Filtration ℕ m0) (μ : Measure Ω) (Xt Ind2 : ℕ → Ω → ℝ) (ℓI : Ω → ℕ)
    (M1 l : ℝ) (K N : ℕ) : Set Ω :=
  {ω | (ℓI ω ≤ K → ∑ k ∈ range N, (Xt k ω - (μ[Xt k | ℱ k]) ω) <
      Real.sqrt (2 * (2 * M1 * (ℓI ω + 3)) * l) + 4 / 3 * M1 * l) ∧
    ∑ k ∈ range N, Ind2 k ω ≤ l}

/-- `1 + √(2λ) + 2λ/3 < λ` for `λ ≥ 30`. -/
lemma count_slack {l : ℝ} (hl : 30 ≤ l) : 1 + (Real.sqrt (2 * 1 * l) + 2 * l / 3) < l := by
  have hs : Real.sqrt (2 * 1 * l) ≤ l / 3 - 1.1 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

/-- **Theorem 6.6(i) for one window.** -/
theorem frEvent_fail {Xt Ind2 : ℕ → Ω → ℝ} {M1 l L : ℝ} (hM : 0 < M1) (hl : 30 ≤ l)
    (hL : 0 < L) (hX0 : ∀ k ω, 0 ≤ Xt k ω) (hXb : ∀ k ω, Xt k ω ≤ 2 * M1)
    (hXm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Xt k))
    (hI0 : ∀ k ω, 0 ≤ Ind2 k ω) (hI1 : ∀ k ω, Ind2 k ω ≤ 1)
    (hIm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Ind2 k)) (ℓI : Ω → ℕ) (K N : ℕ) (G : Set Ω)
    (hR1 : ∀ᵐ ω ∂μ, ω ∈ G →
      ∑ k ∈ range N, (μ[Xt k | ℱ k]) ω ≤ ℓI ω * (1 - 0.15 / L) + 3)
    (hcomp2 : ∀ᵐ ω ∂μ, ω ∈ G → ∑ k ∈ range N, (μ[Ind2 k | ℱ k]) ω ≤ 1) :
    μ ((FrEvent ℱ μ Xt Ind2 ℓI M1 l K N)ᶜ ∩ G) ≤ ENNReal.ofReal ((K + 2) * Real.exp (-l)) := by
  have hl0 : 0 < l := by linarith
  have hb : 0 < 2 * M1 := by linarith
  set v : ℕ → ℝ := fun j => 2 * M1 * (j + 3)
  have hv : ∀ j, 0 < v j := fun j => by simp only [v]; positivity
  have hA := freedman_peel (μ := μ) (ℱ := ℱ) hb hX0 hXb hXm hl0 N K ℓI v hv G (fun j _ => by
    filter_upwards [hR1] with ω h hωG hℓ
    refine (h hωG).trans ?_
    rw [hℓ]
    have e : v j / (2 * M1) = j + 3 := by simp only [v]; field_simp
    rw [e]
    have : (0 : ℝ) ≤ j * (0.15 / L) := by positivity
    nlinarith)
  have hB := count_good (μ := μ) (ℱ := ℱ) hI0 hI1 hIm one_pos hl0 N G hcomp2
  have hsub : (FrEvent ℱ μ Xt Ind2 ℓI M1 l K N)ᶜ ∩ G ⊆
      ({ω | ℓI ω ≤ K ∧ Real.sqrt (2 * v (ℓI ω) * l) + 2 * (2 * M1) * l / 3 ≤
        ∑ k ∈ range N, (Xt k ω - (μ[Xt k | ℱ k]) ω)} ∩ G) ∪
      ({ω | 1 + (Real.sqrt (2 * 1 * l) + 2 * l / 3) ≤ ∑ k ∈ range N, Ind2 k ω} ∩ G) := by
    rintro ω ⟨hω, hG⟩
    simp only [FrEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, Classical.not_imp,
      not_le] at hω
    rcases hω with ⟨hK, hS⟩ | hS
    · left
      refine ⟨⟨hK, ?_⟩, hG⟩
      have e : 2 * (2 * M1) * l / 3 = 4 / 3 * M1 * l := by ring
      simp only [v]
      rw [e]; exact not_lt.mp hS
    · right
      exact ⟨le_of_lt (lt_trans (count_slack hl) hS), hG⟩
  calc μ ((FrEvent ℱ μ Xt Ind2 ℓI M1 l K N)ᶜ ∩ G)
      ≤ ENNReal.ofReal ((K + 1) * Real.exp (-l)) + ENNReal.ofReal (Real.exp (-l)) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hA hB))
    _ = ENNReal.ofReal ((K + 2) * Real.exp (-l)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **The event `Fr(I)`, all partial sums**: (a) if `ℓ_jit(I) ≤ K`, every partial centred sum is
`< √(2 v_ℓ λ) + (4/3) M₁ λ`; (b) every partial count of `{X⁽²⁾_q ≥ 1}` is `≤ λ`. -/
def FrAll (ℱ : Filtration ℕ m0) (μ : Measure Ω) (Xt Ind2 : ℕ → Ω → ℝ) (ℓI : Ω → ℕ)
    (M1 l : ℝ) (K : ℕ) : Set Ω :=
  {ω | (ℓI ω ≤ K → ∀ n, ∑ k ∈ range n, (Xt k ω - (μ[Xt k | ℱ k]) ω) <
      Real.sqrt (2 * (2 * M1 * (ℓI ω + 3)) * l) + 4 / 3 * M1 * l) ∧
    ∀ n, ∑ k ∈ range n, Ind2 k ω ≤ l}

/-- **Theorem 6.6(i) for one window**, all partial sums. -/
theorem frAll_fail {Xt Ind2 : ℕ → Ω → ℝ} {M1 l L : ℝ} (hM : 0 < M1) (hl : 30 ≤ l)
    (hL : 0 < L) (hX0 : ∀ k ω, 0 ≤ Xt k ω) (hXb : ∀ k ω, Xt k ω ≤ 2 * M1)
    (hXm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Xt k))
    (hI0 : ∀ k ω, 0 ≤ Ind2 k ω) (hI1 : ∀ k ω, Ind2 k ω ≤ 1)
    (hIm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Ind2 k)) (ℓI : Ω → ℕ) (K : ℕ) (G : Set Ω)
    (hR1 : ∀ᵐ ω ∂μ, ω ∈ G →
      ∀ n, ∑ k ∈ range n, (μ[Xt k | ℱ k]) ω ≤ ℓI ω * (1 - 0.15 / L) + 3)
    (hcomp2 : ∀ᵐ ω ∂μ, ω ∈ G → ∀ n, ∑ k ∈ range n, (μ[Ind2 k | ℱ k]) ω ≤ 1) :
    μ ((FrAll ℱ μ Xt Ind2 ℓI M1 l K)ᶜ ∩ G) ≤ ENNReal.ofReal ((K + 2) * Real.exp (-l)) := by
  have hl0 : 0 < l := by linarith
  have hb : 0 < 2 * M1 := by linarith
  set v : ℕ → ℝ := fun j => 2 * M1 * (j + 3)
  have hv : ∀ j, 0 < v j := fun j => by simp only [v]; positivity
  have hA := freedman_peel_all (μ := μ) (ℱ := ℱ) hb hX0 hXb hXm hl0 K ℓI v hv G (fun j _ => by
    filter_upwards [hR1] with ω h hωG hℓ n
    refine (h hωG n).trans ?_
    rw [hℓ]
    have e : v j / (2 * M1) = j + 3 := by simp only [v]; field_simp
    rw [e]
    have : (0 : ℝ) ≤ j * (0.15 / L) := by positivity
    nlinarith)
  have hB := count_good_all (μ := μ) (ℱ := ℱ) hI0 hI1 hIm one_pos hl0 G hcomp2
  have hsub : (FrAll ℱ μ Xt Ind2 ℓI M1 l K)ᶜ ∩ G ⊆
      ({ω | ℓI ω ≤ K ∧ ∃ n, Real.sqrt (2 * v (ℓI ω) * l) + 2 * (2 * M1) * l / 3 ≤
        ∑ k ∈ range n, (Xt k ω - (μ[Xt k | ℱ k]) ω)} ∩ G) ∪
      ({ω | ∃ n, 1 + (Real.sqrt (2 * 1 * l) + 2 * l / 3) ≤ ∑ k ∈ range n, Ind2 k ω} ∩ G) := by
    rintro ω ⟨hω, hG⟩
    simp only [FrAll, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, Classical.not_imp,
      not_forall, not_lt, not_le] at hω
    rcases hω with ⟨hK, n, hS⟩ | ⟨n, hS⟩
    · left
      refine ⟨⟨hK, n, ?_⟩, hG⟩
      have e : 2 * (2 * M1) * l / 3 = 4 / 3 * M1 * l := by ring
      simp only [v]
      rw [e]; exact hS
    · right
      exact ⟨⟨n, le_of_lt (lt_trans (count_slack hl) hS)⟩, hG⟩
  calc μ ((FrAll ℱ μ Xt Ind2 ℓI M1 l K)ᶜ ∩ G)
      ≤ ENNReal.ofReal ((K + 1) * Real.exp (-l)) + ENNReal.ofReal (Real.exp (-l)) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hA hB))
    _ = ENNReal.ofReal ((K + 2) * Real.exp (-l)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end Queue6

end
