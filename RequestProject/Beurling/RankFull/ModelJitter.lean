module

public import RequestProject.Beurling.RankFull.PILOneRun
public import RequestProject.Beurling.RankFull.ModelCap

/-!
# `SkeletonBound` for the window model over a jitter process

The window model over `J : JitterLaw` (`dec ω = decOf J ω = {n | ω ∈ A n}`, `q ω = qOf J ω`).
`SkeletonBound` (Lemma A.5 + Theorem A.10 with `C = B'`) splits by run structure:
* one run, `l = [k]`: **proved** (`skeletonBound_oneRun`);
* several runs, `l ≠ [k]`: the named hypothesis `MultiRunSkeletonBound`, exactly the
  statement of `SkeletonBound` restricted to these run structures.

`RankFull.Config.skeletonBound_jitter` assembles them; it is the input `hbound` of
`prop_6_11_window` for `dec = decOf J`, `q = qOf J`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Lemma A.5 + Theorem A.10 (`C = B'`) for the run structures with at least two runs**: the
part of `SkeletonBound` not yet proved. -/
def MultiRunSkeletonBound (P : Measure Ω) (Good : Set Ω) (k : ℕ) (θ δ A Eu : ℝ)
    (τ : Fin k → ℝ) (X : Matrix (Fin k) (Fin k) ℕ → List ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ E ∈ InvPattern k, ∀ l ∈ comps k, l ≠ [k] →
    ∫⁻ ω in Good, X E l ω ∂P ≤
      ENNReal.ofReal (θ ^ k * δ ^ k * patternWeight τ E * finG A l Eu)

lemma one_le_tauSlot {H : ℝ → ℝ} {X₀ : ℝ} (hH : SlotHyp H X₀) (j : ℕ) :
    1 ≤ tauSlot H X₀ j := by
  unfold tauSlot
  refine le_trans ?_ (le_max_left _ _)
  have h1 := hH.hX₀
  have h2 := hH.hHsmall
  linarith

/-- **`SkeletonBound` for the window model over a jitter process**: the one-run part is
`skeletonBound_oneRun`; the multi-run part is `MultiRunSkeletonBound`. -/
theorem skeletonBound_jitter {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) {r₀ : ℕ}
    (hr0 : 1 ≤ r₀) (τ : Fin r₀ → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ)
    (X₀ D Dmax : ℕ) {A Eu : ℝ} (hA : 0 ≤ A) (hEuA : Eu ≤ A)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r₀,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → tailSum Dmax X₀ *
      ∏ n ∈ univ.filter (fun n : Fin N => ω ∈ J.A n ∧ (n : ℕ) < u), (1 - (J.q n ω)⁻¹)⁻¹ ≤ A)
    (hmulti : MultiRunSkeletonBound P Good r₀ θ δ A Eu τ
      (fun E l ω => skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E l)) :
    SkeletonBound P Good r₀ θ δ A Eu τ
      (fun E l ω => skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E l) := by
  obtain ⟨k, rfl⟩ : ∃ k, r₀ = k + 1 := ⟨r₀ - 1, by omega⟩
  intro E hE l hl
  by_cases h1 : l = [k + 1]
  · subst h1
    exact skeletonBound_oneRun J hθ0 hθ hGood G hGm hG smax hGoodG τ hτ1 hJw hJ hδ D Dmax X₀
      hA hEuA hq hsmax hτ hS3 E hE
  · exact hmulti E hE l hl h1

end RankFull.Config
