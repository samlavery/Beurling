module

public import RequestProject.Beurling.RankFull.Step34Link
public import RequestProject.Beurling.RankFull.TypeUnionFormal

/-!
# Theorem 6.23(a) at every scale `s ≥ -log Λ`

`RankFull.theorem_6_23a_all` : **Theorem 6.23(a)** for every `Λ = log X₀ ≥ 10⁸` and every
`s ≥ -log Λ` (`ℓ = 2 log Λ + s`, `L = e^ℓ`, `z = e^L`, `c = e^{log c}`, `Q = c^{1/2}`): the
probability, on `Good`, that some window `J ∈ W` has `rank S(J) < r₀` and
`|S(J)| ≥ r₀ + φ(r₀)` is at most `L^{-3}`.

The proof splits into the three ranges of the paper (Step 2: `s ≤ s_H + 1`; Step 3:
`s > s_H + 1`, `ℓ ≤ 0.3Λ`; Step 4 (T2): `ℓ ≥ 0.3Λ`), and discharges `TypeUnionBound` in each by
`typeUnionBound_of_cover` (Lemma 6.21(ii)) with the (s4) data `admGen` of the rows of `R` and
their counts (Lemma 6.22(b), (d), (e)).

The remaining inputs are the reduction to skeletons `ConfigSkeletonReduction` (for all `j, k`;
the (s4) data of a row of `R` of degree `≥ k + 1` lie in `admGen`) and `CoverSkeletonBound` for
every skeleton (Lemma A.5 + Theorem A.10 with the cover; the join list `l` with `∑ l = κ`,
`#{t : j_t = 0} ≤ |R|`), plus the parameter bounds of `typeUnionBound_of_cover`.
-/

@[expose] public section

open Finset MeasureTheory BSCert.Capl
open scoped ENNReal

namespace RankFull

set_option maxHeartbeats 4000000 in
/-- **Theorem 6.23(a)** at every scale. -/
theorem theorem_6_23a_all {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ))
    (h0 : ∀ J ω, 0 ∉ S J ω) {X₀ : ℕ} (hΛ : 10 ^ 8 ≤ Real.log X₀) {sH s Xm : ℝ}
    (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746) (hval : gstar sH = gTarget)
    (hs : -Real.log (Real.log X₀) ≤ s) {r₀ D : ℕ} (hr0 : 1 ≤ r₀) (hD1 : 1 ≤ D)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * (2 * Real.log (Real.log X₀) + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s) / Real.log X₀)
    (hD : ∀ J ω, ∀ v ∈ S J ω, Covers.deg v ≤ D) (hXm0 : 0 < Xm)
    (hXmlo : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log Xm)
    (hXmhi : Real.log Xm ≤ Real.log X₀)
    (τl : Fin (r₀ * D) → ℝ) (hτlXm : ∀ i, Xm ≤ τl i)
    (hτi : ∀ i : Fin (r₀ * D), (((i : ℕ) : ℝ) + 1) / 2 ≤ τl i)
    {Ch B lam Atop Eu : ℝ} (τ : (r : ℕ) → Fin r → ℝ) (hτ : ∀ r, ∀ i, 1 < τ r i)
    (hlam0 : 0 ≤ lam) (hrlam : 1 + r₀ * lam ≤ Real.exp (2 * Real.log (Real.log X₀) + s))
    (hCh : Ch ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s))
    (hBτ : ∀ r < r₀, ∏ i, (1 - (τ r i)⁻¹)⁻¹ ≤ B)
    (hB : B ≤ 2.1 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (1.02 : ℝ))
    (hEu : 0 < Eu) (hEuA : Eu ≤ Atop) (hACh : Atop ≤ Ch) (hlam : Real.log (Atop / Eu) ≤ lam)
    (hW : (W.card : ℝ) ≤ 2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s)) /
      (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) + 1)
    (hmeas : ∀ j k, ∀ J ∈ W, Measurable fun ω => (configCount r₀ j k (S J ω) : ℝ≥0∞))
    (X : ι → (r : ℕ) → (C : Finset (Fin r)) → Finset (Fin (C.card * D)) →
      (Fin r → Fin r → ℕ) → (Fin r → (Fin (r₀ * D) → ℕ) × ℕ) → Ω → ℝ≥0∞)
    (hXm' : ∀ J r C lab ex s4, Measurable (X J r C lab ex s4))
    (hred : ∀ j k, ConfigSkeletonReduction W S r₀ j k D
      (admGen (r₀ * D) (k + 1) D X₀ τl (2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s))
        + 1)) (0, 0) X)
    (hcov : ∀ j, ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r (1 + 1 / Real.log X₀)
          (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) Atop Eu
          (Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s))) (τ r) (exExcess ex)
          (r - C.card) l (X J r C lab ex s4)) :
    P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi (Real.exp (logc sH (Real.log X₀) s))
        (Real.exp (logc sH (Real.log X₀) s / 2)) r₀ ≤ (S J ω).card} ∩ Good) ≤
      ENNReal.ofReal (Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-3 : ℝ)) := by
  set Λ := Real.log X₀ with hΛdef
  set L := Real.exp (2 * Real.log Λ + s) with hL
  set z := Real.exp L with hz
  set X' := logc sH Λ s with hX'
  have hΛ8 : (100000000 : ℝ) ≤ Λ := by norm_num at hΛ ⊢; linarith
  have hΛ0 : 0 < Λ := by linarith
  have hDL : ∀ {LL : ℝ}, 60 ≤ LL → (D : ℝ) ≤ 2 * LL / Λ → (D : ℝ) ≤ LL := by
    intro LL hLL h
    have : 2 * LL / Λ ≤ LL := by rw [div_le_iff₀ hΛ0]; nlinarith
    linarith
  have hXm3 : 3 ≤ Xm := by
    rw [← Real.exp_log hXm0]
    have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num); linarith
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log Xm) := Real.exp_le_exp.mpr (by linarith)
  have hτ3 : ∀ i, 3 ≤ τl i := fun i => hXm3.trans (hτlXm i)
  rcases le_or_gt s (sH + 1) with hs2 | hs2
  · -- Step 2
    obtain ⟨hL60, hr0L, -, -, -, hmain⟩ :=
      step2_params hsH hval hΛ8 hs hs2 hr0 hr₀ hDle (le_refl (r₀ * D)) hXm0 hXmlo
    refine theorem_6_23a_step2 P hGood W S h0 hsH hval hΛ8 hs hs2 hr0 hr₀ hDle hD
      (le_refl (r₀ * D)) hXm0 hXmlo (hmeas _ _) fun hDk => ?_
    obtain ⟨-, hw1, hcond⟩ := hmain hDk
    have hk1 : 1 ≤ k2 (logc sH Λ s) (A Λ s) + 1 := by omega
    have hz2 : 2 ≤ z := by have := Real.add_one_le_exp L; linarith
    have hadm1 := card_admHigh_le (K := D) hk1 hXm0 hz2 hcond hτlXm
    have hadm : ((admGen (r₀ * D) (k2 (logc sH Λ s) (A Λ s) + 1) D X₀ τl
        (2 * z + 1)).card : ℝ) ≤ z * wHigh (r₀ * D) (k2 (logc sH Λ s) (A Λ s) + 1) Xm := by
      refine le_trans ?_ (by unfold wHigh; push_cast at hadm1 ⊢; exact hadm1)
      exact_mod_cast Finset.card_le_card (admGen_subset_admHigh _ _ _ _ _ _)
    exact typeUnionBound_of_cover P Good W S _ (0, 0) τ hτ hL60 hΛ (hDL hL60 hDle) hr0L
      hlam0 hrlam hCh hBτ hB (wHigh_pos hk1 hXm0) hw1 hadm hEu hEuA hACh hlam hW X hXm'
      (hred _ _) (hcov _)
  rcases le_or_gt (2 * Real.log Λ + s) (0.3 * Λ) with hl | hl
  · -- Step 3
    obtain ⟨hL60, hr0L, hc, h80, hw0, hw1, hadm⟩ :=
      step3_params hΛ hsH.1.le hs2 hl hr0 hD1 hr₀ hDle hXm0 hXmlo hXmhi τl hτlXm
    refine theorem_6_23a P hGood W S h0 hD (k := 0) (Q := Real.exp (X' / 2))
      (Real.exp_pos _).le hL60 hr0L hw0 hc (fun J ω V _ _ => hlow_zero (h0 J ω)
        (Real.exp_pos _).le V) (hmeas _ _) ?_ h80
    exact typeUnionBound_of_cover P Good W S _ (0, 0) τ hτ hL60 hΛ (hDL hL60 hDle) hr0L
      hlam0 hrlam hCh hBτ hB hw0 hw1 hadm hEu hEuA hACh hlam hW X hXm' (hred _ 0) (hcov _)
  · -- Step 4 (T2)
    obtain ⟨hL60, hr0L, hc, h80, hw0, hw1, hadm⟩ :=
      T2_params (sH := sH) hΛ hl.le hr₀ hDle τl hτ3 hτi
    refine theorem_6_23a P hGood W S h0 hD (k := 0) (Q := Real.exp (X' / 2))
      (Real.exp_pos _).le hL60 hr0L hw0 hc (fun J ω V _ _ => hlow_zero (h0 J ω)
        (Real.exp_pos _).le V) (hmeas _ _) ?_ h80
    exact typeUnionBound_of_cover P Good W S _ (0, 0) τ hτ hL60 hΛ (hDL hL60 hDle) hr0L
      hlam0 hrlam hCh hBτ hB hw0 hw1 hadm hEu hEuA hACh hlam hW X hXm' (hred _ 0) (hcov _)

end RankFull
