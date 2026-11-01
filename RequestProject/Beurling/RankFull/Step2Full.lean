module

public import RequestProject.Beurling.RankFull.Step2Link
public import RequestProject.Beurling.RankFull.TypeUnionFormal
public import RequestProject.Beurling.RankFull.RowAdm

/-!
# Theorem 6.23(a), range of Step 2, from the skeleton inputs

`RankFull.theorem_6_23a_step2_full` combines `theorem_6_23a_step2` with
`typeUnionBound_of_cover` (Lemma 6.21(ii)), the (s4) data of a row of `R` being `admHigh`
(monomials of degree in `[D* + 1, D]` in `π = r₀ D` labels, with the label values `τ_j ≥ X₀⁻`, and
tails), whose count is bounded by Lemma 6.22(a)+(b) (`card_admHigh_le`). The remaining inputs are
`ConfigSkeletonReduction` and `CoverSkeletonBound` for every skeleton, and the parameter bounds of
`typeUnionBound_of_cover`.
-/

@[expose] public section

open Finset MeasureTheory BSCert.Capl
open scoped ENNReal

namespace RankFull

/-- **Theorem 6.23(a) for `-log Λ ≤ s ≤ s_H + 1`**, from the reduction to skeletons and the
Cover Bound inputs. -/
theorem theorem_6_23a_step2_full {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Good : Set Ω} (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ}
    (S : ι → Ω → Finset (Fin m → ℕ)) (h0 : ∀ J ω, 0 ∉ S J ω) {sH Λ s Xm : ℝ}
    (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746) (hval : gstar sH = gTarget)
    (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs2 : s ≤ sH + 1) {r₀ D : ℕ} (hr0 : 1 ≤ r₀)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log Λ + s) / Λ)
    (hD : ∀ J ω, ∀ v ∈ S J ω, Covers.deg v ≤ D) (hXm0 : 0 < Xm)
    (hXm : Λ - Real.exp (-0.98 * Λ) ≤ Real.log Xm)
    (τl : Fin (r₀ * D) → ℝ) (hτl : ∀ i, Xm ≤ τl i)
    {Ch B lam Atop Eu : ℝ} (τ : (r : ℕ) → Fin r → ℝ) (hτ : ∀ r, ∀ i, 1 < τ r i)
    (hlam0 : 0 ≤ lam) (hrlam : 1 + r₀ * lam ≤ Real.exp (2 * Real.log Λ + s))
    (hCh : Ch ≤ 2 * Real.exp (2 * Real.log Λ + s))
    (hBτ : ∀ r < r₀, ∏ i, (1 - (τ r i)⁻¹)⁻¹ ≤ B)
    (hB : B ≤ 2.1 * Real.exp (2 * Real.log Λ + s) ^ (1.02 : ℝ))
    (hEu : 0 < Eu) (hEuA : Eu ≤ Atop) (hACh : Atop ≤ Ch) (hlam : Real.log (Atop / Eu) ≤ lam)
    (hW : (W.card : ℝ) ≤ 2 * Real.exp (Real.exp (2 * Real.log Λ + s)) /
      (4 * Real.exp (2 * Real.log Λ + s) ^ (-6 : ℝ)) + 1)
    (hmeas : ∀ J ∈ W, Measurable fun ω =>
      (configCount r₀ (j2 (logc sH Λ s) (A Λ s)) (k2 (logc sH Λ s) (A Λ s)) (S J ω) : ℝ≥0∞))
    (X : ι → (r : ℕ) → (C : Finset (Fin r)) → Finset (Fin (C.card * D)) →
      (Fin r → Fin r → ℕ) → (Fin r → (Fin (r₀ * D) → ℕ) × ℕ) → Ω → ℝ≥0∞)
    (hXm' : ∀ J r C lab ex s4, Measurable (X J r C lab ex s4))
    (hred : ConfigSkeletonReduction W S r₀ (j2 (logc sH Λ s) (A Λ s))
      (k2 (logc sH Λ s) (A Λ s)) D
      (admHigh (r₀ * D) (k2 (logc sH Λ s) (A Λ s) + 1) D τl
        (2 * Real.exp (Real.exp (2 * Real.log Λ + s)) + 1)) (0, 0) X)
    (hcov : ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r (j2 (logc sH Λ s) (A Λ s)), ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r (1 + 1 / Λ) (4 * Real.exp (2 * Real.log Λ + s) ^ (-6 : ℝ))
          Atop Eu (Real.exp (Real.exp (2 * Real.log Λ + s))) (τ r) (exExcess ex) (r - C.card) l
          (X J r C lab ex s4)) :
    P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi (Real.exp (logc sH Λ s)) (Real.exp (logc sH Λ s / 2)) r₀ ≤
        (S J ω).card} ∩ Good) ≤
      ENNReal.ofReal (Real.exp (2 * Real.log Λ + s) ^ (-3 : ℝ)) := by
  set L := Real.exp (2 * Real.log Λ + s) with hL
  obtain ⟨hL60, hr0L, -, -, -, hmain⟩ :=
    step2_params hsH hval hΛ hs hs2 hr0 hr₀ hDle (le_refl (r₀ * D)) hXm0 hXm
  refine theorem_6_23a_step2 P hGood W S h0 hsH hval hΛ hs hs2 hr0 hr₀ hDle hD
    (le_refl (r₀ * D)) hXm0 hXm hmeas fun hDk => ?_
  obtain ⟨-, hw1, hcond⟩ := hmain hDk
  have hk1 : 1 ≤ k2 (logc sH Λ s) (A Λ s) + 1 := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hDL : (D : ℝ) ≤ L := by
    have : 2 * L / Λ ≤ L := by
      rw [div_le_iff₀ hΛ0]; nlinarith [Real.exp_pos (2 * Real.log Λ + s)]
    linarith
  have hz2 : 2 ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hadm := card_admHigh_le (K := D) hk1 hXm0 hz2 hcond hτl
  refine typeUnionBound_of_cover P Good W S _ (0, 0) τ hτ hL60 (by norm_num; linarith) hDL hr0L
    hlam0 hrlam hCh hBτ hB (wHigh_pos hk1 hXm0) hw1 ?_ hEu hEuA hACh hlam hW X hXm' hred hcov
  unfold wHigh
  push_cast at hadm ⊢
  exact hadm

end RankFull
