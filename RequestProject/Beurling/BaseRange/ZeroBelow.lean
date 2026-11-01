module

public import RequestProject.Beurling.BaseRange.Mu0b

/-!
# `μ₀ = μ₁ = 0` on all of `(-∞, X₀)`

The fields `hμ0`, `hμ1` of `BModel.RealMarginLoc` ask for `μ(u) = 0` for every `u < X₀`
(including `u < 0`). `Mu0b` proves it for `0 ≤ u < X₀`; this file removes `0 ≤ u`.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

variable (P : BeurlingSystem)

lemma div_lt_of_lt_X0 {X0 : ℕ} {u v : ℝ} (hv : 1 ≤ v) (hu : u < X0) : u / v < X0 := by
  rcases le_or_gt 0 u with h | h
  · exact lt_of_le_of_lt (div_le_self h hv) hu
  · have : u / v < 0 := div_neg_of_neg_of_pos h (by linarith)
    exact lt_of_lt_of_le this (Nat.cast_nonneg _)

lemma Kpt_zero_below' (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} {g : ℝ → ℝ}
    (hg : ∀ z : ℝ, z < X0 → g z = 0) {u : ℝ} (hu : u < X0) :
    KR.Sharp.Kpt P tw X0m g u = 0 := by
  classical
  unfold KR.Sharp.Kpt
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs
  · rw [hg _ (div_lt_of_lt_X0 (LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)) hu),
      zero_div]
  · rfl

/-- `μ₁ = 0` below `X₀`. -/
lemma mu1R_zero_below' (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} {u : ℝ} (hu : u < X0) :
    KR.Sharp.mu1R P tw X0m X0 u = 0 := by
  unfold KR.Sharp.mu1R
  have h1 : KshQ X0 (f1 X0 (Construction.kappaParam X0)) u = 0 := by
    unfold KshQ
    rw [Finset.Icc_eq_empty, Finset.sum_empty]
    have : ⌊u / X0⌋₊ = 0 := by
      apply Nat.floor_eq_zero.mpr
      rcases (Nat.cast_nonneg X0 : (0 : ℝ) ≤ X0).lt_or_eq with h | h
      · rw [div_lt_one h]; exact hu
      · rw [← h, div_zero]; norm_num
    omega
  have h2 : KR.Sharp.Kpt P tw X0m (KR.Sharp.f1cut X0) u = 0 :=
    Kpt_zero_below' P tw X0m (fun z hz => by unfold KR.Sharp.f1cut; rw [if_neg (not_le.mpr hz)])
      hu
  rw [h1, h2, sub_zero]

/-- `μ₀ = 0` below `X₀`. -/
lemma mu0R_zero_below' (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u : ℝ}
    (hu : u < X0) : mu0R P tw X0m X0 u = 0 := by
  unfold mu0R
  rw [mu1R_zero_below' P tw X0m hu, muEdge_zero_below hX hu,
    Kpt_zero_below' P tw X0m (fun z hz => by unfold MAPcut; rw [if_neg (not_le.mpr hz)]) hu]
  simp [srcBase, MAPcut, not_le.mpr hu]

end BaseRange
