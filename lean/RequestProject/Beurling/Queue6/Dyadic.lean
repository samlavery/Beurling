module

public import RequestProject.Beurling.Queue6.Defs6

/-!
# Dyadic scales `2^m X₀`

* `Queue6.dyadicScale_pow` : `dyadicScale X₀ (2^m X₀) = 2^m X₀`;
* `Queue6.exists_uS` : every height `s ≥ X₀` has dyadic scale `uS X₀ m` for some `m`;
* `Queue6.yq_le_absorbY` : at scale `u = 2^m X₀`, every `n ≥ max(X₀, u/2)` has
  `y(n) ≥ y(max(X₀, u/2)) = y_q(u)` (the threshold is non-decreasing across scales).
-/

@[expose] public section

open Real QueueMono AbsorbEmpty Construction CaplLink

namespace Queue6

variable {X₀ : ℕ}

lemma dyadicScale_pow (hX0 : (0 : ℝ) < X₀) (m : ℕ) :
    dyadicScale X₀ (2 ^ m * (X₀ : ℝ)) = 2 ^ m * (X₀ : ℝ) := by
  unfold dyadicScale
  rw [mul_div_assoc, div_self hX0.ne', mul_one]
  have : Int.log 2 ((2 : ℝ) ^ m) = m := by
    have := Int.log_zpow (R := ℝ) (b := 2) (by norm_num) (m : ℤ)
    simpa using this
  rw [this]; simp; ring

lemma exists_uS (hX0 : (0 : ℝ) < X₀) {s : ℝ} (hs : (X₀ : ℝ) ≤ s) :
    ∃ m : ℕ, dyadicScale X₀ s = uS X₀ m := by
  have h1 : (1 : ℝ) ≤ s / X₀ := by rw [le_div_iff₀ hX0]; linarith
  have h0 : 0 ≤ Int.log 2 (s / X₀) := by rw [Int.log_of_one_le_right _ h1]; positivity
  refine ⟨(Int.log 2 (s / X₀)).toNat, ?_⟩
  unfold dyadicScale uS
  have : (2 : ℝ) ^ Int.log 2 (s / X₀) = 2 ^ (Int.log 2 (s / X₀)).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
  rw [this]; ring

lemma uS_pos (hX0 : (0 : ℝ) < X₀) (m : ℕ) : 0 < uS X₀ m := by unfold uS; positivity

lemma X₀_le_uS (hX0 : (0 : ℝ) < X₀) (m : ℕ) : (X₀ : ℝ) ≤ uS X₀ m := by
  unfold uS
  have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  nlinarith

/-- The block below a dyadic scale is a dyadic scale. -/
lemma uq_uS (hX0 : (0 : ℝ) < X₀) (m : ℕ) : ∃ k : ℕ, uq X₀ (uS X₀ m) = 2 ^ k * (X₀ : ℝ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · refine ⟨0, ?_⟩
    unfold uq uS; rw [h]; simp
  · refine ⟨m - 1, ?_⟩
    unfold uq uS
    have e : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel h]
    rw [e]
    have : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
    rw [max_eq_right (by nlinarith)]; ring

/-- **`y_q(u) ≤ y(n)`** for `n ≥ max(X₀, u/2)`, `u = 2^m X₀`. -/
lemma yq_le_absorbY (hX : 10 ^ 8 ≤ Real.log X₀) (m : ℕ) {n : ℝ}
    (hn : uq X₀ (uS X₀ m) ≤ n) : yq X₀ (uS X₀ m) ≤ absorbY X₀ n := by
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX0 : (0 : ℝ) < X₀ := by linarith
  obtain ⟨k, hk⟩ := uq_uS hX0 m
  have hq : (X₀ : ℝ) ≤ uq X₀ (uS X₀ m) := le_max_left _ _
  unfold yq absorbY
  have h1 : uq X₀ (uS X₀ m) = dyadicScale X₀ (uq X₀ (uS X₀ m)) := by
    rw [hk, dyadicScale_pow hX0]
  have h2 : dyadicScale X₀ (uq X₀ (uS X₀ m)) ≤ dyadicScale X₀ (max X₀ n) :=
    dyadicScale_mono hX0 (by linarith) (le_max_of_le_right hn)
  rw [h1]
  exact absorbYAt_mono (Nat.cast_nonneg _) hX (by rw [← h1]; exact hq) h2

end Queue6

end
