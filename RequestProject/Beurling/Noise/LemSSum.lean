module

public import Mathlib

/-!
# Elementary sums for Lemma 5.21(iii)

* `sum_le_shift` : a sum over a finite set of naturals `≥ k₀` is at most the sum over
  `k₀, k₀ + 1, …` (non-negative terms);
* `sum_geom_le`, `sum_mul_geom_le` : `∑_{m<M} q^m ≤ 1/(1-q)`, `∑_{m<M} m q^m ≤ q/(1-q)²`;
* `sum_inv_sq_le` : `∑_{m<M} (a + m b)^{-2} ≤ a^{-2} + (ab)^{-1}`;
* `one_sub_exp_neg_ge` : `1 - e^{-t} ≥ t/(1+t)`.
-/

@[expose] public section

open Finset Real

namespace LemS

lemma sum_le_shift (K : Finset ℕ) (k0 M : ℕ) (hK : ∀ k ∈ K, k0 ≤ k ∧ k < k0 + M)
    (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ k ∈ K, F k ≤ ∑ m ∈ Finset.range M, F (k0 + m) := by
  rw [← Finset.sum_image (f := F) (s := Finset.range M) (g := fun m => k0 + m)
    (fun a _ b _ h => by simpa using h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨h1, h2⟩ := hK k hk
    rw [Finset.mem_image]
    exact ⟨k - k0, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _ _; exact hF k

lemma sum_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, q ^ m ≤ 1 / (1 - q) := by
  rw [geom_sum_eq hq1.ne]
  have : 0 ≤ q ^ M := pow_nonneg hq0 M
  rw [show q ^ M - 1 = -(1 - q ^ M) by ring, show q - 1 = -(1 - q) by ring, neg_div_neg_eq]
  apply div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma sum_mul_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m ≤ q / (1 - q) ^ 2 := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hs : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hn
    simpa using this
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hn]
  exact hs.sum_le_tsum _ (fun i _ => by positivity)

lemma sum_inv_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (M : ℕ) :
    ∑ m ∈ Finset.range M, 1 / (a + m * b) ^ 2 ≤ 1 / a ^ 2 + 1 / (a * b) := by
  -- `∑_{m < M+1} ≤ 1/a² + (1/b)(1/a - 1/(a + M b))`
  have key : ∀ M : ℕ, ∑ m ∈ Finset.range (M + 1), 1 / (a + m * b) ^ 2 ≤
      1 / a ^ 2 + (1 / b) * (1 / a - 1 / (a + M * b)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hM : 0 < a + M * b := by positivity
      have hM1 : 0 < a + ((M + 1 : ℕ) : ℝ) * b := by positivity
      have hstep : 1 / (a + ((M + 1 : ℕ) : ℝ) * b) ^ 2 ≤
          (1 / b) * (1 / (a + M * b) - 1 / (a + ((M + 1 : ℕ) : ℝ) * b)) := by
        have e : 1 / (a + M * b) - 1 / (a + ((M + 1 : ℕ) : ℝ) * b) =
            b / ((a + M * b) * (a + ((M + 1 : ℕ) : ℝ) * b)) := by
          push_cast; field_simp; ring
        rw [e, one_div_mul_eq_div]
        have e2 : b / ((a + M * b) * (a + ((M + 1 : ℕ) : ℝ) * b)) / b =
            1 / ((a + M * b) * (a + ((M + 1 : ℕ) : ℝ) * b)) := by field_simp
        rw [e2]
        apply one_div_le_one_div_of_le (by positivity)
        rw [sq]
        apply mul_le_mul_of_nonneg_right _ hM1.le
        push_cast; nlinarith
      linarith
  rcases M with _ | M
  · simp; positivity
  · refine (key M).trans ?_
    have : 0 ≤ 1 / (a + M * b) := by positivity
    have e : (1 / b) * (1 / a) = 1 / (a * b) := by field_simp
    have h2 : (1 / b) * (1 / a - 1 / (a + M * b)) ≤ (1 / b) * (1 / a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

lemma one_sub_exp_neg_ge {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have h := Real.add_one_le_exp t
  have hp := Real.exp_pos t
  rw [Real.exp_neg, div_le_iff₀ (by linarith)]
  have : (Real.exp t)⁻¹ * Real.exp t = 1 := inv_mul_cancel₀ hp.ne'
  nlinarith [inv_pos.mpr hp]

end LemS

end
