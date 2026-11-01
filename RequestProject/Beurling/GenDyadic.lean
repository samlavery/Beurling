module

public import Mathlib

/-!
# Dyadic blocks

* `GenDyadic.dIdx a` : for `a > 1`, the index `m` with `2^m < a ≤ 2^{m+1}` (`dIdx_spec`);
* `GenDyadic.sum_le_blocks` : a sum `∑ w_i g_i` split along the dyadic blocks of the points
  `a_i`, bounded by `∑_m B_m G_m` when the block weights are `≤ B_m` and `g ≤ G_m` on block `m`;
* `GenDyadic.sum_half_pow_le` : `∑_{m ∈ K} 2^{-m} ≤ 2 · 2^{-m₀}` if `K ⊆ [m₀, ∞)`.
-/

@[expose] public section

open Finset

namespace GenDyadic

/-- The dyadic index of `a`: for `a > 1` it is the `m` with `2^m < a ≤ 2^{m+1}`. -/
noncomputable def dIdx (a : ℝ) : ℕ := Nat.clog 2 ⌈a⌉₊ - 1

lemma dIdx_spec {a : ℝ} (ha : 1 < a) :
    (2 : ℝ) ^ dIdx a < a ∧ a ≤ 2 ^ (dIdx a + 1) := by
  have hc1 : 1 < ⌈a⌉₊ := by
    have : (1 : ℝ) < ⌈a⌉₊ := lt_of_lt_of_le ha (Nat.le_ceil a)
    exact_mod_cast this
  have hpos : 1 ≤ Nat.clog 2 ⌈a⌉₊ := by
    by_contra h; push_neg at h
    have h0 : Nat.clog 2 ⌈a⌉₊ = 0 := by omega
    have := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈a⌉₊
    rw [h0] at this; omega
  have e : dIdx a + 1 = Nat.clog 2 ⌈a⌉₊ := by unfold dIdx; omega
  constructor
  · have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hc1
    have h' : Nat.pred (Nat.clog 2 ⌈a⌉₊) = dIdx a := by unfold dIdx; exact Nat.pred_eq_sub_one
    rw [h'] at h
    have : ((2 ^ dIdx a : ℕ) : ℝ) < a := Nat.lt_ceil.mp h
    exact_mod_cast this
  · rw [e]
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈a⌉₊
    have : a ≤ ((2 ^ Nat.clog 2 ⌈a⌉₊ : ℕ) : ℝ) := Nat.ceil_le.mp h
    exact_mod_cast this

/-- **Dyadic block bound.** If on every dyadic block `m` (of the points `a_i > 1`) the weights
sum to at most `B m`, and `g_i ≤ G m` on block `m` with `G m ≥ 0`, then
`∑ w_i g_i ≤ ∑_m B m · G m` (sum over the blocks that occur). -/
theorem sum_le_blocks {ι : Type*} (s : Finset ι) (a w g : ι → ℝ) (B G : ℕ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : ∀ m ∈ s.image (fun i => dIdx (a i)),
      ∑ i ∈ s.filter (fun i => dIdx (a i) = m), w i ≤ B m)
    (hG : ∀ i ∈ s, g i ≤ G (dIdx (a i)))
    (hG0 : ∀ m ∈ s.image (fun i => dIdx (a i)), 0 ≤ G m) :
    ∑ i ∈ s, w i * g i ≤ ∑ m ∈ s.image (fun i => dIdx (a i)), B m * G m := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => dIdx (a i))
    (t := s.image (fun i => dIdx (a i))) (fun i hi => mem_image_of_mem _ hi)]
  refine Finset.sum_le_sum fun m hm => ?_
  calc ∑ i ∈ s.filter (fun i => dIdx (a i) = m), w i * g i
      ≤ ∑ i ∈ s.filter (fun i => dIdx (a i) = m), w i * G m := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mem_filter] at hi
        have := hG i hi.1
        rw [hi.2] at this
        exact mul_le_mul_of_nonneg_left this (hw i hi.1)
    _ = (∑ i ∈ s.filter (fun i => dIdx (a i) = m), w i) * G m := by rw [Finset.sum_mul]
    _ ≤ B m * G m := mul_le_mul_of_nonneg_right (hB m hm) (hG0 m hm)

/-- `∑_{m ∈ K} (1/2)^m ≤ 2 (1/2)^{m₀}` when every `m ∈ K` is `≥ m₀`. -/
lemma sum_half_pow_le (K : Finset ℕ) (m0 : ℕ) (hK : ∀ m ∈ K, m0 ≤ m) :
    ∑ m ∈ K, (1 / 2 : ℝ) ^ m ≤ 2 * (1 / 2) ^ m0 := by
  have hinj : Set.InjOn (fun m => m - m0) K := by
    intro a ha b hb h; simp only at h; have := hK a ha; have := hK b hb; omega
  have e : ∑ m ∈ K, (1 / 2 : ℝ) ^ m = ∑ n ∈ K.image (fun m => m - m0), (1 / 2 : ℝ) ^ (n + m0) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Nat.sub_add_cancel (hK m hm)]
  rw [e]
  have hs : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + m0) := by
    simp_rw [pow_add]
    exact (summable_geometric_two).mul_right _
  calc ∑ n ∈ K.image (fun m => m - m0), (1 / 2 : ℝ) ^ (n + m0)
      ≤ ∑' n, (1 / 2 : ℝ) ^ (n + m0) := hs.sum_le_tsum _ (fun _ _ => by positivity)
    _ = 2 * (1 / 2) ^ m0 := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_two]

end GenDyadic

end
