module

public import Mathlib

/-!
# The greedy rule and Lindley's formula (Section 3.4, Lemma 3.7)

The hard greedy rule processes slots `j = 1, 2, …` (in the paper `j = X₀, X₀ + 1, …`; here
re-indexed so that the first slot is `1` and `Q₀ = 0`). With `A j` the number of composite
arrivals in slot `j`,

  `P j = max(0, 1 - Q (j-1) - A j)`,   `Q j = Q (j-1) + A j + P j - 1`.

* `greedyQueue_succ` : `Q j = max(0, Q (j-1) + A j - 1)` (the recursion of Lemma 3.7);
* `greedyQueue_nonneg`, `greedyPrime_mem` : `Q j ≥ 0` and `P j ∈ {0, 1}` when `A ≥ 0`;
* `greedyQueue_lindley` : **Lemma 3.7 (Lindley)**,
  `Q j = max_{0 ≤ i ≤ j} (∑_{l = i+1}^{j} A l - (j - i))`.
-/

@[expose] public section

open Finset

namespace Greedy

/-- The queue `Q j` of the hard greedy rule, driven by the arrivals `A j` (`j ≥ 1`), `Q 0 = 0`. -/
def greedyQueue (A : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => greedyQueue A j + A (j + 1) + max 0 (1 - greedyQueue A j - A (j + 1)) - 1

/-- The prime decision `P j = max(0, 1 - Q (j-1) - A j)` of the hard greedy rule. -/
def greedyPrime (A : ℕ → ℤ) (j : ℕ) : ℤ := max 0 (1 - greedyQueue A j - A (j + 1))

lemma greedyQueue_succ (A : ℕ → ℤ) (j : ℕ) :
    greedyQueue A (j + 1) = max 0 (greedyQueue A j + A (j + 1) - 1) := by
  simp only [greedyQueue]
  omega

lemma greedyQueue_nonneg (A : ℕ → ℤ) (j : ℕ) : 0 ≤ greedyQueue A j := by
  cases j with
  | zero => simp [greedyQueue]
  | succ j => rw [greedyQueue_succ]; exact le_max_left _ _

/-- With nonnegative arrivals, `P j ∈ {0, 1}`. -/
lemma greedyPrime_mem {A : ℕ → ℤ} (hA : ∀ j, 0 ≤ A j) (j : ℕ) :
    greedyPrime A j = 0 ∨ greedyPrime A j = 1 := by
  have h1 := greedyQueue_nonneg A j
  have h2 := hA (j + 1)
  unfold greedyPrime
  omega

/-- **Lemma 3.7 (Lindley)**: the queue is the largest excess of arrivals over slots, taken over
slot windows `(i, j]` ending at `j`: `Q j = max_{0 ≤ i ≤ j} (∑_{l ∈ (i, j]} A l - (j - i))`. -/
theorem greedyQueue_lindley (A : ℕ → ℤ) (j : ℕ) :
    greedyQueue A j = (range (j + 1)).sup' nonempty_range_add_one
      (fun i => ∑ l ∈ Ioc i j, A l - ((j : ℤ) - i)) := by
  induction j with
  | zero => simp [greedyQueue]
  | succ j ih =>
    rw [greedyQueue_succ, ih]
    apply le_antisymm
    · apply max_le
      · exact le_trans (by simp) (le_sup' _ (mem_range.mpr (Nat.lt_succ_self (j + 1))))
      · rw [sub_le_iff_le_add, ← le_sub_iff_add_le, sup'_le_iff]
        intro i hi
        have hi' : i < j + 1 + 1 := by simp at hi; omega
        rw [le_sub_iff_add_le, ← sub_le_iff_le_add]
        refine le_trans (le_of_eq ?_) (le_sup' _ (mem_range.mpr hi'))
        rw [sum_Ioc_succ_top (by simp at hi; omega)]
        push_cast; ring
    · rw [sup'_le_iff]
      intro i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · refine le_trans ?_ (le_max_right _ _)
        have := le_sup' (fun i => ∑ l ∈ Ioc i j, A l - ((j : ℤ) - i)) (mem_range.mpr h)
        refine le_trans (le_of_eq ?_) (by linarith [this] :
          (∑ l ∈ Ioc i j, A l - ((j : ℤ) - i)) + A (j + 1) - 1 ≤ _ + A (j + 1) - 1)
        rw [sum_Ioc_succ_top (by omega)]
        push_cast; ring
      · have : i = j + 1 := by simp at hi; omega
        subst this
        simp

end Greedy

end
