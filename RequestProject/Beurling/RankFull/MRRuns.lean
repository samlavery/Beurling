module

public import Mathlib

/-!
# Run structure of a skeleton, by column

A run structure `l = [j_T, …, j_1]` (earliest run first, as in `comps`/`finG`) splits the pivot
columns `0, …, K-1` (earliest first, `K = ∑ l`) into consecutive runs. For a column `j`:
* `runNum l j` : the index of its run from the front (`0` for the earliest run);
* `runFirst l j` : the first (earliest) column of its run.

These are the run data used by the multi-run recursion of Lemma A.5.
-/

@[expose] public section

namespace RankFull.Runs

/-- The index (from the front) of the run containing column `j`. -/
def runNum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: l, j => if j < a then 0 else runNum l (j - a) + 1

/-- The first column of the run containing column `j`. -/
def runFirst : List ℕ → ℕ → ℕ
  | [], j => j
  | a :: l, j => if j < a then 0 else runFirst l (j - a) + a

theorem runFirst_le : ∀ (l : List ℕ) (j : ℕ), runFirst l j ≤ j
  | [], j => le_rfl
  | a :: l, j => by
    simp only [runFirst]
    split_ifs with h
    · exact Nat.zero_le _
    · have := runFirst_le l (j - a); omega

theorem runNum_mono : ∀ (l : List ℕ) {j j' : ℕ}, j ≤ j' → runNum l j ≤ runNum l j'
  | [], _, _, _ => le_rfl
  | a :: l, j, j', h => by
    simp only [runNum]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · have := runNum_mono l (show j - a ≤ j' - a by omega); omega

/-- Columns between the first column of a run and `j` lie in the same run. -/
theorem runNum_eq_of_between : ∀ (l : List ℕ) {j j' : ℕ}, runFirst l j ≤ j' → j' ≤ j →
    runNum l j' = runNum l j ∧ runFirst l j' = runFirst l j
  | [], j, j', h1, h2 => by simp only [runFirst] at h1; simp [runNum, runFirst]; omega
  | a :: l, j, j', h1, h2 => by
    simp only [runNum, runFirst] at h1 ⊢
    by_cases hj : j < a
    · have hj' : j' < a := lt_of_le_of_lt h2 hj
      simp [hj, hj']
    · rw [if_neg hj] at h1
      have hj' : ¬ j' < a := by omega
      simp only [hj, hj', if_false]
      have := runNum_eq_of_between l (j := j - a) (j' := j' - a) (by omega) (by omega)
      exact ⟨by rw [this.1], by rw [this.2]⟩

/-- Two columns of the same run: the earlier one is at least the first column of the run. -/
theorem runFirst_le_of_runNum_eq : ∀ (l : List ℕ) {j j' : ℕ}, j < l.sum → j' ≤ j →
    runNum l j' = runNum l j → runFirst l j ≤ j'
  | [], j, j', hs, h, _ => by simp at hs
  | a :: l, j, j', hs, h, he => by
    simp only [runNum, runFirst, List.sum_cons] at he hs ⊢
    by_cases hj : j < a
    · simp only [hj, if_true]; exact Nat.zero_le _
    · simp only [hj, if_false] at he ⊢
      by_cases hj' : j' < a
      · simp only [hj', if_true] at he; omega
      · simp only [hj', if_false] at he
        have := runFirst_le_of_runNum_eq l (j := j - a) (j' := j' - a) (by omega) (by omega)
          (by omega)
        omega

theorem runNum_zero (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) : runNum l 0 = 0 := by
  cases l with
  | nil => rfl
  | cons b l =>
    have := hpos b (by simp)
    simp only [runNum]; split_ifs <;> omega

theorem runFirst_zero (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) : runFirst l 0 = 0 := by
  cases l with
  | nil => rfl
  | cons b l =>
    have := hpos b (by simp)
    simp only [runFirst]; split_ifs <;> omega

/-- The first column of a run, not the first column overall, starts a new run: the previous
column is in the previous run. -/
theorem runNum_pred_of_first : ∀ (l : List ℕ) {j : ℕ}, j < l.sum → 1 ≤ j → runFirst l j = j →
    (∀ a ∈ l, 1 ≤ a) → runNum l (j - 1) + 1 = runNum l j
  | [], j, hs, _, _, _ => by simp at hs
  | a :: l, j, hs, h1, h2, hpos => by
    have ha : 1 ≤ a := hpos a (by simp)
    simp only [runNum, runFirst, List.sum_cons] at h2 hs ⊢
    by_cases hj : j < a
    · simp only [hj, if_true] at h2; omega
    · simp only [hj, if_false] at h2 ⊢
      by_cases hj1 : j - 1 < a
      · simp only [hj1, if_true]
        have hja : j = a := by omega
        subst hja
        simp only [Nat.sub_self]
        rw [runNum_zero l (fun b hb => hpos b (by simp [hb]))]
      · simp only [hj1, if_false]
        have hpos' : ∀ b ∈ l, 1 ≤ b := fun b hb => hpos b (by simp [hb])
        have hja : 1 ≤ j - a := by
          by_contra h; push_neg at h
          have h0 : j - a = 0 := by omega
          rw [h0, runFirst_zero l hpos'] at h2; omega
        have := runNum_pred_of_first l (j := j - a) (by omega) hja (by omega) hpos'
        rw [show j - 1 - a = j - a - 1 by omega]
        omega

/-- A column that is not the first of its run: the previous column is in the same run. -/
theorem runNum_pred_of_not_first (l : List ℕ) {j : ℕ} (h : runFirst l j < j) :
    runNum l (j - 1) = runNum l j ∧ runFirst l (j - 1) = runFirst l j :=
  runNum_eq_of_between l (by omega) (by omega)

/-- The columns from the first column of the run of `j` on are those of the runs from
`runNum l j` on. -/
theorem sum_drop_runNum : ∀ (l : List ℕ) {j : ℕ}, j < l.sum →
    (l.drop (runNum l j)).sum = l.sum - runFirst l j
  | [], j, h => by simp at h
  | a :: l, j, h => by
    simp only [runNum, runFirst, List.sum_cons] at h ⊢
    by_cases hj : j < a
    · rw [if_pos hj, if_pos hj]; simp
    · rw [if_neg hj, if_neg hj]
      simp only [List.drop_succ_cons]
      rw [sum_drop_runNum l (j := j - a) (by omega)]
      have := runFirst_le l (j - a)
      omega

theorem runNum_lt_length : ∀ (l : List ℕ) {j : ℕ}, j < l.sum → runNum l j < l.length
  | [], j, h => by simp at h
  | a :: l, j, h => by
    simp only [runNum, List.sum_cons, List.length_cons] at h ⊢
    split_ifs with hj
    · omega
    · have := runNum_lt_length l (j := j - a) (by omega); omega



/-- The runs before run `i` are the first `(l.take i).sum` columns. -/
theorem runNum_lt_iff : ∀ (l : List ℕ) {j : ℕ} (i : ℕ), j < l.sum →
    (runNum l j < i ↔ j < (l.take i).sum)
  | [], j, i, h => by simp at h
  | a :: l, j, i, h => by
    simp only [runNum, List.sum_cons] at h ⊢
    rcases i with _ | i
    · simp
    · simp only [List.take_succ_cons, List.sum_cons]
      by_cases hj : j < a
      · rw [if_pos hj]; constructor <;> intro <;> omega
      · rw [if_neg hj]
        have := runNum_lt_iff l (j := j - a) i (by omega)
        constructor
        · intro h1; have := this.mp (by omega); omega
        · intro h1; have := this.mpr (by omega); omega

/-- A function with the same initial segments as the runs is the run index. -/
theorem runNum_eq_of_lt_iff (l : List ℕ) (r : ℕ → ℕ) {j : ℕ} (hj : j < l.sum)
    (hr : ∀ i, r j < i ↔ j < (l.take i).sum) : runNum l j = r j := by
  have h1 := runNum_lt_iff l (runNum l j + 1) hj
  have h2 := runNum_lt_iff l (r j + 1) hj
  have h3 := runNum_lt_iff l (runNum l j) hj
  have h4 := hr (runNum l j)
  have h5 := hr (r j + 1)
  have h6 := hr (runNum l j + 1)
  have h7 := runNum_lt_iff l (r j) hj
  have h8 := hr (r j)
  -- both `runNum l j` and `r j` are the least `i` with `j < (l.take (i+1)).sum`
  rcases Nat.lt_trichotomy (runNum l j) (r j) with h | h | h
  · exfalso
    have a1 : j < (l.take (runNum l j + 1)).sum := h1.mp (Nat.lt_succ_self _)
    have a2 : r j < runNum l j + 1 := h6.mpr a1
    omega
  · exact h
  · exfalso
    have a1 : j < (l.take (r j + 1)).sum := h5.mp (Nat.lt_succ_self _)
    have a2 : runNum l j < r j + 1 := h2.mpr a1
    omega

end RankFull.Runs
