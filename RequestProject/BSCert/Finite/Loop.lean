module

public import RequestProject.BSCert.Finite.LogTab

/-!
# A checked running-sum loop

`sumLoop lo hi ok f n A B` runs through `i = n, n+1, …, n+f-1`, adding `lo i` to `A` and
`hi i` to `B`, and checks `ok i A B` after each step. If `lo i ≤ 2^KS g i ≤ hi i` for all `i`
and `A ≤ 2^KS ∑_{i<n} g i ≤ B` at the start, then at every step the running bounds enclose
`2^KS ∑_{i ≤ k} g i` and `ok` holds for them (`sumLoop_spec`).
-/

@[expose] public section

namespace BSCert.FiniteN

/-- The checked running-sum loop. -/
def sumLoop (lo hi : ℕ → ℤ) (ok : ℕ → ℤ → ℤ → Bool) : ℕ → ℕ → ℤ → ℤ → Bool
  | 0, _, _, _ => true
  | f + 1, n, A, B =>
    let A' := A + lo n
    let B' := B + hi n
    ok n A' B' && sumLoop lo hi ok f (n + 1) A' B'

theorem sumLoop_spec (lo hi : ℕ → ℤ) (ok : ℕ → ℤ → ℤ → Bool) (g : ℕ → ℝ)
    (hg : ∀ i, (lo i : ℝ) ≤ 2 ^ KS * g i ∧ 2 ^ KS * g i ≤ hi i) :
    ∀ f n A B, sumLoop lo hi ok f n A B = true →
      (A : ℝ) ≤ 2 ^ KS * ∑ i ∈ Finset.range n, g i →
      2 ^ KS * ∑ i ∈ Finset.range n, g i ≤ B →
      ∀ k, n ≤ k → k < n + f → ∃ A' B' : ℤ,
        (A' : ℝ) ≤ 2 ^ KS * ∑ i ∈ Finset.range (k + 1), g i ∧
        2 ^ KS * ∑ i ∈ Finset.range (k + 1), g i ≤ B' ∧ ok k A' B' = true := by
  intro f
  induction f with
  | zero => intro n A B _ _ _ k h1 h2; omega
  | succ f ih =>
    intro n A B h hA hB k hk1 hk2
    simp only [sumLoop, Bool.and_eq_true] at h
    have hA' : ((A + lo n : ℤ) : ℝ) ≤ 2 ^ KS * ∑ i ∈ Finset.range (n + 1), g i := by
      rw [Finset.sum_range_succ, mul_add]; push_cast; linarith [(hg n).1]
    have hB' : 2 ^ KS * ∑ i ∈ Finset.range (n + 1), g i ≤ ((B + hi n : ℤ) : ℝ) := by
      rw [Finset.sum_range_succ, mul_add]; push_cast; linarith [(hg n).2]
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
    · exact ⟨_, _, hA', hB', h.1⟩
    · exact ih (n + 1) _ _ h.2 hA' hB' k hlt (by omega)

end BSCert.FiniteN
