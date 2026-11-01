module

public import RequestProject.Beurling.Construction.Link

/-!
# The landing data from two counting bounds

`SlotModel.Landing N W x` (and `LandingInit`) ask for the decomposition
`N = V_j - C + E₊ - E₋`, `0 ≤ C ≤ A_j`, together with finite sets of points carrying the landing
errors `E±`, unit-separated for a monotone function `F` of slope at most `c` with
`c ℓ± ≤ W + ε`. Taking `F` linear, these point sets exist as soon as `E± ≤ W + ε + 1`: the
data reduce to the decomposition and the two counting bounds (`landing_of_counts`,
`landingInit_of_counts`).
-/

@[expose] public section

open Set Real

namespace SlotModel

variable {X₀ : ℕ} (M : SlotModel X₀)

/-- `n` points `x, x + 1, …, x + n - 1`. -/
lemma exists_unit_points (x : ℝ) (n : ℕ) :
    ∃ S : Finset ℝ, S.card = n ∧ (∀ s ∈ S, x ≤ s ∧ s ≤ x + (n - 1 : ℝ)) ∧
      ∀ s ∈ S, ∀ t ∈ S, s < t → 1 ≤ t - s := by
  classical
  refine ⟨(Finset.range n).image (fun i : ℕ => x + i), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun i j h => by
      have : (i : ℝ) = j := by linarith [h]
      exact_mod_cast this)]
    exact Finset.card_range n
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hi
    constructor <;> [linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]; linarith]
  · intro s hs t ht hst
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    have hij : i < j := by
      have : (i : ℝ) < j := by linarith
      exact_mod_cast this
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith

/-- **The landing data from the counts**: the decomposition, `0 ≤ C ≤ A_j`, and `E± ≤ W + 3/2`
for natural numbers `E±` give `Landing N W x`. -/
theorem landing_of_counts {N W x C : ℝ} {Ep Em : ℕ} (hW : 0 ≤ W)
    (hN : N = (M.V (M.slotIdx x) : ℝ) - C + Ep - Em) (hC0 : 0 ≤ C)
    (hCA : C ≤ (M.slotArr (M.slotIdx x) : ℝ)) (hEp : (Ep : ℝ) ≤ W + 3 / 2)
    (hEm : (Em : ℝ) ≤ W + 3 / 2) : M.Landing N W x := by
  obtain ⟨Sp, hSpc, hSp, hgp⟩ := exists_unit_points x Ep
  obtain ⟨Sm', hSmc, hSm', hgm⟩ := exists_unit_points (x - (W + 1 / 2)) Em
  refine ⟨C, Ep, Em, 1 / 2, 1, W + 1 / 2, W + 1 / 2, id, Sp, Sm', monotone_id, hN, hC0, hCA,
    by linarith, by linarith, ?_, ?_, hgp, hgm, by simp, by simp, Nat.cast_nonneg _,
    by rw [hSpc], Nat.cast_nonneg _, by rw [hSmc], by linarith, by linarith, by norm_num⟩
  · intro s hs
    obtain ⟨h1, h2⟩ := hSp s hs
    exact ⟨h1, by linarith⟩
  · intro s hs
    obtain ⟨h1, h2⟩ := hSm' s hs
    exact ⟨h1, by linarith⟩

/-- **The initial landing data from the counts**: as `landing_of_counts`, with `E± ≤ W + 7/2`. -/
theorem landingInit_of_counts {N W x C : ℝ} {Ep Em : ℕ} (hW : 0 ≤ W)
    (hN : N = (M.V (M.slotIdx x) : ℝ) - C + Ep - Em) (hC0 : 0 ≤ C)
    (hCA : C ≤ (M.slotArr (M.slotIdx x) : ℝ)) (hEp : (Ep : ℝ) ≤ W + 7 / 2)
    (hEm : (Em : ℝ) ≤ W + 7 / 2) : M.LandingInit N W x := by
  obtain ⟨Sp, hSpc, hSp, hgp⟩ := exists_unit_points x Ep
  obtain ⟨Sm', hSmc, hSm', hgm⟩ := exists_unit_points (x - (W + 5 / 2)) Em
  refine ⟨C, Ep, Em, 5 / 2, 1, W + 5 / 2, W + 5 / 2, id, Sp, Sm', monotone_id, hN, hC0, hCA,
    by linarith, by linarith, ?_, ?_, hgp, hgm, by simp, by simp, Nat.cast_nonneg _,
    by rw [hSpc], Nat.cast_nonneg _, by rw [hSmc], by linarith, by linarith, by norm_num⟩
  · intro s hs
    obtain ⟨h1, h2⟩ := hSp s hs
    exact ⟨h1, by linarith⟩
  · intro s hs
    obtain ⟨h1, h2⟩ := hSm' s hs
    exact ⟨h1, by linarith⟩

end SlotModel

end
