module

public import RequestProject.BSCert.RankinCert
meta import RequestProject.BSCert.Rankin

/-!
# `rankin_R.py`, part (1), second claim: `R(0.75) ≤ 0.63`

Still checked by `native_decide` (floating-point hints for `p^{-σ}`); not used by
`BModel.corollary_2_2_complete`.
-/

@[expose] public section

namespace BSCert.Rankin

lemma head75_ok :
    ∀ p ∈ (Finset.range (100000 + 1)).filter Nat.Prime, primeOK 3 4 0.75 p = true := by
  native_decide

lemma final75 :
    ((headUB 0.75 100000 : ℚ) : ℝ) + (1 / 2 + (9 / 50000) / (1 - 9 / 50000)) *
      ((3163 / 1000000) / (2 * (2 * (3 / 4) - 1))) ≤ 63 / 100 := by
  have : (headUB 0.75 100000 : ℚ) + (1 / 2 + (9 / 50000) / (1 - 9 / 50000)) *
      ((3163 / 1000000) / (2 * (2 * (3 / 4) - 1))) ≤ 63 / 100 := by native_decide
  generalize headUB 0.75 100000 = h at this ⊢
  have h2 := (Rat.cast_le (K := ℝ)).mpr this
  push_cast at h2
  linarith

/-- **`rankin_R.py`, check (1), second claim.** `R(0.75) ≤ 0.63`. -/
theorem R_075_le : R (3 / 4) ≤ 63 / 100 := by
  have hσ : ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 / 4 := by norm_num
  have hH := head_le (a := 3) (b := 4) (by norm_num) head75_ok
  rw [hσ] at hH
  have hδ : ((100000 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 9 / 50000 := by
    have := rpow_neg_le_of_check (n := ((100000 : ℕ) : ℝ)) (by norm_num) (a := 3) (b := 4)
      (by norm_num) (q := 9 / 50000) (by norm_num) (by norm_num)
    rwa [hσ] at this
  have hY : (((100000 : ℕ) : ℝ) - 1) ^ (-(2 * (3 / 4 : ℝ) - 1)) ≤ 3163 / 1000000 := by
    have := rpow_neg_le_of_check (n := ((100000 : ℕ) : ℝ) - 1) (by norm_num) (a := 1) (b := 2)
      (by norm_num) (q := 3163 / 1000000) (by norm_num) (by norm_num)
    have e : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 2 * (3 / 4 : ℝ) - 1 := by norm_num
    rwa [e] at this
  have := R_le_of (σ := 3 / 4) (by norm_num) (by norm_num) (N := 100000) (by norm_num)
    (by decide) hδ (by norm_num) hY hH
  exact le_trans this final75

end BSCert.Rankin
