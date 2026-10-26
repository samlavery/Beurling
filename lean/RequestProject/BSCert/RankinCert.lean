module

public import RequestProject.BSCert.Rankin
meta import RequestProject.BSCert.Rankin

/-!
# `rankin_R.py`, part (1): `R(0.69) ≤ 0.77` and `R(0.75) ≤ 0.63`

Here `R(σ) = ∑_p (-log(1 - p^{-σ}) - p^{-σ})` over all primes (Lemma 6.22(c),(e) of the paper).
-/

@[expose] public section

namespace BSCert.Rankin

/-- The defining series of `R(σ)` converges for `σ > 1/2`. -/
theorem summable_rTerm {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes => rTerm σ p) := by
  have hσ0 : 0 < σ := by linarith
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + (2 * σ - 1)))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine Summable.of_nonneg_of_le (fun p => rTerm_nonneg hσ0 p.2.two_le) (fun p => ?_)
    (hs.mul_left (1 / 2 + (2 : ℝ) ^ (-σ) / (1 - (2 : ℝ) ^ (-σ))))
  exact rTerm_le_tail (N := 2) hσ0 (by norm_num) p.2.two_le (by norm_num) h2

lemma head69_ok :
    ∀ p ∈ (Finset.range (100000 + 1)).filter Nat.Prime, primeOK 69 100 0.69 p = true := by
  native_decide

lemma head75_ok :
    ∀ p ∈ (Finset.range (100000 + 1)).filter Nat.Prime, primeOK 3 4 0.75 p = true := by
  native_decide

lemma final69 :
    ((headUB 0.69 100000 : ℚ) : ℝ) + (1 / 2 + (9 / 25000) / (1 - 9 / 25000)) *
      ((63 / 5000) / (2 * (2 * (69 / 100) - 1))) ≤ 77 / 100 := by
  have : (headUB 0.69 100000 : ℚ) + (1 / 2 + (9 / 25000) / (1 - 9 / 25000)) *
      ((63 / 5000) / (2 * (2 * (69 / 100) - 1))) ≤ 77 / 100 := by native_decide
  generalize headUB 0.69 100000 = h at this ⊢
  have h2 := (Rat.cast_le (K := ℝ)).mpr this
  push_cast at h2
  linarith

lemma final75 :
    ((headUB 0.75 100000 : ℚ) : ℝ) + (1 / 2 + (9 / 50000) / (1 - 9 / 50000)) *
      ((3163 / 1000000) / (2 * (2 * (3 / 4) - 1))) ≤ 63 / 100 := by
  have : (headUB 0.75 100000 : ℚ) + (1 / 2 + (9 / 50000) / (1 - 9 / 50000)) *
      ((3163 / 1000000) / (2 * (2 * (3 / 4) - 1))) ≤ 63 / 100 := by native_decide
  generalize headUB 0.75 100000 = h at this ⊢
  have h2 := (Rat.cast_le (K := ℝ)).mpr this
  push_cast at h2
  linarith

/-- **`rankin_R.py`, check (1), first claim.** `R(0.69) ≤ 0.77`. -/
theorem R_069_le : R (69 / 100) ≤ 77 / 100 := by
  have hσ : ((69 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 69 / 100 := by norm_num
  have hH := head_le (a := 69) (b := 100) (by norm_num) head69_ok
  rw [hσ] at hH
  have hδ : ((100000 : ℕ) : ℝ) ^ (-(69 / 100 : ℝ)) ≤ 9 / 25000 := by
    have := rpow_neg_le_of_check (n := ((100000 : ℕ) : ℝ)) (by norm_num) (a := 69) (b := 100)
      (by norm_num) (q := 9 / 25000) (by norm_num) (by norm_num)
    rwa [hσ] at this
  have hY : (((100000 : ℕ) : ℝ) - 1) ^ (-(2 * (69 / 100 : ℝ) - 1)) ≤ 63 / 5000 := by
    have := rpow_neg_le_of_check (n := ((100000 : ℕ) : ℝ) - 1) (by norm_num) (a := 38) (b := 100)
      (by norm_num) (q := 63 / 5000) (by norm_num) (by norm_num)
    have e : ((38 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 2 * (69 / 100 : ℝ) - 1 := by norm_num
    rwa [e] at this
  have := R_le_of (σ := 69 / 100) (by norm_num) (by norm_num) (N := 100000) (by norm_num)
    (by decide) hδ (by norm_num) hY hH
  exact le_trans this final69

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
