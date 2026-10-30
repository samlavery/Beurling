module

public import RequestProject.BSCert.RankinKHead

/-!
# `rankin_R.py`, part (1): `R(0.69) ≤ 0.77`

The head sum over `p ≤ 10⁵` is kernel-checked in fixed point (`RankinKHead`); the companion
bound `R(0.75) ≤ 0.63`, not used by the corollary, is in `RankinCert75` (`native_decide`).

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

/-- **`rankin_R.py`, check (1), first claim.** `R(0.69) ≤ 0.77`. -/
theorem R_069_le : R (69 / 100) ≤ 77 / 100 := by
  have hσ : ((69 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 69 / 100 := by norm_num
  have hH := head69K
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
  exact le_trans this final69K

end BSCert.Rankin
