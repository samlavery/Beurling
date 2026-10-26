module

public import RequestProject.BSCert.Finite.CM
meta import RequestProject.BSCert.Finite.CM

/-!
# `finite_checks.py`, lines 1, 2 and 6 (Lemma 5.1 for `ℕ`)
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction Chebyshev

lemma cm1_checks : ∀ N ∈ Icc 1 1499, cm1Check N = true := by native_decide

lemma cm2_checks : sumLoop cm2Lo cm2Hi cm2Ok (10 ^ 7) 1 0 0 = true := by native_decide

lemma cm3_checks : sumLoop (fun _ => 0) cm3Hi cm3Ok (cm3N + 1) 0 0 0 = true := by native_decide

/-- **`finite_checks.py`, line 1** (Lemma 5.1(i) for `ℕ`, small `x`): for `1 ≤ x < 1500`,
`ψ(x) - ψ(x/2) ≤ 0.6803 x` (the maximum `0.68024 x` is attained at `x = 5`). -/
theorem psi_sub_psi_half_le_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x < 1500) :
    ψ x - ψ (x / 2) ≤ 0.6803 * x :=
  cm1_of_check cm1_checks hx1 hx2

/-- **`finite_checks.py`, line 2** (Lemma 5.1(ii) for `ℕ`): for `1 ≤ x ≤ 10⁷`,
`-0.753 ≤ S(x) - log x ≤ 0`, where `S(x) = ∑_{p^k ≤ x} log p / p^k`. -/
theorem mertensS_sub_log_mem {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 7) :
    -0.753 ≤ mertensS x - Real.log x ∧ mertensS x - Real.log x ≤ 0 :=
  cm2_of_check cm2_checks hx1 hx2

/-- **`finite_checks.py`, line 6** (Lemma 5.1(iii)): `∑_p log p / (p(p-1)) ≤ 0.75537`, the sum
over all primes (the series converges). -/
theorem sum_log_div_prime_le :
    Summable (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) ∧
    ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75537 :=
  cm3_of_check cm3_checks

end BSCert.FiniteN
