module

public import Mathlib

/-!
# `consts.py`, lines x2–x4 (Appendix B.4, Proposition 5.31)

* x2: `(1/4) · 7.4915 · 2^{0.2} ≤ 2.152`;
* x3: `2^{ω(n)} ≤ ∏_{p | n} 2 p^{-1/2} · √n ≤ (4/√6) √n` and `4/√6 ≤ 1.64`, proved for every
  `n ≥ 1` (the script evaluates `4/√6`);
* x4: `(1/2 + 1.64 √n)/n + 2.152 n^{-0.2} ≤ 0.14` for every `n ≥ 10⁶` (the script evaluates the
  left side at `n = 10⁶`, where both terms are largest).
-/

@[expose] public section

namespace BSCert.Consts

open Real Finset

/-- **x2.** `(1/4) · 7.4915 · 2^{0.2} ≤ 2.152`. -/
theorem x2 : 1 / 4 * 7.4915 * (2 : ℝ) ^ (0.2 : ℝ) ≤ 2.152 := by
  set t := (2 : ℝ) ^ (0.2 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have ht5 : t ^ 5 = 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have : t ≤ 1.149 := by
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (by norm_num) (show (5 : ℕ) ≠ 0 by norm_num)
    rw [ht5] at this
    norm_num at this
  linarith

/-- `∏_{p ∈ S} (4/p) ≤ 8/3` for every finite set of primes. -/
lemma prod_four_div_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (4 / (p : ℝ)) ≤ 8 / 3 := by
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ 3)]
  have hsub : S.filter (fun p => p ≤ 3) ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [mem_filter] at hp
    have := (hS p hp.1).two_le
    simp only [mem_insert, mem_singleton]
    omega
  have h1 : ∏ p ∈ S.filter (fun p => p ≤ 3), (4 / (p : ℝ)) ≤ 8 / 3 := by
    rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem,
      Finset.prod_pair (by norm_num)]
    split_ifs <;> norm_num
  have h2 : ∏ p ∈ S.filter (fun p => ¬ p ≤ 3), (4 / (p : ℝ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p _; positivity
    · intro p hp
      simp only [mem_filter] at hp
      have h4 : (4 : ℝ) ≤ p := by
        have : 4 ≤ p := by omega
        exact_mod_cast this
      rw [div_le_one (by linarith)]; exact h4
  have h0 : 0 ≤ ∏ p ∈ S.filter (fun p => ¬ p ≤ 3), (4 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have h0' : 0 ≤ ∏ p ∈ S.filter (fun p => p ≤ 3), (4 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  nlinarith

/-- `3 · 4^{ω(n)} ≤ 8 n` for every `n ≥ 1`. -/
lemma four_pow_omega_le {n : ℕ} (hn : n ≠ 0) :
    3 * (4 : ℝ) ^ n.primeFactors.card ≤ 8 * n := by
  have hS : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod := prod_four_div_le n.primeFactors hS
  have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hle : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hP : 0 < ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos (fun p hp => (hS p hp).pos)
    exact_mod_cast this
  rw [Finset.prod_div_distrib, Finset.prod_const] at hprod
  push_cast at hle hP
  rw [div_le_iff₀ hP] at hprod
  nlinarith

/-- **x3.** `2^{ω(n)} ≤ (4/√6) √n` for every `n ≥ 1`, and `4/√6 ≤ 1.64`. So
`2^{ω(n)} ≤ 1.64 √n`. -/
theorem x3 {n : ℕ} (hn : n ≠ 0) :
    (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ 4 / Real.sqrt 6 * Real.sqrt n ∧
      4 / Real.sqrt 6 ≤ 1.64 := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    ← Nat.primeFactors.eq_1]
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have h66 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  constructor
  · have key := four_pow_omega_le hn
    set k := n.primeFactors.card
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
    have hrhs : 0 ≤ 4 / Real.sqrt 6 * Real.sqrt n := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
    rw [← abs_of_nonneg h2, ← abs_of_nonneg hrhs]
    apply sq_le_sq.mp
    rw [mul_pow, div_pow, sq, sq, sq, h66, sq, hsn, ← pow_add, ← two_mul, pow_mul]
    norm_num
    linarith
  · rw [div_le_iff₀ h6]
    nlinarith [Real.sqrt_nonneg 6]

/-- **x4.** `(1/2 + 1.64 √n)/n + 2.152 n^{-0.2} ≤ 0.14` for every `n ≥ 10⁶`. -/
theorem x4 {n : ℝ} (hn : 10 ^ 6 ≤ n) :
    (1 / 2 + 1.64 * Real.sqrt n) / n + 2.152 * n ^ (-0.2 : ℝ) ≤ 0.14 := by
  have hn0 : 0 < n := by linarith
  have hs : 1000 ≤ Real.sqrt n := by
    rw [show (1000 : ℝ) = Real.sqrt (10 ^ 6) by
      rw [show (10 : ℝ) ^ 6 = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hn
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have h1 : (1 / 2 + 1.64 * Real.sqrt n) / n ≤ 0.0016405 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  set t := n ^ (-0.2 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
  have ht5 : t ^ 5 = 1 / n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have h2n : 1 / n ≤ 1 / 10 ^ 6 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have htle : t ≤ 0.0631 := by
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (by norm_num) (show (5 : ℕ) ≠ 0 by norm_num)
    rw [ht5] at this
    norm_num at this h2n
    linarith
  linarith

/-- x2 and x4 together: the analytic tail of Proposition 5.31(i),
`(1/2 + 1.64√n)/n + (1/4) · 7.4915 · 2^{0.2} n^{-0.2} ≤ 0.14` for `n ≥ 10⁶`. -/
theorem x0_tail_le {n : ℝ} (hn : 10 ^ 6 ≤ n) :
    (1 / 2 + 1.64 * Real.sqrt n) / n + 1 / 4 * 7.4915 * (2 : ℝ) ^ (0.2 : ℝ) * n ^ (-0.2 : ℝ)
      ≤ 0.14 := by
  have h := x4 hn
  have hp : 0 ≤ n ^ (-0.2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have := mul_le_mul_of_nonneg_right x2 hp
  linarith

end BSCert.Consts
