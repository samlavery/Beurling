module

public import RequestProject.Beurling.SmoothTailsCert
public import RequestProject.Beurling.Construction.NatPrimeCountDefs
meta import RequestProject.Beurling.Construction.NatPrimeCountDefs

/-!
# `π(N) ≤ 2N / log N` for the rational primes, `N ≥ 8`

Step (v) of Lemma 6.26 uses `π(s) ≤ 2s/log s` for the realised primes; below `X₀⁻` these are the
rational primes, for which the paper cites the Rosser–Schoenfeld bound `π(s) ≤ 1.26 s/log s`.
Here the weaker bound `π(N) ≤ 2N/log N`, which is all that step (v) needs, is proved from
Chebyshev's bound `θ(N) ≤ ψ(N) ≤ 1.42 N` (Lemma 5.1(i) for ℕ, `finite_checks.py`):

* Abel summation: `π(N) ≤ 2.84/log 2 + 1.42 ∑_{n=3}^N 1/log n` (`primeCount_le_abel`);
* the right-hand side is `≤ 2N/log N` at `N = 1000` (a certified computation with the fixed-point
  logarithms of `LogTab`) and the increments are compatible for `N ≥ 1000`;
* for `8 ≤ N ≤ 1000` the bound is checked directly (certified computation).
-/

@[expose] public section

open Finset Real BSCert.FiniteN

namespace NatPrimeCount

lemma piOk_all : ∀ N ∈ Icc 8 1000, piOk N = true := by native_decide

lemma logLoN_pos_all : ∀ n ∈ Icc 3 1000, 0 < logLoN n := by native_decide

lemma lo2_pos : 0 < lo2 := by native_decide

lemma base_ok : (284 / 100 : ℚ) * (2 ^ KS / lo2) + (142 / 100) * sumRecip 1000 ≤
    2000 * 2 ^ KS / logHiN 1000 := by native_decide

/-- `π(N) ≤ 2N/log N` for `8 ≤ N ≤ 1000`. -/
lemma primeCount_le_small {N : ℕ} (h8 : 8 ≤ N) (h1000 : N ≤ 1000) :
    (((N + 1).primesBelow.card : ℕ) : ℝ) ≤ 2 * N / Real.log N := by
  have hok := piOk_all N (Finset.mem_Icc.mpr ⟨h8, h1000⟩)
  unfold piOk at hok
  have hle : (((N + 1).primesBelow.card : ℤ) : ℝ) * (logHiN N : ℝ) ≤ 2 * N * 2 ^ KS := by
    have := of_decide_eq_true hok
    exact_mod_cast this
  have hspec := logHiN_spec (n := N) (by omega)
  have hN : (8 : ℝ) ≤ N := by exact_mod_cast h8
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have hc : (0 : ℝ) ≤ ((N + 1).primesBelow.card : ℝ) := by positivity
  rw [le_div_iff₀ hl]
  push_cast at hle
  have : ((N + 1).primesBelow.card : ℝ) * (2 ^ KS * Real.log N) ≤ 2 * N * 2 ^ KS :=
    (mul_le_mul_of_nonneg_left hspec hc).trans hle
  nlinarith

/-- **Abel summation against `θ(N) ≤ 1.42 N`**: `π(N) ≤ 2.84/log 2 + 1.42 ∑_{n=3}^N 1/log n`. -/
lemma primeCount_le_abel {N : ℕ} (hN : 2 ≤ N) :
    (((N + 1).primesBelow.card : ℕ) : ℝ) ≤
      2.84 / Real.log 2 + 1.42 * ∑ n ∈ Icc 3 N, 1 / Real.log n := by
  have e : (((N + 1).primesBelow.card : ℕ) : ℝ) =
      ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) * (1 / Real.log k) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Mertens.sum_primesBelow_eq]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs with hp
    · have : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp; simp
    · simp
  rw [e]
  have hab := Mertens.abel_upper (fun k => if k.Prime then Real.log k else 0)
    (fun n => 1 / Real.log n) (fun n => 1.42 * n) (fun N _ => SmoothTails.theta_partial_le N)
    (by
      intro n hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le (Real.log_pos (by linarith))
      exact Real.log_le_log (by linarith) (by push_cast; linarith))
    (by
      intro n hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg zero_le_one (Real.log_nonneg (by linarith))) hN
  refine hab.trans (le_of_eq ?_)
  simp only
  rw [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The comparison inequality at `N = 1000`. -/
lemma compare_base :
    2.84 / Real.log 2 + 1.42 * ∑ n ∈ (Icc 3 1000 : Finset ℕ), 1 / Real.log (n : ℝ) ≤
      2 * (1000 : ℕ) / Real.log (1000 : ℕ) := by
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have hb := base_ok
  have hb' : (284 / 100 : ℝ) * (2 ^ KS / (lo2 : ℝ)) +
      (142 / 100) * ∑ n ∈ (Icc 3 1000 : Finset ℕ), ((2 : ℝ) ^ KS / (logLoN n : ℝ)) ≤
      2000 * 2 ^ KS / (logHiN 1000 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hb
    unfold sumRecip at this
    push_cast at this
    exact this
  have hl2 := log2_spec.1
  have hlo2 : (0 : ℝ) < lo2 := by exact_mod_cast lo2_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have t1 : 1 / Real.log 2 ≤ 2 ^ KS / (lo2 : ℝ) := by
    rw [div_le_div_iff₀ hlog2 hlo2]; linarith
  have t2 : ∀ n ∈ (Icc 3 1000 : Finset ℕ), 1 / Real.log (n : ℝ) ≤
      (2 : ℝ) ^ KS / (logLoN n : ℝ) := by
    intro n hn
    have hpos : (0 : ℝ) < logLoN n := by exact_mod_cast logLoN_pos_all n hn
    have hsp := logLoN_spec (n := n) (by simp at hn; omega)
    have hln : 0 < Real.log n := by
      have : (3 : ℝ) ≤ n := by simp at hn; exact_mod_cast hn.1
      exact Real.log_pos (by linarith)
    rw [div_le_div_iff₀ hln hpos]; linarith
  have t3 := Finset.sum_le_sum t2
  have hhi := logHiN_spec (n := 1000) (by norm_num)
  have hl1000 : 0 < Real.log (1000 : ℕ) := Real.log_pos (by norm_num)
  have hhipos : (0 : ℝ) < logHiN 1000 := by
    have : (0 : ℝ) < 2 ^ KS * Real.log (1000 : ℕ) := by positivity
    push_cast at hhi this ⊢; linarith
  have t4 : 2000 * 2 ^ KS / (logHiN 1000 : ℝ) ≤ 2 * (1000 : ℕ) / Real.log (1000 : ℕ) := by
    rw [div_le_div_iff₀ hhipos hl1000]
    push_cast at hhi ⊢
    nlinarith
  have t5 : 2.84 / Real.log 2 = 2.84 * (1 / Real.log 2) := by ring
  rw [t5]
  have : (284 / 100 : ℝ) = 2.84 := by norm_num
  have : (142 / 100 : ℝ) = 1.42 := by norm_num
  nlinarith

/-- The increments: `1.42/log(N+1) ≤ 2(N+1)/log(N+1) - 2N/log N` for `N ≥ 1000`. -/
lemma compare_step {N : ℕ} (hN : 1000 ≤ N) :
    1.42 * (1 / Real.log ((N + 1 : ℕ) : ℝ)) ≤
      2 * ((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ) - 2 * (N : ℝ) / Real.log N := by
  have hN' : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hl1 : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hl1pos : 0 < Real.log ((N : ℝ) + 1) := by linarith
  have hd : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1) / N) (by positivity)
    have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
    linarith
  have hl7 : 6 ≤ Real.log N := by
    have : Real.log 1000 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
    have h2 : 6 ≤ Real.log 1000 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h := Real.exp_one_lt_d9
      have e2 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      have e3 : Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 := pow_le_pow_left₀ (by positivity) h.le 6
      linarith [show (2.7182818286 : ℝ) ^ 6 ≤ 1000 by norm_num]
    linarith
  -- multiply through by `log N · log(N+1)`
  have key : 1.42 * Real.log N ≤ 2 * ((N : ℝ) + 1) * Real.log N - 2 * N * Real.log ((N : ℝ) + 1) := by
    have h1 : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ N)
      rwa [mul_one_div_cancel (by linarith)] at this
    nlinarith
  rw [div_sub_div _ _ hl1pos.ne' hl.ne', le_div_iff₀ (by positivity)]
  have e : 1.42 * (1 / Real.log ((N : ℝ) + 1)) * (Real.log ((N : ℝ) + 1) * Real.log N) =
      1.42 * Real.log N := by field_simp
  rw [e]; linarith

lemma compare_ge {N : ℕ} (hN : 1000 ≤ N) :
    2.84 / Real.log 2 + 1.42 * ∑ n ∈ Icc 3 N, 1 / Real.log n ≤ 2 * (N : ℝ) / Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => exact compare_base
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := compare_step hM
    linarith

/-- **`π(N) ≤ 2N/log N` for every `N ≥ 8`** (rational primes). -/
theorem primeCount_le {N : ℕ} (hN : 8 ≤ N) :
    (((N + 1).primesBelow.card : ℕ) : ℝ) ≤ 2 * N / Real.log N := by
  rcases le_or_gt N 1000 with h | h
  · exact primeCount_le_small hN h
  · exact (primeCount_le_abel (by omega)).trans (compare_ge h.le)

end NatPrimeCount

end
