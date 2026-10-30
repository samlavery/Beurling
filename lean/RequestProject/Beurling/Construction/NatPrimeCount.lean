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
* the right-hand side is `≤ 2N/log N` at `N = 1000` (a kernel-checked computation, with
  `log n ≥ j/10` certified by `e^{j/10} ≤ (U/10⁸)^j ≤ n`) and the increments are compatible for
  `N ≥ 1000`;
* for `8 ≤ N ≤ 1000` the bound is checked directly (kernel-checked trial division, with
  `log N ≤ k log 2 < 0.7 k` for `N ≤ 2^k`).

The computations (`NatPrimeCountDefs`) are checked by `decide +kernel`, without `native_decide`.
-/

@[expose] public section

open Finset Real

namespace NatPrimeCount

lemma tdiv_of_prime {n : ℕ} (hn : n.Prime) : ∀ f d, 2 ≤ d → tdiv n f d = true := by
  intro f
  induction f with
  | zero => intro d _; rfl
  | succ f ih =>
    intro d hd
    unfold tdiv
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      rcases hn.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · subst h; nlinarith
    · exact ih (d + 1) (by omega)

lemma primeK_of_prime {n : ℕ} (hn : n.Prime) : primeK n = true := by
  simp [primeK, hn.two_le, tdiv_of_prime hn]

lemma le_two_pow_kOf (n : ℕ) : ∀ f k, n ≤ 2 ^ (k + f) → n ≤ 2 ^ kOf f k n := by
  intro f
  induction f with
  | zero => intro k h; simpa [kOf] using h
  | succ f ih =>
    intro k h
    unfold kOf
    split_ifs with h1
    · exact h1
    · exact ih (k + 1) (by rw [show k + 1 + f = k + (f + 1) by omega]; exact h)

lemma sweepPi_sound : ∀ f n c, Nat.count Nat.Prime n ≤ c → sweepPi f n c = true →
    ∀ N, n ≤ N → N < n + f → 8 ≤ N → N ≤ 1024 →
      ∃ c k, Nat.count Nat.Prime (N + 1) ≤ c ∧ N ≤ 2 ^ k ∧ c * 7 * k ≤ 20 * N := by
  intro f
  induction f with
  | zero => intro n c _ _ N h1 h2; omega
  | succ f ih =>
    intro n c hc h N h1 h2 h8 hN
    simp only [sweepPi, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h0, hrest⟩ := h
    have hc' : Nat.count Nat.Prime (n + 1) ≤ c + (if primeK n then 1 else 0) := by
      rw [Nat.count_succ]
      split_ifs with hp hk
      · omega
      · exact absurd (primeK_of_prime hp) hk
      · omega
      · omega
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · refine ⟨_, kOf 10 0 n, hc', le_two_pow_kOf n 10 0 (by simpa using hN), ?_⟩
      rcases h0 with h0 | h0
      · omega
      · exact h0
    · exact ih (n + 1) _ hc' hrest N hlt (by omega) h8 hN

lemma sweepPi_ok : sweepPi 1001 0 0 = true := by decide +kernel

/-- `π(N) ≤ 2N/log N` for `8 ≤ N ≤ 1000`. -/
lemma primeCount_le_small {N : ℕ} (h8 : 8 ≤ N) (h1000 : N ≤ 1000) :
    (((N + 1).primesBelow.card : ℕ) : ℝ) ≤ 2 * N / Real.log N := by
  obtain ⟨c, k, hc, hk, hck⟩ :=
    sweepPi_sound 1001 0 0 (by simp) sweepPi_ok N (by omega) (by omega) h8 (by omega)
  rw [Nat.primesBelow_card_eq_primeCounting']
  have hN : (8 : ℝ) ≤ N := by exact_mod_cast h8
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogk : Real.log N ≤ k * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) (by exact_mod_cast hk)
  have h2 := Real.log_two_lt_d9
  have hc' : ((Nat.primeCounting' (N + 1) : ℕ) : ℝ) ≤ c := by exact_mod_cast hc
  have hck' : (c : ℝ) * 7 * k ≤ 20 * N := by exact_mod_cast hck
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [le_div_iff₀ hl]
  have : (c : ℝ) * Real.log N ≤ c * (k * 0.7) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  have hp0 : (0 : ℝ) ≤ Nat.primeCounting' (N + 1) := by positivity
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

/-- `e^{1/10} ≤ U/10⁸`. -/
lemma exp_tenth_le : Real.exp (1 / 10) ≤ (U10 : ℝ) / 10 ^ 8 := by
  have h : e10Ok = true := by decide +kernel
  unfold e10Ok at h
  split at h
  · rename_i p hp
    have := (BSCert.expPt_spec hp).2
    have h' : ((p.2 : ℚ) : ℝ) ≤ (((U10 : ℚ) / 10 ^ 8 : ℚ) : ℝ) := by
      exact_mod_cast of_decide_eq_true h
    push_cast at this h'
    linarith
  · cases h

/-- `U^j ≤ n · 10^(8j)` gives `log n ≥ j/10`. -/
lemma log_ge_of_pow {n j : ℕ} (hn : 1 ≤ n) (h : U10 ^ j ≤ n * 10 ^ (8 * j)) :
    (j : ℝ) / 10 ≤ Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le hn']
  have e : Real.exp ((j : ℝ) / 10) = Real.exp (1 / 10) ^ j := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e]
  have h1 : Real.exp (1 / 10) ^ j ≤ ((U10 : ℝ) / 10 ^ 8) ^ j :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_tenth_le j
  have h2 : ((U10 : ℝ) / 10 ^ 8) ^ j ≤ n := by
    rw [div_pow, div_le_iff₀ (by positivity), ← pow_mul]
    exact_mod_cast h
  linarith

lemma bump_spec (n : ℕ) : ∀ f j, U10 ^ j ≤ n * 10 ^ (8 * j) →
    j ≤ bump f n j ∧ U10 ^ bump f n j ≤ n * 10 ^ (8 * bump f n j) := by
  intro f
  induction f with
  | zero => intro j h; exact ⟨le_rfl, h⟩
  | succ f ih =>
    intro j h
    unfold bump
    split_ifs with h1
    · obtain ⟨a, b⟩ := ih (j + 1) h1
      exact ⟨by omega, b⟩
    · exact ⟨le_rfl, h⟩

/-- `1/log n ≤ ⌈10⁷/j⌉/10⁶` if `log n ≥ j/10`, `j ≥ 1`. -/
lemma inv_log_le {n j : ℕ} (hj : 1 ≤ j) (hl : (j : ℝ) / 10 ≤ Real.log n) :
    1 / Real.log n ≤ (((10 ^ 7 + j - 1) / j : ℕ) : ℝ) / 10 ^ 6 := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hl0 : 0 < Real.log n := lt_of_lt_of_le (by positivity) hl
  have hceil : (10 ^ 7 : ℝ) ≤ (((10 ^ 7 + j - 1) / j : ℕ) : ℝ) * j := by
    have : 10 ^ 7 ≤ (10 ^ 7 + j - 1) / j * j := by
      have h1 := Nat.div_add_mod (10 ^ 7 + j - 1) j
      have h2 := Nat.mod_lt (10 ^ 7 + j - 1) (show 0 < j by omega)
      rw [mul_comm] at h1
      omega
    exact_mod_cast this
  rw [div_le_div_iff₀ hl0 (by positivity), one_mul]
  nlinarith

lemma sweepS_sound : ∀ f n j (acc : ℕ), 1 ≤ j → 1 ≤ n → U10 ^ j ≤ n * 10 ^ (8 * j) →
    (acc : ℝ) / 10 ^ 6 + ∑ m ∈ Ico n (n + f), 1 / Real.log m ≤ (sweepS f n j acc : ℝ) / 10 ^ 6 := by
  intro f
  induction f with
  | zero => intro n j acc _ _ _; simp [sweepS]
  | succ f ih =>
    intro n j acc hj hn h
    obtain ⟨hj1, hj2⟩ := bump_spec n 80 j h
    have hn1 : 1 ≤ n + 1 := by omega
    have hmono : U10 ^ bump 80 n j ≤ (n + 1) * 10 ^ (8 * bump 80 n j) :=
      le_trans hj2 (Nat.mul_le_mul_right _ (by omega))
    have key := ih (n + 1) (bump 80 n j) (acc + (10 ^ 7 + bump 80 n j - 1) / bump 80 n j)
      (by omega) hn1 hmono
    have ht := inv_log_le (by omega : 1 ≤ bump 80 n j) (log_ge_of_pow hn hj2)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [sweepS, force_eq]
    rw [show n + (f + 1) = n + 1 + f by omega]
    push_cast at key ⊢
    linarith

lemma base_ok : (284 / 100 : ℚ) * (10 ^ 10 / 6931471803) + 142 / 100 * ((sumS : ℚ) / 10 ^ 6) ≤
    2000 * (100 / 695) := by decide +kernel

lemma log_1000_le : Real.log 1000 ≤ 695 / 100 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : ((1 : ℝ) + 695 / 100000) ^ 1000 ≤ Real.exp (695 / 100) := by
    have := pow_le_pow_left₀ (by norm_num) (Real.add_one_le_exp (695 / 100000 : ℝ)) 1000
    rw [← Real.exp_nat_mul, add_comm] at this
    convert this using 2
    norm_num
  have h2 : (1000 : ℝ) ≤ ((1 : ℝ) + 695 / 100000) ^ 1000 := by
    have : 1000 * 100000 ^ 1000 ≤ 100695 ^ 1000 := by decide +kernel
    have e : ((1 : ℝ) + 695 / 100000) = 100695 / 100000 := by norm_num
    rw [e, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast this
  exact h2.trans h1

/-- The comparison inequality at `N = 1000`. -/
lemma compare_base :
    2.84 / Real.log 2 + 1.42 * ∑ n ∈ (Icc 3 1000 : Finset ℕ), 1 / Real.log (n : ℝ) ≤
      2 * (1000 : ℕ) / Real.log (1000 : ℕ) := by
  have hS := sweepS_sound 998 3 1 0 le_rfl (by norm_num) (by unfold U10; norm_num)
  rw [show (Icc 3 1000 : Finset ℕ) = Ico 3 (3 + 998) by rfl]
  have hb := (Rat.cast_le (K := ℝ)).mpr base_ok
  push_cast at hb hS
  unfold sumS at hb
  have hl2 := Real.log_two_gt_d9
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have t1 : 2.84 / Real.log 2 ≤ 2.84 * (10 ^ 10 / 6931471803) := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  have hl1000 : 0 < Real.log (1000 : ℕ) := Real.log_pos (by norm_num)
  have t2 : 2000 * (100 / 695 : ℝ) ≤ 2 * (1000 : ℕ) / Real.log (1000 : ℕ) := by
    rw [le_div_iff₀ hl1000]
    have := log_1000_le
    push_cast at this ⊢
    nlinarith
  rw [zero_div, zero_add] at hS
  push_cast at t2 ⊢
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
