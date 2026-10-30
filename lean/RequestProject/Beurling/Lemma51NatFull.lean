module

public import RequestProject.Beurling.Lemma51NatBase
public import RequestProject.BSCert.Finite.ChebN

/-!
# Lemma 5.1(ii)–(iv) for the rational primes, for every `x`

Lemma 5.1(ii)–(iv) for the rational primes **for all `x ≥ 1`**, with the paper's constants:

* `lemma_5_1_ii_nat`: `-1.01 ≤ S(x) - log x ≤ 0.43`, `S(x) = ∑_{n ≤ x} Λ(n)/n`;
* `lemma_5_1_iii_nat_all`: `-1.77 ≤ ∑_{p ≤ x} log p/p - log x ≤ 0.43`;
* `lemma_5_1_iv_nat_all`: `|∑_{y<p≤x} 1/p - log(log x/log y)| ≤ 2.20/log y` for `2 ≤ y ≤ x`.

For `x ≤ 1000`, (ii) is the kernel-checked computation `BSCert.FiniteN.mertensS_sub_log_small`
(and the prime-power constant is `≤ 0.75539`, `primePowerConst_le_weak`). For `x ≥ 1000` (the
paper cites Rosser–Schoenfeld above `10⁷`) we use instead the argument the paper gives for the
Beurling system above `X₀⁻` (the identity (25) with `E₁ = 0`): from
`log N! = ∑_{d ≤ N} Λ(d) ⌊N/d⌋` (`chebL_eq_log_factorial`),

  `N S(N) - ψ(N) ≤ log N! ≤ N S(N)`,

and Stirling's bounds `N log N - N ≤ log N! ≤ N log N - N + 1 + (log N)/2` (Mathlib's
`Stirling.stirlingSeq`), together with `ψ(N) ≤ 1.42 N` (Lemma 5.1(i), `psi_le_one_point_four_two`).
-/

@[expose] public section

open Real Finset ArithmeticFunction Chebyshev Stirling

namespace Lemma51Nat

/-- Stirling's bounds `n log n - n ≤ log n! ≤ n log n - n + 1 + (log n)/2` for `n ≥ 1`. -/
lemma log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : stirlingSeq n =
      (n.factorial : ℝ) / (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := rfl
  have hD : 0 < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hlogD : Real.log (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) =
      Real.log 2 / 2 + Real.log n / 2 + (n * Real.log n - n) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
      Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity)]
    ring
  have hfac : (n.factorial : ℝ) =
      stirlingSeq n * (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [hS]; field_simp
  have hlo := sqrt_pi_le_stirlingSeq (n := n) (by omega)
  have hup : stirlingSeq n ≤ stirlingSeq 1 := by
    have := stirlingSeq'_antitone (show 0 ≤ n - 1 by omega)
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [stirlingSeq_one] at hup
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hspos : 0 < stirlingSeq n := by linarith
  have hlog_eq : Real.log (n.factorial : ℝ) = Real.log (stirlingSeq n) +
      (Real.log 2 / 2 + Real.log n / 2 + (n * Real.log n - n)) := by
    rw [hfac, Real.log_mul hspos.ne' hD.ne', hlogD]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  constructor
  · have : 0 ≤ Real.log (stirlingSeq n) := Real.log_nonneg (by linarith)
    rw [hlog_eq]; linarith
  · have h1 : Real.log (stirlingSeq n) ≤ Real.log (Real.exp 1 / Real.sqrt 2) :=
      Real.log_le_log hspos hup
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by norm_num)] at h1
    rw [hlog_eq]; linarith

/-- `S(N) = ∑_{n ≤ N} Λ(n)/n` at an integer. -/
lemma mertensS_natCast (N : ℕ) :
    BSCert.FiniteN.mertensS (N : ℝ) = ∑ n ∈ range (N + 1), Λ n / (n : ℝ) := by
  unfold BSCert.FiniteN.mertensS
  rw [Nat.floor_natCast]

lemma mertensS_floor (x : ℝ) :
    BSCert.FiniteN.mertensS x = BSCert.FiniteN.mertensS (⌊x⌋₊ : ℝ) := by
  unfold BSCert.FiniteN.mertensS
  rw [Nat.floor_natCast]

lemma psi_natCast_range (N : ℕ) : ψ (N : ℝ) = ∑ n ∈ range (N + 1), Λ n := by
  rw [BSCert.FiniteN.psi_natCast, range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [ArithmeticFunction.map_zero, zero_add]
  congr 1

/-- The Chebyshev identity with `E₁ = 0`: `N S(N) - ψ(N) ≤ log N! ≤ N S(N)`. -/
lemma chebL_bounds (N : ℕ) :
    (N : ℝ) * BSCert.FiniteN.mertensS (N : ℝ) - ψ (N : ℝ) ≤ Real.log (N.factorial : ℝ) ∧
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * BSCert.FiniteN.mertensS (N : ℝ) := by
  rw [← BSCert.FiniteN.chebL_eq_log_factorial, mertensS_natCast, psi_natCast_range,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold BSCert.FiniteN.chebL
  constructor
  · refine Finset.sum_le_sum fun d _ => ?_
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hΛ := vonMangoldt_nonneg (n := d)
    have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd']
      have := Nat.lt_div_mul_add (a := N) hd
      exact_mod_cast (by nlinarith [this] : N < (N / d + 1) * d)
    have : (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
    rw [this]; nlinarith
  · refine Finset.sum_le_sum fun d _ => ?_
    have hΛ := vonMangoldt_nonneg (n := d)
    have : (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le hΛ

/-- `log 10⁴ ≤ 10`. -/
lemma log_ten_thousand_le : Real.log (10000 : ℝ) ≤ 10 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (10000 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := by gcongr

/-- `log N ≤ N/10⁴ + 10` for `N > 0`. -/
lemma log_le_lin {N : ℝ} (hN : 0 < N) : Real.log N ≤ N / 10000 + 10 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < N / 10000 by positivity)
  rw [Real.log_div hN.ne' (by norm_num)] at h1
  have h2 := log_ten_thousand_le
  linarith

/-- **Lemma 5.1(ii)** for the rational primes, the range `x ≥ 10⁷`:
`-1.01 ≤ S(x) - log x ≤ 0.43`. -/
theorem lemma_5_1_ii_nat_large {x : ℝ} (hx : 10 ^ 7 ≤ x) :
    -1.01 ≤ BSCert.FiniteN.mertensS x - Real.log x ∧
      BSCert.FiniteN.mertensS x - Real.log x ≤ 0.43 := by
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 ≤ x := by linarith
  have hN1 : (10 : ℝ) ^ 7 ≤ N := by
    have : (10 ^ 7 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1' : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  rw [mertensS_floor x]
  set S := BSCert.FiniteN.mertensS (N : ℝ)
  obtain ⟨hc1, hc2⟩ := chebL_bounds N
  obtain ⟨hs1, hs2⟩ := log_factorial_bounds N hN1'
  have hψ := BSCert.FiniteN.psi_le_one_point_four_two (x := (N : ℝ)) hNpos.le
  have hlogx1 : Real.log N ≤ Real.log x := Real.log_le_log hNpos hNx
  have hlogx2 : Real.log x ≤ Real.log N + 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / N by positivity)
    rw [Real.log_div (by linarith) hNpos.ne'] at h
    have : x / N - 1 ≤ 1 / N := by
      rw [div_sub_one hNpos.ne', div_le_div_iff_of_pos_right hNpos]; linarith
    linarith
  have hlogN := log_le_lin hNpos
  constructor
  · -- `N log N - N ≤ log N! ≤ N S`, so `S ≥ log N - 1`.
    have hS : Real.log N - 1 ≤ S := by
      have : (N : ℝ) * (Real.log N - 1) ≤ N * S := by nlinarith
      exact le_of_mul_le_mul_left this hNpos
    have : 1 / (N : ℝ) ≤ 0.01 := by
      rw [div_le_iff₀ hNpos]; linarith
    linarith
  · -- `N S ≤ log N! + ψ(N) ≤ N log N - N + 1 + (log N)/2 + 1.42 N`.
    have hS : (N : ℝ) * S ≤ N * (Real.log N + 0.43) := by
      nlinarith
    have := le_of_mul_le_mul_left hS hNpos
    linarith

/-- **Lemma 5.1(ii)** for the rational primes, the range `x ≥ 1000`:
`-1.01 ≤ S(x) - log x ≤ 0.43`. -/
theorem lemma_5_1_ii_nat_mid {x : ℝ} (hx : 1000 ≤ x) :
    -1.01 ≤ BSCert.FiniteN.mertensS x - Real.log x ∧
      BSCert.FiniteN.mertensS x - Real.log x ≤ 0.43 := by
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 ≤ x := by linarith
  have hN1 : (1000 : ℝ) ≤ N := by
    have : (1000 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1' : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  rw [mertensS_floor x]
  set S := BSCert.FiniteN.mertensS (N : ℝ)
  obtain ⟨hc1, hc2⟩ := chebL_bounds N
  obtain ⟨hs1, hs2⟩ := log_factorial_bounds N hN1'
  have hψ := BSCert.FiniteN.psi_le_one_point_four_two (x := (N : ℝ)) hNpos.le
  have hlogx1 : Real.log N ≤ Real.log x := Real.log_le_log hNpos hNx
  have hlogx2 : Real.log x ≤ Real.log N + 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / N by positivity)
    rw [Real.log_div (by linarith) hNpos.ne'] at h
    have : x / N - 1 ≤ 1 / N := by
      rw [div_sub_one hNpos.ne', div_le_div_iff_of_pos_right hNpos]; linarith
    linarith
  have hlogN := log_le_lin hNpos
  constructor
  · -- `N log N - N ≤ log N! ≤ N S`, so `S ≥ log N - 1`.
    have hS : Real.log N - 1 ≤ S := by
      have : (N : ℝ) * (Real.log N - 1) ≤ N * S := by nlinarith
      exact le_of_mul_le_mul_left this hNpos
    have : 1 / (N : ℝ) ≤ 0.01 := by
      rw [div_le_iff₀ hNpos]; linarith
    linarith
  · -- `N S ≤ log N! + ψ(N) ≤ N log N - N + 1 + (log N)/2 + 1.42 N`.
    have hS : (N : ℝ) * S ≤ N * (Real.log N + 0.43) := by
      nlinarith
    have := le_of_mul_le_mul_left hS hNpos
    linarith

/-- **Lemma 5.1(ii)** for the rational primes, for all `x ≥ 1`:
`-1.01 ≤ S(x) - log x ≤ 0.43`, `S(x) = ∑_{n ≤ x} Λ(n)/n` (with `K_M = 1.01`). -/
theorem lemma_5_1_ii_nat {x : ℝ} (hx : 1 ≤ x) :
    -1.01 ≤ BSCert.FiniteN.mertensS x - Real.log x ∧
      BSCert.FiniteN.mertensS x - Real.log x ≤ 0.43 := by
  rcases le_total x 1000 with h | h
  · exact BSCert.FiniteN.mertensS_sub_log_small hx h
  · exact lemma_5_1_ii_nat_mid h

/-- **Lemma 5.1(iii)** for the rational primes, for all `x ≥ 1`:
`-1.77 ≤ ∑_{p ≤ x} log p / p - log x ≤ 0.43`. -/
theorem lemma_5_1_iii_nat_all {x : ℝ} (hx : 1 ≤ x) :
    -1.77 ≤ primeLogSum x - Real.log x ∧ primeLogSum x - Real.log x ≤ 0.43 := by
  have h1 := lemma_5_1_ii_nat hx
  have h2 := mertensS_eq x
  have h3 := nonprime_vonMangoldt_le ⌊x⌋₊
  have h4 := primePowerConst_le_weak ⌊x⌋₊
  have h5 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, Λ n / (n : ℝ) :=
    sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  constructor <;> linarith [h1.1, h1.2]

/-- **Lemma 5.1(iv)** for the rational primes, for all `2 ≤ y ≤ x`:
`|∑_{y < p ≤ x} 1/p - log(log x / log y)| ≤ 2.20 / log y` (`K' = 2.20`). -/
theorem lemma_5_1_iv_nat_all {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |∑ p ∈ (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ y < p), 1 / (p : ℝ) -
      Real.log (Real.log x / Real.log y)| ≤ 2.20 / Real.log y := by
  set P : Finset ℕ := (Ioc 0 ⌊x⌋₊).filter Nat.Prime with hP
  have hp : ∀ i ∈ P, 1 < ((i : ℕ) : ℝ) := fun i hi => by
    exact_mod_cast (mem_filter.mp hi).2.one_lt
  have hSp : ∀ v ∈ Set.Icc y x, MertensIV.Sp P (fun i : ℕ => (i : ℝ)) v = primeLogSum v := by
    intro v hv
    have hv0 : 0 ≤ v := by linarith [hv.1]
    unfold MertensIV.Sp primeLogSum
    rw [← sum_filter, hP, filter_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3, h4⟩
      exact ⟨⟨h1, Nat.le_floor h4⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : (p : ℝ) ≤ v := (Nat.le_floor_iff hv0).mp h2
      exact ⟨⟨h1, h2.trans (Nat.floor_le_floor hv.2)⟩, h3, h4⟩
  have hE : ∀ v ∈ Set.Icc y x, -1.77 ≤ MertensIV.Sp P (fun i : ℕ => (i : ℝ)) v - Real.log v ∧
      MertensIV.Sp P (fun i : ℕ => (i : ℝ)) v - Real.log v ≤ 0.43 := by
    intro v hv
    rw [hSp v hv]
    exact lemma_5_1_iii_nat_all (by linarith [hv.1])
  have := MertensIV.mertens_iv_explicit P (fun i : ℕ => (i : ℝ)) hp hy hyx hE
  have e : P.filter (fun i : ℕ => y < (i : ℝ) ∧ (i : ℝ) ≤ x) =
      (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ y < p) := by
    rw [hP, filter_filter]
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3, (Nat.le_floor_iff (by linarith)).mp h1.2⟩
  rw [e] at this
  exact this

end Lemma51Nat
