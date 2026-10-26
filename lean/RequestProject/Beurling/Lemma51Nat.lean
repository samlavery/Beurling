module

public import RequestProject.Beurling.MertensIV
public import RequestProject.BSCert.Finite.CMCert

/-!
# Lemma 5.1(ii)–(iv) for the rational primes up to `10⁷`, from `finite_checks.py`

`MertensIII` and `MertensIV` derive Lemma 5.1(iii) and (iv) from (ii) and the prime-power
constant, for any finite family of primes. For the rational primes in `[1, 10⁷]` both inputs are
certificates of `finite_checks.py`:

* line 2 (`BSCert.FiniteN.mertensS_sub_log_mem`): `-0.753 ≤ S(x) - log x ≤ 0` on `[1, 10⁷]`, with
  `S(x) = ∑_{n ≤ x} Λ(n)/n`;
* line 6 (`BSCert.FiniteN.sum_log_div_prime_le`): `∑_p log p/(p(p-1)) ≤ 0.75537`.

Here the prime-power part `S(x) - S_p(x) = ∑_{n ≤ x, n not prime} Λ(n)/n` is bounded by
`∑_{p ≤ x} log p/(p(p-1))` (`nonprime_vonMangoldt_le`), which gives:

* `lemma_5_1_iii_nat`: `-1.50837 ≤ ∑_{p ≤ x} log p/p - log x ≤ 0` for `1 ≤ x ≤ 10⁷`;
* `lemma_5_1_iv_nat`: `|∑_{y < p ≤ x} 1/p - log(log x/log y)| ≤ 1.50837/log y` for
  `2 ≤ y ≤ x ≤ 10⁷`.
-/

@[expose] public section

open Real Finset ArithmeticFunction Chebyshev

namespace Lemma51Nat

lemma geom_tail_le {p : ℝ} (hp : 2 ≤ p) (K : ℕ) :
    ∑ k ∈ Icc 2 K, 1 / p ^ k ≤ 1 / (p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have key : ∀ K : ℕ, 1 ≤ K → ∑ k ∈ Icc 2 K, 1 / p ^ k + 1 / (p ^ K * (p - 1)) =
      1 / (p * (p - 1)) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => simp
    | succ K hK ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ← ih]
      have : 0 < p ^ K := by positivity
      field_simp
      ring
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp; positivity
  · have := key K h
    have : 0 < 1 / (p ^ K * (p - 1)) := by positivity
    linarith

/-- The prime powers `p^k`, `k ≥ 2`, contribute at most `∑_{p ≤ M} log p/(p(p-1))` to
`∑_{n ≤ M} Λ(n)/n`. -/
theorem nonprime_vonMangoldt_le (M : ℕ) :
    ∑ n ∈ Ioc 0 M with ¬ n.Prime, Λ n / (n : ℝ) ≤
      ∑ p ∈ Ioc 0 M with p.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rcases Nat.eq_zero_or_pos M with rfl | h0
  · simp
  set g : ℕ → ℝ := fun n => if n.Prime then 0 else Real.log (n.minFac) / n with hg
  have e1 : ∑ n ∈ Ioc 0 M with ¬ n.Prime, Λ n / (n : ℝ) =
      ∑ n ∈ Ioc 0 ⌊(M : ℝ)⌋₊ with IsPrimePow n, g n := by
    rw [Nat.floor_natCast, sum_filter, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hp, hg, hp.isPrimePow]
    · simp only [hp, not_false_eq_true, if_true, hg, if_false, vonMangoldt_apply]
      split_ifs <;> simp
  rw [e1, sum_PrimePow_eq_sum_sum g (Nat.cast_nonneg M)]
  set K := ⌊Real.log (M : ℝ) / Real.log 2⌋₊
  have step : ∀ k ∈ Icc 1 K,
      ∑ p ∈ Ioc 0 ⌊(M : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime, g (p ^ k) ≤
      ∑ p ∈ Ioc 0 M with p.Prime, (if 2 ≤ k then Real.log p / (p : ℝ) ^ k else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hgk : ∀ p : ℕ, p.Prime →
        g (p ^ k) = if 2 ≤ k then Real.log p / (p : ℝ) ^ k else 0 := by
      intro p hp
      by_cases h2 : 2 ≤ k
      · have hnp : ¬ (p ^ k).Prime := Nat.Prime.not_prime_pow h2
        simp [hg, hnp, h2, Nat.Prime.pow_minFac hp (by omega : k ≠ 0)]
      · have : k = 1 := by omega
        subst this; simp [hg, hp]
    rw [sum_congr rfl (fun p hp => hgk p (mem_filter.mp hp).2)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, mem_Ioc] at hp ⊢
      refine ⟨⟨hp.1.1, le_trans hp.1.2 ?_⟩, hp.2⟩
      have : (M : ℝ) ^ ((1 : ℝ) / k) ≤ M := by
        apply Real.rpow_le_self_of_one_le (by exact_mod_cast h0)
        rw [div_le_one (by exact_mod_cast hk1)]; exact_mod_cast hk1
      have := Nat.floor_le_floor this
      simpa using this
    · intro p _ _
      split_ifs
      · positivity
      · rfl
  refine (sum_le_sum step).trans ?_
  rw [sum_comm]
  apply sum_le_sum
  intro p hp
  have hpp := (mem_filter.mp hp).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have e2 : ∑ k ∈ Icc 1 K, (if 2 ≤ k then Real.log p / (p : ℝ) ^ k else 0) =
      Real.log p * ∑ k ∈ Icc 2 K, 1 / (p : ℝ) ^ k := by
    rw [← sum_filter, mul_sum]
    have : (Icc 1 K).filter (fun k => 2 ≤ k) = Icc 2 K := by
      ext k; simp; omega
    rw [this]
    refine sum_congr rfl fun k _ => by ring
  rw [e2]
  have := geom_tail_le hp2 K
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  calc Real.log p * ∑ k ∈ Icc 2 K, 1 / (p : ℝ) ^ k ≤ Real.log p * (1 / (p * (p - 1))) := by
        gcongr
    _ = _ := by ring

/-- `S_p(x) = ∑_{p ≤ x} log p / p` over the rational primes. -/
noncomputable def primeLogSum (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / (p : ℝ)

/-- `S(x) = S_p(x) + ∑_{n ≤ x, n not prime} Λ(n)/n`. -/
lemma mertensS_eq (x : ℝ) : BSCert.FiniteN.mertensS x =
    primeLogSum x + ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, Λ n / (n : ℝ) := by
  unfold BSCert.FiniteN.mertensS primeLogSum
  have e : ∑ n ∈ range (⌊x⌋₊ + 1), Λ n / (n : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) := by
    rw [range_eq_Ico]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, div_zero, zero_add]
    rfl
  rw [e, ← Finset.sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  rw [vonMangoldt_apply_prime (mem_filter.mp hp).2]

/-- Finite prime sums of `log p/(p(p-1))` are at most `0.75537` (`finite_checks.py`, line 6). -/
lemma primePowerConst_le (M : ℕ) :
    ∑ p ∈ Ioc 0 M with p.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75537 := by
  obtain ⟨hs, hle⟩ := BSCert.FiniteN.sum_log_div_prime_le
  have hnn : ∀ q : Nat.Primes,
      0 ≤ Real.log (q : ℕ) / (((q : ℕ) : ℝ) * (((q : ℕ) : ℝ) - 1)) := by
    intro q
    have h2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.2.two_le
    have : 0 ≤ Real.log ((q : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    apply div_nonneg this; nlinarith
  have e := (Finset.sum_subtype_eq_sum_filter
    (f := fun p : ℕ => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) (p := Nat.Prime) (s := Ioc 0 M))
  rw [← e]
  calc _ ≤ _ := hs.sum_le_tsum _ (fun q _ => hnn q)
    _ ≤ 0.75537 := hle

/-- **Lemma 5.1(iii)** for the rational primes in `[1, 10⁷]`:
`-1.50837 ≤ ∑_{p ≤ x} log p / p - log x ≤ 0`. -/
theorem lemma_5_1_iii_nat {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 7) :
    -1.50837 ≤ primeLogSum x - Real.log x ∧ primeLogSum x - Real.log x ≤ 0 := by
  have h1 := BSCert.FiniteN.mertensS_sub_log_mem hx1 hx2
  have h2 := mertensS_eq x
  have h3 := nonprime_vonMangoldt_le ⌊x⌋₊
  have h4 := primePowerConst_le ⌊x⌋₊
  have h5 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, Λ n / (n : ℝ) :=
    sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  constructor <;> linarith

/-- **Lemma 5.1(iv)** for the rational primes in `[2, 10⁷]`: for `2 ≤ y ≤ x ≤ 10⁷`,
`|∑_{y < p ≤ x} 1/p - log(log x / log y)| ≤ 1.50837 / log y`. -/
theorem lemma_5_1_iv_nat {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) (hx : x ≤ 10 ^ 7) :
    |∑ p ∈ (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ y < p), 1 / (p : ℝ) -
      Real.log (Real.log x / Real.log y)| ≤ 1.50837 / Real.log y := by
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
  have hE : ∀ v ∈ Set.Icc y x, -1.50837 ≤ MertensIV.Sp P (fun i : ℕ => (i : ℝ)) v - Real.log v ∧
      MertensIV.Sp P (fun i : ℕ => (i : ℝ)) v - Real.log v ≤ 0 := by
    intro v hv
    rw [hSp v hv]
    exact lemma_5_1_iii_nat (by linarith [hv.1]) (hv.2.trans hx)
  have := MertensIV.mertens_iv P (fun i : ℕ => (i : ℝ)) hp hy hyx hE
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
  simpa using this

end Lemma51Nat
