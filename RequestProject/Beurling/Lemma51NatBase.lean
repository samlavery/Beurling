module

public import RequestProject.Beurling.MertensIV
public import RequestProject.BSCert.Finite.CMWeak

/-!
# Prime-power part of the Mertens sums for the rational primes

The parts of `Lemma51Nat` that do not depend on the certificates up to `10⁷`:

* `nonprime_vonMangoldt_le`: `S(x) - S_p(x) = ∑_{n ≤ x, n not prime} Λ(n)/n ≤ ∑_{p ≤ x} log p/(p(p-1))`;
* `primeLogSum`, `mertensS_eq`;
* `primePowerConst_le_weak`: `∑_{p ≤ M} log p/(p(p-1)) ≤ 0.75539` (from the kernel-checked
  `BSCert.FiniteN.sum_log_div_prime_le_weak`).

The statements with the paper's sharp constants on `[1, 10⁷]` are in `Lemma51Nat`.
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

/-- Finite prime sums of `log p/(p(p-1))` are at most `0.75539` (kernel-checked weak form of
`finite_checks.py`, line 6). -/
lemma primePowerConst_le_weak (M : ℕ) :
    ∑ p ∈ Ioc 0 M with p.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75539 := by
  obtain ⟨hs, hle⟩ := BSCert.FiniteN.sum_log_div_prime_le_weak
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
    _ ≤ 0.75539 := hle

end Lemma51Nat

end
