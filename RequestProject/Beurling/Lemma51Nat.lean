module

public import RequestProject.Beurling.Lemma51NatBase
public import RequestProject.BSCert.Finite.CMCertSharp

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
