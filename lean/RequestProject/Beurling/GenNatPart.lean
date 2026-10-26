module

public import RequestProject.Beurling.GenIdentify
public import RequestProject.Beurling.Lemma51NatFull

/-!
# Below the identification height, `ψ_P`, `S_P` and `S_{p,P}` are the rational ones

* `BeurlingSystem.mertensS` : `S_P(x) = ∑_{p_j^{k+1} ≤ x} log p_j / p_j^{k+1}`;
* `BeurlingSystem.primesLe`, `BeurlingSystem.Sp` : `S_{p,P}(x) = ∑_{p_j ≤ x} log p_j / p_j`;
* `sum_pps_eq_vonMangoldt` : if the primes up to `x` are the rational ones, a weighted sum over
  the prime powers `≤ x` is the corresponding sum against `Λ`;
* `psi_eq_chebyshev`, `mertensS_eq_nat`, `Sp_eq_nat` : the three functions agree with those of
  `ℕ` at such `x`.
-/

@[expose] public section

open Finset ArithmeticFunction

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `S_P(x) = ∑_{p_j^{k+1} ≤ x} log p_j / p_j^{k+1}` (over the prime powers, with
multiplicity). -/
noncomputable def mertensS (x : ℝ) : ℝ :=
  ∑ jk ∈ P.pps x, Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1)

lemma finite_p_le (x : ℝ) : {j : ℕ | P.p j ≤ x}.Finite := by
  obtain ⟨J, -, hJ, -⟩ := P.exists_bounds x
  exact (Set.finite_lt_nat J).subset fun j hj => hJ j hj

/-- The indices `j` with `p_j ≤ x`. -/
noncomputable def primesLe (x : ℝ) : Finset ℕ := (P.finite_p_le x).toFinset

@[simp] lemma mem_primesLe {x : ℝ} {j : ℕ} : j ∈ P.primesLe x ↔ P.p j ≤ x := by
  simp [primesLe]

/-- `S_{p,P}(x) = ∑_{p_j ≤ x} log p_j / p_j`. -/
noncomputable def Sp (x : ℝ) : ℝ := ∑ j ∈ P.primesLe x, Real.log (P.p j) / P.p j

lemma factorization_qp_pow (j k : ℕ) :
    (qp j ^ (k + 1)).factorization = Finsupp.single (qp j) (k + 1) := by
  rw [Nat.Prime.factorization_pow (qp_prime j)]

/-- If every generalized prime `p_j` with `p_j ≤ x` or `qp j ≤ x` equals `qp j`, then
`∑_{p_j^{k+1} ≤ x} log p_j · F(p_j^{k+1}) = ∑_{n ≤ x} Λ(n) F(n)`. -/
theorem sum_pps_eq_vonMangoldt {x : ℝ}
    (hx : ∀ j, (P.p j ≤ x ∨ ((qp j : ℕ) : ℝ) ≤ x) → P.p j = qp j) (F : ℝ → ℝ) :
    ∑ jk ∈ P.pps x, Real.log (P.p jk.1) * F (P.p jk.1 ^ (jk.2 + 1)) =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * F n := by
  have hpj : ∀ jk ∈ P.pps x, P.p jk.1 = qp jk.1 := by
    intro jk hjk
    rw [mem_pps] at hjk
    apply hx; left
    calc P.p jk.1 = P.p jk.1 ^ 1 := (pow_one _).symm
      _ ≤ P.p jk.1 ^ (jk.2 + 1) := pow_le_pow_right₀ (P.one_lt _).le (by omega)
      _ ≤ x := hjk
  refine Finset.sum_bij_ne_zero (fun jk _ _ => qp jk.1 ^ (jk.2 + 1)) ?_ ?_ ?_ ?_
  · intro jk hjk _
    have h := hpj jk hjk
    rw [mem_pps, h] at hjk
    have hx0 : 0 ≤ x := le_trans (by positivity) hjk
    rw [mem_Ioc]
    refine ⟨pow_pos (qp_prime _).pos _, ?_⟩
    exact Nat.le_floor (by exact_mod_cast hjk)
  · intro a _ _ b _ _ hab
    have := congrArg Nat.factorization hab
    simp only [factorization_qp_pow] at this
    rw [Finsupp.single_eq_single_iff] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (qp_injective h1) (by omega)
    · omega
  · intro n hn hne
    have hΛ : Λ n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨r, m, hr, hm, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    set j := Nat.count Nat.Prime r
    have hqj : qp j = r := exists_qp_eq hr
    rw [mem_Ioc] at hn
    have hx0 : 0 ≤ x := by
      by_contra h; push_neg at h
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hn; omega
    have hrn : ((r ^ m : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hx0).mp hn.2
    have hr1 : (r : ℝ) ≤ x := by
      refine le_trans ?_ hrn
      exact_mod_cast Nat.le_self_pow (by omega) r
    have hpe : P.p j = qp j := hx j (Or.inr (by rw [hqj]; exact hr1))
    refine ⟨(j, m - 1), ?_, ?_, ?_⟩
    · rw [mem_pps]; simp only
      rw [hpe, hqj, Nat.sub_add_cancel hm]; exact_mod_cast hrn
    · intro h
      apply hne
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hr]
      simp only at h
      rw [hpe, hqj, Nat.sub_add_cancel hm] at h
      push_cast at h ⊢
      exact h
    · simp only; rw [hqj, Nat.sub_add_cancel hm]
  · intro jk hjk _
    have h := hpj jk hjk
    rw [h, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime (qp_prime _)]
    push_cast; rfl

/-- `ψ_P(x) = ψ(x)` when the primes up to `x` are the rational ones. -/
theorem psi_eq_chebyshev {x : ℝ}
    (hx : ∀ j, (P.p j ≤ x ∨ ((qp j : ℕ) : ℝ) ≤ x) → P.p j = qp j) :
    P.psi x = Chebyshev.psi x := by
  have := P.sum_pps_eq_vonMangoldt hx (fun _ => 1)
  simp only [mul_one] at this
  rw [psi_eq_sum, this]; rfl

/-- `S_P(x) = S(x)` when the primes up to `x` are the rational ones. -/
theorem mertensS_eq_nat {x : ℝ}
    (hx : ∀ j, (P.p j ≤ x ∨ ((qp j : ℕ) : ℝ) ≤ x) → P.p j = qp j) :
    P.mertensS x = BSCert.FiniteN.mertensS x := by
  have := P.sum_pps_eq_vonMangoldt hx (fun t => 1 / t)
  simp only [mul_one_div] at this
  rw [mertensS, this]
  unfold BSCert.FiniteN.mertensS
  rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [Nat.cast_zero, div_zero, zero_add]
  rfl

/-- `S_{p,P}(x) = ∑_{p ≤ x} log p / p` when the primes up to `x` are the rational ones. -/
theorem Sp_eq_nat {x : ℝ}
    (hx : ∀ j, (P.p j ≤ x ∨ ((qp j : ℕ) : ℝ) ≤ x) → P.p j = qp j) :
    P.Sp x = Lemma51Nat.primeLogSum x := by
  unfold Sp Lemma51Nat.primeLogSum
  refine Finset.sum_nbij' (fun j => qp j) (fun r => Nat.count Nat.Prime r) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_primesLe, mem_filter, mem_Ioc] at hj ⊢
    have h := hx j (Or.inl hj)
    rw [h] at hj
    have hx0 : 0 ≤ x := le_trans (by positivity) hj
    exact ⟨⟨(qp_prime j).pos, Nat.le_floor hj⟩, qp_prime j⟩
  · intro r hr
    simp only [mem_primesLe, mem_filter, mem_Ioc] at hr ⊢
    have hqr := exists_qp_eq hr.2
    have hx0 : 0 ≤ x := by
      by_contra h; push_neg at h
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hr; omega
    have hrx : (r : ℝ) ≤ x := (Nat.le_floor_iff hx0).mp hr.1.2
    rw [hx _ (Or.inr (by rw [hqr]; exact hrx)), hqr]
    exact hrx
  · intro j _
    exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime j
  · intro r hr
    simp only [mem_filter] at hr
    exact exists_qp_eq hr.2
  · intro j hj
    simp only [mem_primesLe] at hj
    rw [hx j (Or.inl hj)]

end BeurlingSystem

end
