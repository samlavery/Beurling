module

public import RequestProject.Beurling.Construction.HBSLocal

/-!
# The realised system below `X₀⁻ = X₀ - H(X₀)/2`

Every jittered prime is `≥ X₀⁻ = X₀ - H(X₀)/2`, so below `X₀⁻` the realised system consists of the
rational primes only. Here this is turned into the two facts used by (HBS):

* `realised_p_eq_qp`: if `p_j < X₀⁻` or `q_j < X₀⁻` (`q_j` the `j`-th rational prime), then
  `p_j = q_j`;
* `realised_floor_eq`: `N(v) = ⌊v⌋` for `1 ≤ v < X₀⁻`.
-/

@[expose] public section

open Set BeurlingSystem CaplLink

namespace Construction

/-- For a monotone sequence with finite sublevel sets, `f j ≤ t ↔ j < #{i : f i ≤ t}`. -/
lemma le_iff_lt_ncard_of_monotone {f : ℕ → ℝ} (hf : Monotone f) {t : ℝ}
    (hfin : {j | f j ≤ t}.Finite) (j : ℕ) : f j ≤ t ↔ j < {i | f i ≤ t}.ncard := by
  constructor
  · intro hj
    have hsub : Finset.range (j + 1) ⊆ hfin.toFinset := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finite.mem_toFinset, mem_setOf_eq]
      exact (hf (by omega)).trans hj
    have := Finset.card_le_card hsub
    rw [Finset.card_range, ← ncard_eq_toFinset_card _ hfin] at this
    omega
  · intro hj
    by_contra hlt
    push_neg at hlt
    have hsub : hfin.toFinset ⊆ Finset.range j := by
      intro i hi
      rw [Finite.mem_toFinset, mem_setOf_eq] at hi
      rw [Finset.mem_range]
      by_contra hij
      push_neg at hij
      exact absurd ((hf hij).trans hi) (not_le.mpr hlt)
    have := Finset.card_le_card hsub
    rw [Finset.card_range, ← ncard_eq_toFinset_card _ hfin] at this
    omega

/-- The primes `≤ t` are finite in number. -/
lemma finite_primes_le (t : ℝ) : {q : ℕ | q.Prime ∧ (q : ℝ) ≤ t}.Finite :=
  (Set.finite_Iic ⌊t⌋₊).subset (fun q hq => by
    simp only [mem_Iic]
    exact Nat.le_floor hq.2)

/-- The number of rational primes `q_i ≤ t` is the number of primes `≤ t`. -/
lemma ncard_qp_le (t : ℝ) :
    {i | (qp i : ℝ) ≤ t}.ncard = {q : ℕ | q.Prime ∧ (q : ℝ) ≤ t}.ncard := by
  apply Set.ncard_congr (fun i _ => qp i)
  · intro i hi; exact ⟨qp_prime i, hi⟩
  · intro i j _ _ h; exact qp_injective h
  · intro q hq
    exact ⟨Nat.count Nat.Prime q, by
      show ((qp (Nat.count Nat.Prime q) : ℕ) : ℝ) ≤ t
      rw [exists_qp_eq hq.1]; exact hq.2, exists_qp_eq hq.1⟩

lemma finite_qp_le (t : ℝ) : {i | (qp i : ℝ) ≤ t}.Finite :=
  (Set.finite_Iic ⌊t⌋₊).subset (fun i hi => by
    simp only [mem_Iic, mem_setOf_eq] at hi ⊢
    have h1 : i ≤ qp i := qp_strictMono.id_le i
    exact h1.trans (Nat.le_floor hi))

section Realised

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- The rational prime of a realised index (`0` for a jittered one). -/
def ratVal : RealisedIdx M → ℕ
  | Sum.inl p => p.1
  | Sum.inr _ => 0

/-- Every jittered prime is `≥ X₀⁻ = X₀ - H(X₀)/2`. -/
lemma realisedVal_inr_ge (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (k : {k : ℕ // placedAt M k}) :
    (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ realisedVal M (capH X₀) U (Sum.inr k) := by
  have h := GreedyRun.jittered_ge_of_floor ⟨M, capH X₀, U, hTlow⟩ hU (capH_nonneg X₀)
    (fun s hs => JitterFloor.capH_floor (Nat.cast_nonneg _) hX hs)
  exact h _ ⟨k.1, k.2, rfl⟩

/-- Below `X₀⁻`, a realised prime is rational. -/
lemma realised_rat_of_lt (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {i : RealisedIdx M}
    (hi : realisedVal M (capH X₀) U i < (X₀ : ℝ) - capH X₀ X₀ / 2) :
    ∃ p : {p : ℕ // p.Prime ∧ p < X₀}, i = Sum.inl p := by
  cases i with
  | inl p => exact ⟨p, rfl⟩
  | inr k => exact absurd (realisedVal_inr_ge hU hX hTlow k) (not_le.mpr hi)

variable (h : RealisedOK M (capH X₀) U)
include h

/-- The number of realised primes `≤ t` equals the number of rational primes `≤ t`, for
`t < X₀⁻`. -/
lemma realised_ncard_le (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {t : ℝ} (ht : t < (X₀ : ℝ) - capH X₀ X₀ / 2) :
    {j | (realisedSystem M (capH X₀) U).p j ≤ t}.ncard =
      {q : ℕ | q.Prime ∧ (q : ℝ) ≤ t}.ncard := by
  have hH0 := capH_nonneg (X₀ : ℝ) (X₀ : ℝ)
  apply Set.ncard_congr (fun j _ => ratVal (h.equiv j))
  · intro j hj
    simp only [mem_setOf_eq, realisedSystem_p h] at hj
    obtain ⟨p, hp⟩ := realised_rat_of_lt hU hX hTlow (lt_of_le_of_lt hj ht)
    rw [hp] at hj ⊢
    exact ⟨p.2.1, hj⟩
  · intro i j hi hj hij
    simp only [mem_setOf_eq, realisedSystem_p h] at hi hj
    obtain ⟨p, hp⟩ := realised_rat_of_lt hU hX hTlow (lt_of_le_of_lt hi ht)
    obtain ⟨q, hq⟩ := realised_rat_of_lt hU hX hTlow (lt_of_le_of_lt hj ht)
    simp only [hp, hq, ratVal] at hij
    have : h.equiv i = h.equiv j := by rw [hp, hq, Subtype.ext hij]
    exact h.equiv.injective this
  · intro q hq
    have hqX : q < X₀ := by
      have : (q : ℝ) < X₀ := by linarith [hq.2]
      exact_mod_cast this
    refine ⟨h.equiv.symm (Sum.inl ⟨q, hq.1, hqX⟩), ?_, ?_⟩
    · simp only [mem_setOf_eq, realisedSystem_p h, Equiv.apply_symm_apply]
      exact hq.2
    · simp [ratVal]

/-- **Below `X₀⁻` the realised system is `ℕ`**: if `p_j < X₀⁻` or `q_j < X₀⁻`, then `p_j = q_j`. -/
theorem realised_p_eq_qp (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (j : ℕ)
    (hj : (realisedSystem M (capH X₀) U).p j < (X₀ : ℝ) - capH X₀ X₀ / 2 ∨
      (qp j : ℝ) < (X₀ : ℝ) - capH X₀ X₀ / 2) :
    (realisedSystem M (capH X₀) U).p j = qp j := by
  set P := realisedSystem M (capH X₀) U
  -- for `t < X₀⁻`: `p_j ≤ t ↔ q_j ≤ t`
  have key : ∀ t < (X₀ : ℝ) - capH X₀ X₀ / 2, (P.p j ≤ t ↔ (qp j : ℝ) ≤ t) := by
    intro t ht
    rw [le_iff_lt_ncard_of_monotone P.mono (P.finite_p_le t),
      le_iff_lt_ncard_of_monotone (fun a b hab => by exact_mod_cast qp_strictMono.monotone hab)
        (finite_qp_le t),
      realised_ncard_le h hU hX hTlow ht, ncard_qp_le]
  rcases hj with hj | hj
  · have h1 : (qp j : ℝ) ≤ P.p j := (key _ hj).mp le_rfl
    have h2 : P.p j ≤ qp j := (key _ (lt_of_le_of_lt h1 hj)).mpr le_rfl
    linarith
  · have h1 : P.p j ≤ qp j := (key _ hj).mpr le_rfl
    have h2 : (qp j : ℝ) ≤ P.p j := (key _ (lt_of_le_of_lt h1 hj)).mp le_rfl
    linarith

/-- **`N(v) = ⌊v⌋` below `X₀⁻`** for the realised system. -/
theorem realised_floor_eq (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {v : ℝ} (hv1 : 1 ≤ v)
    (hv : v < (X₀ : ℝ) - capH X₀ X₀ / 2) :
    (realisedSystem M (capH X₀) U).N v = ⌊v⌋₊ := by
  classical
  set P := realisedSystem M (capH X₀) U
  have hpq := realised_p_eq_qp h hU hX hTlow
  rw [N_eq_card]
  congr 1
  -- `iota` is a bijection from the elements `≤ v` onto `[1, ⌊v⌋]`
  have hsupp : ∀ e ∈ P.elems v, ∀ i ∈ e.support, P.p i = qp i := by
    intro e he i hi
    rw [mem_elems] at he
    have h1 : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have : P.p i ≤ P.val e :=
      calc P.p i = P.p i ^ 1 := (pow_one _).symm
        _ ≤ P.p i ^ e i := pow_le_pow_right₀ (P.one_lt i).le h1
        _ ≤ P.val e := P.pow_le_val e i
    exact hpq i (Or.inl (by linarith))
  rw [show ⌊v⌋₊ = (Finset.Icc 1 ⌊v⌋₊).card by simp]
  apply Finset.card_bij (fun e _ => iota e)
  · intro e he
    have hval := P.val_eq_iota (hsupp e he)
    have hle : (iota e : ℝ) ≤ v := by rw [← hval]; exact (mem_elems P).mp he
    rw [Finset.mem_Icc]
    exact ⟨iota_pos e, Nat.le_floor hle⟩
  · intro e _ e' _ hee
    exact iota_injective hee
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨e, -, he⟩ := exists_iota_eq (j := n) hn0 (fun r hr => by
      have hrn : r ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hr)
      have : n + 2 ≤ qp n := Nat.add_two_le_nth_prime n
      omega)
    have hnv : (n : ℝ) ≤ v := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by linarith))
    have hsupp' : ∀ i ∈ e.support, P.p i = qp i := by
      intro i hi
      apply hpq i (Or.inr _)
      have hdvd : qp i ∈ n.primeFactors := by
        rw [← he, ← Nat.support_factorization, factorization_iota]
        rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply_of_injective qp_injective]
        exact Finsupp.mem_support_iff.mp hi
      have : qp i ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hdvd)
      have : (qp i : ℝ) ≤ n := by exact_mod_cast this
      linarith
    refine ⟨e, ?_, he⟩
    rw [mem_elems, P.val_eq_iota hsupp', he]
    exact hnv

end Realised

end Construction

end
