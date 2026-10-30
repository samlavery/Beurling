module

public import RequestProject.Beurling.GenChebyshev

/-!
# A Beurling system with `N(v) = ⌊v⌋` below a height has the rational primes there

If `N_P(v) = ⌊v⌋` for all `v ≥ 1` in a down-closed set `D` (for the hypothesis (HBS), `D` is
`[1, X₀⁻) ∩ [1, z]`), then every generalized prime `p_j` in `D` is the `j`-th rational prime, and
so is every `p_j` whose rational counterpart lies in `D` (`p_eq_nth_prime`). This is the
statement "below `X₀⁻` the system is `ℕ`" used in the proof of Lemma 5.1.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

/-- The `j`-th rational prime. -/
noncomputable abbrev qp (j : ℕ) : ℕ := Nat.nth Nat.Prime j

lemma qp_prime (j : ℕ) : (qp j).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j

lemma qp_strictMono : StrictMono qp := Nat.nth_strictMono Nat.infinite_setOf_prime

lemma qp_injective : Function.Injective qp := qp_strictMono.injective

/-- Every prime is some `qp i`. -/
lemma exists_qp_eq {r : ℕ} (hr : r.Prime) : qp (Nat.count Nat.Prime r) = r := Nat.nth_count hr

/-- The rational integer `∏ qp_i ^ e_i` attached to the exponent vector `e`. -/
noncomputable def iota (e : ℕ →₀ ℕ) : ℕ := e.prod fun i k => qp i ^ k

lemma iota_eq_mapDomain (e : ℕ →₀ ℕ) :
    iota e = (Finsupp.mapDomain qp e).prod fun r k => r ^ k := by
  unfold iota
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

lemma factorization_iota (e : ℕ →₀ ℕ) : (iota e).factorization = Finsupp.mapDomain qp e := by
  rw [iota_eq_mapDomain]
  apply Nat.prod_pow_factorization_eq_self
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hr)
  exact qp_prime i

lemma iota_injective : Function.Injective iota := by
  intro e e' h
  have := congrArg Nat.factorization h
  rw [factorization_iota, factorization_iota] at this
  exact Finsupp.mapDomain_injective qp_injective this

lemma iota_pos (e : ℕ →₀ ℕ) : 0 < iota e := by
  unfold iota Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (qp_prime i).pos _

/-- If the support of `e` lies in `[0, j)`, then `iota e ≠ qp j`. -/
lemma iota_ne_qp {e : ℕ →₀ ℕ} {j : ℕ} (he : ∀ i ∈ e.support, i < j) : iota e ≠ qp j := by
  intro h
  have h1 := congrArg Nat.factorization h
  rw [factorization_iota, (qp_prime j).factorization, ← Finsupp.mapDomain_single] at h1
  have h2 := Finsupp.mapDomain_injective qp_injective h1
  have : j ∈ e.support := by rw [h2]; simp
  exact lt_irrefl _ (he j this)

/-- Every `n ≥ 1` whose prime factors are all `< qp j` is `iota e` for some `e` supported in
`[0, j)`. -/
lemma exists_iota_eq {n j : ℕ} (hn : n ≠ 0) (hf : ∀ r ∈ n.primeFactors, r < qp j) :
    ∃ e : ℕ →₀ ℕ, (∀ i ∈ e.support, i < j) ∧ iota e = n := by
  have hrange : (n.factorization.support : Set ℕ) ⊆ Set.range qp := by
    intro r hr
    have hr' : r.Prime := Nat.prime_of_mem_primeFactors (by simpa using hr)
    exact ⟨_, exists_qp_eq hr'⟩
  set e := Finsupp.comapDomain qp n.factorization qp_injective.injOn
  have hmap : Finsupp.mapDomain qp e = n.factorization :=
    Finsupp.mapDomain_comapDomain qp qp_injective _ hrange
  refine ⟨e, fun i hi => ?_, ?_⟩
  · have hi' : n.factorization (qp i) ≠ 0 := by
      rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at hi; exact hi
    have : qp i ∈ n.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hi'
    exact qp_strictMono.lt_iff_lt.mp (hf _ this)
  · rw [iota_eq_mapDomain, hmap]
    exact Nat.prod_factorization_pow_eq_self hn

variable (P : BeurlingSystem)

lemma val_eq_iota {e : ℕ →₀ ℕ} (h : ∀ i ∈ e.support, P.p i = qp i) :
    P.val e = (iota e : ℝ) := by
  unfold val iota Finsupp.prod
  push_cast
  exact Finset.prod_congr rfl fun i hi => by rw [h i hi]

/-- **Identification with the rational primes.** Let `D` be down-closed, and suppose
`N_P(v) = ⌊v⌋` for every `v ≥ 1` in `D`. If `p_j ∈ D` or `qp j ∈ D`, then `p_j = qp j`, the
`j`-th rational prime. -/
theorem p_eq_nth_prime {D : Set ℝ} (hD : ∀ u v, u ≤ v → v ∈ D → u ∈ D)
    (hN : ∀ v ∈ D, 1 ≤ v → P.N v = ⌊v⌋₊) :
    ∀ j, (P.p j ∈ D ∨ ((qp j : ℕ) : ℝ) ∈ D) → P.p j = qp j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro hjD
  -- the elements supported in `[0, j)` have the rational values
  have hval : ∀ e : ℕ →₀ ℕ, (∀ i ∈ e.support, i < j) → P.val e = (iota e : ℝ) := by
    intro e he
    apply P.val_eq_iota
    intro i hi
    have hij := he i hi
    rcases hjD with h | h
    · exact IH i hij (Or.inl (hD _ _ (P.mono hij.le) h))
    · exact IH i hij (Or.inr (hD _ _ (by exact_mod_cast (qp_strictMono hij).le) h))
  -- below `p_j`, only the first `j` primes occur
  have hsupp : ∀ t < P.p j, ∀ e ∈ P.elems t, ∀ i ∈ e.support, i < j := by
    intro t ht e he i hi
    by_contra hij; push_neg at hij
    rw [mem_elems] at he
    have h1 : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have : P.p j ≤ P.val e :=
      calc P.p j ≤ P.p i := P.mono hij
        _ = P.p i ^ 1 := (pow_one _).symm
        _ ≤ P.p i ^ e i := pow_le_pow_right₀ (P.one_lt i).le h1
        _ ≤ P.val e := P.pow_le_val e i
    linarith
  have hq2 : (2 : ℝ) ≤ (qp j : ℝ) := by exact_mod_cast (qp_prime j).two_le
  rcases lt_trichotomy (P.p j) (qp j) with hlt | heq | hgt
  · -- Case B: `p_j < qp j`; then `N(p_j) ≥ ⌊p_j⌋ + 1`.
    exfalso
    set t := P.p j
    have htD : t ∈ D := by
      rcases hjD with h | h
      · exact h
      · exact hD _ _ hlt.le h
    have ht1 : 1 ≤ t := (P.one_lt j).le
    have hNt := hN t htD ht1
    set V := (P.elems t).filter (fun e => ∀ i ∈ e.support, i < j)
    have hcardV : ⌊t⌋₊ ≤ V.card := by
      have hex : ∀ n ∈ Icc 1 ⌊t⌋₊, ∃ e : ℕ →₀ ℕ, (∀ i ∈ e.support, i < j) ∧ iota e = n := by
        intro n hn
        rw [mem_Icc] at hn
        refine exists_iota_eq (by omega) fun r hr => ?_
        have hrn : r ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hr)
        have : (n : ℝ) ≤ t := (Nat.le_floor_iff (by linarith)).mp hn.2
        have : (r : ℝ) < (qp j : ℝ) := by
          calc (r : ℝ) ≤ n := by exact_mod_cast hrn
            _ ≤ t := this
            _ < _ := hlt
        exact_mod_cast this
      choose! f hf1 hf2 using hex
      have : (Icc 1 ⌊t⌋₊).card ≤ V.card := by
        apply Finset.card_le_card_of_injOn f
        · intro n hn
          rw [Finset.mem_coe] at hn ⊢
          simp only [V, mem_filter, mem_elems]
          refine ⟨?_, hf1 n hn⟩
          rw [hval _ (hf1 n hn), hf2 n hn]
          exact (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp hn).2
        · intro a ha b hb hab
          have := congrArg iota hab
          try simp only at this
          rwa [hf2 a ha, hf2 b hb] at this
      simpa using this
    have hsingle : Finsupp.single j 1 ∈ P.elems t := by
      rw [mem_elems, val_single, pow_one]
    have hnot : Finsupp.single j 1 ∉ V := by
      simp only [V, mem_filter, not_and]
      intro _ h
      exact lt_irrefl j (h j (by simp))
    have hsub : insert (Finsupp.single j 1) V ⊆ P.elems t := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · exact hsingle
      · exact (mem_filter.mp he).1
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    rw [N_eq_card] at hNt
    have h2 : ((P.elems t).card : ℝ) ≥ ⌊t⌋₊ + 1 := by exact_mod_cast (by omega :
      (P.elems t).card ≥ ⌊t⌋₊ + 1)
    rw [hNt] at h2
    linarith
  · exact heq
  · -- Case A: `qp j < p_j`; then `N(qp j) ≤ qp j - 1`.
    exfalso
    set t : ℝ := (qp j : ℝ)
    have htD : t ∈ D := by
      rcases hjD with h | h
      · exact hD _ _ hgt.le h
      · exact h
    have hNt := hN t htD (by linarith)
    have hfl : ⌊t⌋₊ = qp j := Nat.floor_natCast _
    rw [hfl, N_eq_card] at hNt
    have hle : (P.elems t).card ≤ ((Icc 1 (qp j)).erase (qp j)).card := by
      apply Finset.card_le_card_of_injOn iota
      · intro e he
        rw [Finset.mem_coe] at he ⊢
        have hs := hsupp t hgt e he
        have hv := hval e hs
        rw [mem_elems, hv] at he
        have h1 : iota e ≤ qp j := by
          have he' : ((iota e : ℕ) : ℝ) ≤ ((qp j : ℕ) : ℝ) := he
          exact_mod_cast he'
        simp only [mem_erase, mem_Icc]
        exact ⟨iota_ne_qp hs, iota_pos e, h1⟩
      · intro a _ b _ hab; exact iota_injective hab
    rw [card_erase_of_mem (by simp [(qp_prime j).one_le]), Nat.card_Icc] at hle
    have : ((P.elems t).card : ℝ) ≤ (qp j : ℝ) - 1 := by
      have h2 := (qp_prime j).two_le
      have : (P.elems t).card ≤ qp j - 1 := by omega
      have h3 : ((qp j - 1 : ℕ) : ℝ) = (qp j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [← h3]; exact_mod_cast this
    linarith

end BeurlingSystem

end
