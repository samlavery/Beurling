module

public import RequestProject.Beurling.Construction.JitterRegular

/-!
# The elements of the realised system: rigid, absorbed and residual (proof of Lemma 4.8(ii))

In the proof of Lemma 4.8(ii) (§4, "Decomposition"), the elements of the system are split into
the rigid elements (`X₀`-smooth integers, `𝒟` with `1`), the absorbed set `A` (a set of real
values; one element of each value is the absorbed element) and the residual
elements `ℬ = ℕ_P \ (𝒟 ∪ A)`, counted with multiplicity. Here:

* `rigidElem h n`: the rigid element of value `n`, for `n` `X₀`-smooth (built from the rational
  primes of the realised system);
* `absElem h n`: for `n ∈ A`, an element of value `n` containing a jittered prime;
* `residual h`: the remaining elements;
* `N_eq_psi_add_countA_add` : `N(x) = Ψ(x) + #(A ∩ [1, x]) + #{e ∈ ℬ : val e ≤ x}`.
-/

@[expose] public section

open Set Finset Construction Target Rankin Absorbed

namespace Zeros48

variable {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}

/-- An element is *non-rigid* if it contains a placed (jittered) prime. -/
def NonRigid (h : RealisedOK M H U) (e : ℕ →₀ ℕ) : Prop :=
  ∃ j ∈ e.support, (h.equiv j).isRight

open Classical in
/-- The index of the rational prime `q < X₀` in the realised system (junk `0` otherwise). -/
noncomputable def ratIdx (h : RealisedOK M H U) (q : ℕ) : ℕ :=
  if hq : q.Prime ∧ q < X₀ then h.equiv.symm (Sum.inl ⟨q, hq⟩) else 0

/-- The rigid element of value `n` (for `n` `X₀`-smooth). -/
noncomputable def rigidElem (h : RealisedOK M H U) (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (ratIdx h) n.factorization

lemma val_rigidElem (h : RealisedOK M H U) {n : ℕ} (hn : n ∈ X₀.smoothNumbers) :
    (realisedSystem M H U).val (rigidElem h n) = n := by
  have hn0 : n ≠ 0 := (Nat.mem_smoothNumbers.mp hn).1
  unfold rigidElem BeurlingSystem.val
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
  have hc : ((n.factorization.prod fun x1 x2 => x1 ^ x2 : ℕ) : ℝ) =
      n.factorization.prod fun q m => (q : ℝ) ^ m := by
    unfold Finsupp.prod; push_cast; rfl
  rw [hc]
  refine Finsupp.prod_congr fun q hq => ?_
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqX : q < X₀ := (Nat.mem_smoothNumbers.mp hn).2 q
    (Nat.mem_primeFactorsList'.mpr ⟨hqp, Nat.dvd_of_mem_primeFactors hq, hn0⟩)
  have : (realisedSystem M H U).p (ratIdx h q) = q := by
    rw [realisedSystem_p h]
    simp only [ratIdx, dif_pos (And.intro hqp hqX), Equiv.apply_symm_apply, realisedVal]
  rw [this]

lemma not_nonRigid_rigidElem (h : RealisedOK M H U) {n : ℕ} (hn : n ∈ X₀.smoothNumbers) :
    ¬ NonRigid h (rigidElem h n) := by
  rintro ⟨j, hj, hr⟩
  have hn0 : n ≠ 0 := (Nat.mem_smoothNumbers.mp hn).1
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by simpa using hq)
  have hqX : q < X₀ := (Nat.mem_smoothNumbers.mp hn).2 q
    (Nat.mem_primeFactorsList'.mpr ⟨hqp, Nat.dvd_of_mem_primeFactors (by simpa using hq), hn0⟩)
  simp [ratIdx, dif_pos (And.intro hqp hqX)] at hr

/-- **Every absorbed `n` is the value of a non-rigid element**: the witness of `n ∈ A` has a latest
prime whose value is a jittered prime; replacing that prime by the jittered one keeps the value. -/
lemma exists_nonRigid_of_mem_realisedA (h : RealisedOK M H U) {n : ℝ}
    (hn : n ∈ realisedA M H U) :
    ∃ e, (realisedSystem M H U).val e = n ∧ NonRigid h e := by
  classical
  set P := realisedSystem M H U
  obtain ⟨hlog, e, hval, hjit, -⟩ := hn
  set src := realisedSrc M H U
  set j := latestIdxOf src e
  have hsupp : e.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    have : P.val 0 = 1 := by simp [BeurlingSystem.val]
    rw [this] at hval
    have hn1 : n = 1 := hval.symm
    rw [hn1, Real.log_one] at hlog
    norm_num at hlog
  have hj : j ∈ e.support := by
    simp only [j, latestIdxOf, dif_pos hsupp]
    exact (e.support.exists_max_image (keyOf src) hsupp).choose_spec.1
  obtain ⟨k, hk, hkv⟩ := hjit
  set j' := h.equiv.symm (Sum.inr ⟨k, hk⟩)
  have hpj' : P.p j' = P.p j := by
    rw [realisedSystem_p h j', Equiv.apply_symm_apply]
    exact hkv.symm
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hle : Finsupp.single j 1 ≤ e := by
    intro i
    by_cases hi : i = j
    · subst hi; simpa using hej
    · simp [Ne.symm hi]
  refine ⟨(e - Finsupp.single j 1) + Finsupp.single j' 1, ?_, j', ?_, ?_⟩
  · have he : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
    rw [P.val_add, P.val_single, pow_one, hpj', ← pow_one (P.p j), ← P.val_single, ← P.val_add,
      ← he, hval]
  · rw [Finsupp.mem_support_iff]
    simp
  · simp [j']

open Classical in
/-- For `n ∈ A`: a non-rigid element of value `n` (junk `0` otherwise). -/
noncomputable def absElem (h : RealisedOK M H U) (n : ℝ) : ℕ →₀ ℕ :=
  if hex : ∃ e, (realisedSystem M H U).val e = n ∧ NonRigid h e then hex.choose else 0

lemma absElem_spec (h : RealisedOK M H U) {n : ℝ} (hn : n ∈ realisedA M H U) :
    (realisedSystem M H U).val (absElem h n) = n ∧ NonRigid h (absElem h n) := by
  have hex := exists_nonRigid_of_mem_realisedA h hn
  simp only [absElem, dif_pos hex]
  exact hex.choose_spec

/-- **The residual elements `ℬ`**: neither a rigid element `rigidElem n` (`n` `X₀`-smooth) nor an
absorbed element `absElem n` (`n ∈ A`). -/
def residual (h : RealisedOK M H U) : Set (ℕ →₀ ℕ) :=
  {e | (∀ n ∈ X₀.smoothNumbers, e ≠ rigidElem h n) ∧ (∀ n ∈ realisedA M H U, e ≠ absElem h n)}

open Classical in
/-- The residual elements of value `≤ x`. -/
noncomputable def residualLe (h : RealisedOK M H U) (x : ℝ) : Finset (ℕ →₀ ℕ) :=
  ((realisedSystem M H U).elems x).filter (· ∈ residual h)

open Classical in
/-- **The element count splits**: `N(x) = Ψ(x) + #(A ∩ [1, x]) + #{e ∈ ℬ : val e ≤ x}`. -/
theorem N_eq_psi_add_countA_add (h : RealisedOK M H U) {x : ℝ} (hx : 0 ≤ x) :
    (realisedSystem M H U).N x =
      (smoothCount X₀ x : ℝ) + countA (realisedA M H U) x + ((residualLe h x).card : ℝ) := by
  classical
  set P := realisedSystem M H U
  set A := realisedA M H U
  set S := Nat.smoothNumbersUpTo ⌊x⌋₊ X₀
  have hfin := (realisedA_locFin M H U).finite_Icc 1 x
  set AS := hfin.toFinset
  have hcA : countA A x = (AS.card : ℝ) := by
    unfold countA
    rw [Set.ncard_eq_toFinset_card _ hfin]
  have hmemS : ∀ n ∈ S, n ∈ X₀.smoothNumbers ∧ (n : ℝ) ≤ x := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    exact ⟨hn.2, (Nat.cast_le.mpr hn.1).trans (Nat.floor_le hx)⟩
  have hmemA : ∀ n ∈ AS, n ∈ A ∧ (n : ℝ) ≤ x := by
    intro n hn
    simp only [AS, Set.Finite.mem_toFinset] at hn
    exact ⟨hn.1, hn.2.2⟩
  have hdecomp : P.elems x = (S.image (rigidElem h) ∪ AS.image (absElem h)) ∪ residualLe h x := by
    ext e
    simp only [Finset.mem_union, Finset.mem_image, residualLe, Finset.mem_filter,
      BeurlingSystem.mem_elems]
    constructor
    · intro he
      by_cases h1 : ∃ n ∈ X₀.smoothNumbers, e = rigidElem h n
      · obtain ⟨n, hn, rfl⟩ := h1
        refine Or.inl (Or.inl ⟨n, ?_, rfl⟩)
        rw [val_rigidElem h hn] at he
        rw [Nat.mem_smoothNumbersUpTo]
        exact ⟨Nat.le_floor he, hn⟩
      by_cases h2 : ∃ n ∈ A, e = absElem h n
      · obtain ⟨n, hn, rfl⟩ := h2
        refine Or.inl (Or.inr ⟨n, ?_, rfl⟩)
        have hn1 : 1 ≤ n := by
          rw [← (absElem_spec h hn).1]; exact P.one_le_val _
        rw [(absElem_spec h hn).1] at he
        simp only [AS, Set.Finite.mem_toFinset]
        exact ⟨hn, hn1, he⟩
      push_neg at h1 h2
      exact Or.inr ⟨he, h1, h2⟩
    · rintro ((⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) | ⟨he, -⟩)
      · obtain ⟨h1, h2⟩ := hmemS n hn
        rw [val_rigidElem h h1]; exact h2
      · obtain ⟨h1, h2⟩ := hmemA n hn
        rw [(absElem_spec h h1).1]; exact h2
      · exact he
  have hinjS : Set.InjOn (rigidElem h) S := by
    intro n hn m hm hnm
    have := congrArg P.val hnm
    rw [val_rigidElem h (hmemS n hn).1, val_rigidElem h (hmemS m hm).1] at this
    exact_mod_cast this
  have hinjA : Set.InjOn (absElem h) AS := by
    intro n hn m hm hnm
    have := congrArg P.val hnm
    rw [(absElem_spec h (hmemA n hn).1).1, (absElem_spec h (hmemA m hm).1).1] at this
    exact this
  have hd1 : Disjoint (S.image (rigidElem h)) (AS.image (absElem h)) := by
    rw [Finset.disjoint_left]
    rintro e he he'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨m, hm, hmn⟩ := Finset.mem_image.mp he'
    have := (absElem_spec h (hmemA m hm).1).2
    rw [hmn] at this
    exact not_nonRigid_rigidElem h (hmemS n hn).1 this
  have hd2 : Disjoint (S.image (rigidElem h) ∪ AS.image (absElem h)) (residualLe h x) := by
    rw [Finset.disjoint_left]
    rintro e he he'
    simp only [residualLe, Finset.mem_filter, residual, Set.mem_setOf_eq] at he'
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
      exact he'.2.1 n (hmemS n hn).1 rfl
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
      exact he'.2.2 n (hmemA n hn).1 rfl
  rw [BeurlingSystem.N_eq_card, hdecomp, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1, Finset.card_image_of_injOn hinjS,
    Finset.card_image_of_injOn hinjA, hcA]
  unfold smoothCount
  push_cast
  ring

end Zeros48

end
