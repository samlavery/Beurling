module

public import RequestProject.Beurling.Defs
public import RequestProject.Beurling.AbsorbedPart

/-!
# Rankin's bound for a Beurling system (Lemma 6.26, steps (iii) and (v))

For a discrete Beurling system `P` and `z > 0`, the `z`-smooth elements are the exponent vectors
supported on the primes `p_j < z`, and `Ψ_N(Y, z)` is the number of them with value `≤ Y`
(with multiplicity). Rankin's method gives, for every `σ > 0`,

  `Ψ_N(Y, z) ≤ Y^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}`     (`smoothCountN_le_rankin`).

Consequently, if every element `n ≥ 1` of a set `A ⊆ ℕ` is the value of a `z`-smooth element of
`N` (step (i) of Lemma 6.26: every prime of `n ∈ A` is `< 2y`), then
`#(A ∩ [1, x]) ≤ x^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}` (`countA_le_rankin`). What remains of the
Rankin bound of Lemma 6.26 is the numerical estimate of the product for the realised primes.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The primes below `z` form a finite set. -/
lemma finite_primes_lt (z : ℝ) : {j : ℕ | P.p j < z}.Finite := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (P.tendsto.eventually_ge_atTop z)
  refine (Set.finite_lt_nat J).subset fun j hj => ?_
  simp only [Set.mem_setOf_eq] at hj ⊢
  by_contra h
  exact absurd (hJ j (not_lt.mp h)) (not_le.mpr hj)

/-- The indices of the primes `p_j < z`. -/
noncomputable def primesLt (z : ℝ) : Finset ℕ := (P.finite_primes_lt z).toFinset

lemma mem_primesLt {z : ℝ} {j : ℕ} : j ∈ P.primesLt z ↔ P.p j < z := by
  simp [primesLt]

/-- The `z`-smooth elements: exponent vectors supported on the primes `p_j < z`. -/
def smoothElems (z : ℝ) : Set (ℕ →₀ ℕ) := {e | ∀ j ∈ e.support, P.p j < z}

/-- `Ψ_N(Y, z)`: the number of `z`-smooth elements of value `≤ Y`. -/
noncomputable def smoothCountN (Y z : ℝ) : ℝ := ({e | e ∈ P.smoothElems z ∧ P.val e ≤ Y}.ncard : ℝ)

/-- The Rankin product `∏_{p_j < z} (1 - p_j^{-σ})^{-1}`. -/
noncomputable def rankinProd (z σ : ℝ) : ℝ := ∏ j ∈ P.primesLt z, (1 - P.p j ^ (-σ))⁻¹

lemma val_eq_prod {z : ℝ} {e : ℕ →₀ ℕ} (he : e ∈ P.smoothElems z) :
    P.val e = ∏ j ∈ P.primesLt z, P.p j ^ e j := by
  unfold val
  exact Finsupp.prod_of_support_subset e (fun j hj => P.mem_primesLt.mpr (he j hj)) _
    (fun _ _ => pow_zero _)

lemma one_le_prod_real (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) h
  simpa using this

lemma one_le_val (e : ℕ →₀ ℕ) : 1 ≤ P.val e := by
  unfold val Finsupp.prod
  exact one_le_prod_real _ _ fun j _ => one_le_pow₀ (P.one_lt j).le

lemma pow_le_val (e : ℕ →₀ ℕ) (j : ℕ) : P.p j ^ e j ≤ P.val e := by
  by_cases hj : j ∈ e.support
  · unfold val Finsupp.prod
    rw [← Finset.mul_prod_erase _ _ hj]
    exact le_mul_of_one_le_right (pow_nonneg (by linarith [P.one_lt j]) _)
      (one_le_prod_real _ _ fun i _ => one_le_pow₀ (P.one_lt i).le)
  · rw [Finsupp.notMem_support_iff.mp hj, pow_zero]; exact P.one_le_val e

/-- **Rankin's bound** for a Beurling system: `Ψ_N(Y, z) ≤ Y^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}`. -/
theorem smoothCountN_le_rankin {σ : ℝ} (hσ : 0 < σ) {Y : ℝ} (hY : 0 ≤ Y) (z : ℝ) :
    P.smoothCountN Y z ≤ Y ^ σ * P.rankinProd z σ := by
  set T := P.primesLt z
  set E := {e | e ∈ P.smoothElems z ∧ P.val e ≤ Y}
  -- the exponents are bounded
  have hp0 := P.one_lt 0
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt Y hp0
  have hexp : ∀ e ∈ E, ∀ j, e j < K := by
    intro e he j
    by_contra h
    push_neg at h
    have h1 : P.p 0 ^ K ≤ P.p j ^ e j :=
      (pow_le_pow_right₀ hp0.le h).trans (pow_le_pow_left₀ (by linarith) (P.mono (Nat.zero_le j)) _)
    linarith [P.pow_le_val e j, he.2]
  -- the map to exponent tuples on `T`
  let φ : (ℕ →₀ ℕ) → (T → ℕ) := fun e j => e j
  have hφinj : Set.InjOn φ E := by
    intro e he f hf hef
    ext j
    by_cases hj : j ∈ T
    · exact congrFun hef ⟨j, hj⟩
    · have hej : e j = 0 := by
        by_contra h
        exact hj (P.mem_primesLt.mpr (he.1 j (Finsupp.mem_support_iff.mpr h)))
      have hfj : f j = 0 := by
        by_contra h
        exact hj (P.mem_primesLt.mpr (hf.1 j (Finsupp.mem_support_iff.mpr h)))
      rw [hej, hfj]
  set B : Finset (T → ℕ) := Fintype.piFinset fun _ => range K
  have hmaps : Set.MapsTo φ E B := by
    intro e he
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    exact fun j => Finset.mem_range.mpr (hexp e he j)
  have hEfin : E.Finite := Set.Finite.of_finite_image
    ((B.finite_toSet).subset (Set.image_subset_iff.mpr hmaps)) hφinj
  set Ef := hEfin.toFinset
  have hcard : P.smoothCountN Y z = (Ef.card : ℝ) := by
    unfold smoothCountN
    rw [Set.ncard_eq_toFinset_card E hEfin]
  set q : T → ℝ := fun j => P.p j ^ (-σ)
  have hq0 : ∀ j, 0 ≤ q j := fun j => Real.rpow_nonneg (by linarith [P.one_lt j]) _
  have hq1 : ∀ j, q j < 1 := fun j =>
    Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)
  -- each element contributes `(Y / n)^σ ≥ 1`
  have hterm : ∀ e ∈ Ef, (1 : ℝ) ≤ Y ^ σ * ∏ j : T, q j ^ (φ e j) := by
    intro e he
    rw [Set.Finite.mem_toFinset] at he
    have hv1 := P.one_le_val e
    have hprod : ∏ j : T, q j ^ (φ e j) = P.val e ^ (-σ) := by
      rw [P.val_eq_prod he.1, ← Real.finset_prod_rpow _ _ (fun j _ => by
        have := P.one_lt j; positivity)]
      rw [← Finset.prod_coe_sort T]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [q, φ]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [P.one_lt j]),
        ← Real.rpow_mul (by linarith [P.one_lt j]), mul_comm]
    rw [hprod, Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
      one_mul]
    exact Real.rpow_le_rpow (by linarith) he.2 hσ.le
  have hYσ : 0 ≤ Y ^ σ := Real.rpow_nonneg hY _
  set g : (T → ℕ) → ℝ := fun f => ∏ j : T, q j ^ (f j)
  have hg0 : ∀ f, 0 ≤ g f := fun f => Finset.prod_nonneg fun j _ => pow_nonneg (hq0 j) _
  have himage : Ef.image φ ⊆ B := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    rw [Set.Finite.mem_toFinset] at he
    exact hmaps he
  have hinj' : Set.InjOn φ Ef := fun e he f hf h =>
    hφinj ((Set.Finite.mem_toFinset hEfin).mp he) ((Set.Finite.mem_toFinset hEfin).mp hf) h
  calc P.smoothCountN Y z = ∑ e ∈ Ef, (1 : ℝ) := by rw [hcard]; simp
    _ ≤ ∑ e ∈ Ef, Y ^ σ * g (φ e) := Finset.sum_le_sum hterm
    _ = Y ^ σ * ∑ f ∈ Ef.image φ, g f := by
        rw [← Finset.mul_sum, Finset.sum_image fun e he f hf h => hinj' he hf h]
    _ ≤ Y ^ σ * ∑ f ∈ B, g f :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg himage
          fun f _ _ => hg0 f) hYσ
    _ = Y ^ σ * ∏ j : T, ∑ n ∈ range K, q j ^ n := by
        rw [Finset.prod_univ_sum]
    _ ≤ Y ^ σ * ∏ j : T, (1 - q j)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
          (fun j _ => Finset.sum_nonneg fun n _ => pow_nonneg (hq0 j) n) fun j _ => ?_) hYσ
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) (hq0 j) (hq1 j)
        rw [Finset.range_eq_Ico]
        simpa [one_div] using this
    _ = Y ^ σ * P.rankinProd z σ := by
        unfold rankinProd
        rw [← Finset.prod_coe_sort (P.primesLt z)]

/-- The `z`-smooth elements of value `≤ Y` form a finite set. -/
lemma finite_smooth_le (Y z : ℝ) : {e | e ∈ P.smoothElems z ∧ P.val e ≤ Y}.Finite := by
  set T := P.primesLt z
  set E := {e | e ∈ P.smoothElems z ∧ P.val e ≤ Y}
  have hp0 := P.one_lt 0
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt Y hp0
  have hexp : ∀ e ∈ E, ∀ j, e j < K := by
    intro e he j
    by_contra h
    push_neg at h
    have h1 : P.p 0 ^ K ≤ P.p j ^ e j :=
      (pow_le_pow_right₀ hp0.le h).trans (pow_le_pow_left₀ (by linarith) (P.mono (Nat.zero_le j)) _)
    linarith [P.pow_le_val e j, he.2]
  let φ : (ℕ →₀ ℕ) → (T → ℕ) := fun e j => e j
  have hφinj : Set.InjOn φ E := by
    intro e he f hf hef
    ext j
    by_cases hj : j ∈ T
    · exact congrFun hef ⟨j, hj⟩
    · have hej : e j = 0 := by
        by_contra h
        exact hj (P.mem_primesLt.mpr (he.1 j (Finsupp.mem_support_iff.mpr h)))
      have hfj : f j = 0 := by
        by_contra h
        exact hj (P.mem_primesLt.mpr (hf.1 j (Finsupp.mem_support_iff.mpr h)))
      rw [hej, hfj]
  set B : Finset (T → ℕ) := Fintype.piFinset fun _ => range K
  have hmaps : Set.MapsTo φ E B := by
    intro e he
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    exact fun j => Finset.mem_range.mpr (hexp e he j)
  exact Set.Finite.of_finite_image
    ((B.finite_toSet).subset (Set.image_subset_iff.mpr hmaps)) hφinj

/-- **Rankin's bound for a set of smooth elements** (Lemma 6.26, steps (iii) and (v)): if every
`n ∈ A` is `≥ 1` and is the value of a `z`-smooth element of `N`, then
`#(A ∩ [1, x]) ≤ x^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}`. -/
theorem countA_le_rankin {A : Set ℕ} {z : ℝ}
    (hA : ∀ n ∈ A, 1 ≤ n ∧ ∃ e ∈ P.smoothElems z, P.val e = n) {σ : ℝ} (hσ : 0 < σ) {x : ℝ}
    (hx : 0 ≤ x) : Absorbed.countA A x ≤ x ^ σ * P.rankinProd z σ := by
  classical
  refine le_trans ?_ (P.smoothCountN_le_rankin hσ hx z)
  set S := (Finset.Icc 0 ⌊x⌋₊).filter (· ∈ A)
  have hcount : Absorbed.countA A x = (S.card : ℝ) := by
    unfold Absorbed.countA
    rw [Finset.sum_boole]
  rw [hcount]
  choose! f hf using fun n (hn : n ∈ A) => (hA n hn).2
  unfold smoothCountN
  have key := Set.ncard_le_ncard_of_injOn (s := (S : Set ℕ)) f
    (fun n hn => by
      have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
      refine ⟨(hf n hn'.2).1, ?_⟩
      rw [(hf n hn'.2).2]
      exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hn'.1).2).trans (Nat.floor_le hx))
    (fun n hn m hm h => by
      have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
      have hm' := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
      have := congrArg P.val h
      rw [(hf n hn'.2).2, (hf m hm'.2).2] at this
      exact_mod_cast this)
    (P.finite_smooth_le x z)
  rw [Set.ncard_coe_finset] at key
  exact_mod_cast key

end BeurlingSystem

end
