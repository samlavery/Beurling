module

public import RequestProject.Beurling.AbelMellin
public import RequestProject.Beurling.Defs

/-!
# Elementary properties of discrete Beurling systems

* `val` is multiplicative, `val e ≥ 1`, and `log (val e) = ∑ⱼ e j log p j`;
* only finitely many elements and prime powers lie below any bound;
* `N_P` and `ψ_P` are weighted counting functions in the sense of `AbelMellin.cnt`.
-/

@[expose] public section

open Filter

namespace BeurlingSystem

variable (P : BeurlingSystem)

lemma one_le_pow' (j k : ℕ) : 1 ≤ P.p j ^ k := one_le_pow₀ (P.one_lt j).le

lemma p_pos (j : ℕ) : 0 < P.p j := lt_trans one_pos (P.one_lt j)

private lemma one_le_finset_prod (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have := Finset.prod_le_prod₀ (s := s) (f := fun _ => (1:ℝ)) (g := f) (fun _ _ => zero_le_one) h
  simpa using this

lemma one_le_val (e : ℕ →₀ ℕ) : 1 ≤ P.val e := by
  unfold val Finsupp.prod
  exact one_le_finset_prod _ _ (fun j _ => P.one_le_pow' j (e j))

lemma val_pos (e : ℕ →₀ ℕ) : 0 < P.val e := lt_of_lt_of_le one_pos (P.one_le_val e)

lemma pow_le_val (e : ℕ →₀ ℕ) (j : ℕ) : P.p j ^ e j ≤ P.val e := by
  by_cases hj : j ∈ e.support
  · unfold val Finsupp.prod
    rw [← Finset.mul_prod_erase e.support _ hj]
    have := one_le_finset_prod (e.support.erase j) (fun i => P.p i ^ e i)
      (fun i _ => P.one_le_pow' i (e i))
    have := P.one_le_pow' j (e j)
    nlinarith
  · rw [Finsupp.notMem_support_iff.mp hj, pow_zero]
    exact P.one_le_val e

lemma val_add (e f : ℕ →₀ ℕ) : P.val (e + f) = P.val e * P.val f := by
  unfold val
  exact Finsupp.prod_add_index' (fun j => pow_zero _) (fun j a b => pow_add _ _ _)

lemma val_single (j k : ℕ) : P.val (Finsupp.single j k) = P.p j ^ k := by
  unfold val
  exact Finsupp.prod_single_index (pow_zero _)

lemma log_val (e : ℕ →₀ ℕ) :
    Real.log (P.val e) = e.sum fun j k => k * Real.log (P.p j) := by
  unfold val Finsupp.prod Finsupp.sum
  rw [Real.log_prod]
  · simp [Real.log_pow]
  · intro j _; exact pow_ne_zero _ (P.p_pos j).ne'

/-- Below any bound `x` there are only finitely many indices `j` with `p j ≤ x`, and exponents
`k` with `p j ^ k ≤ x` are bounded. -/
lemma exists_bounds (x : ℝ) : ∃ J M : ℕ, (∀ j, P.p j ≤ x → j < J) ∧
    ∀ j k, P.p j ^ k ≤ x → k < M := by
  obtain ⟨J, hJ⟩ := (P.tendsto.eventually_gt_atTop x).exists_forall_of_atTop
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt x (P.one_lt 0)
  refine ⟨J, M, fun j hj => ?_, fun j k hk => ?_⟩
  · by_contra h; push_neg at h; linarith [hJ j h]
  · by_contra h; push_neg at h
    have h1 : P.p 0 ^ M ≤ P.p 0 ^ k := pow_le_pow_right₀ (P.one_lt 0).le h
    have h2 : P.p 0 ^ k ≤ P.p j ^ k :=
      pow_le_pow_left₀ (P.p_pos 0).le (P.mono (Nat.zero_le j)) k
    linarith

lemma finite_val_le (x : ℝ) : {e : ℕ →₀ ℕ | P.val e ≤ x}.Finite := by
  obtain ⟨J, M, hJ, hM⟩ := P.exists_bounds x
  refine (Finset.finite_toSet ((Finset.range J).finsupp fun _ => Finset.range M)).subset ?_
  intro e he
  simp only [Set.mem_setOf_eq] at he
  simp only [Finset.mem_coe, Finset.mem_finsupp_iff, Finset.mem_range]
  refine ⟨fun j hj => ?_, fun j _ => hM j (e j) ((P.pow_le_val e j).trans he)⟩
  rw [Finset.mem_range]
  apply hJ
  have h1 : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  calc P.p j = P.p j ^ 1 := (pow_one _).symm
    _ ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le h1
    _ ≤ P.val e := P.pow_le_val e j
    _ ≤ x := he

lemma finite_primePow_le (x : ℝ) :
    {jk : ℕ × ℕ | P.p jk.1 ^ (jk.2 + 1) ≤ x}.Finite := by
  obtain ⟨J, M, hJ, hM⟩ := P.exists_bounds x
  refine (Finset.finite_toSet (Finset.range J ×ˢ Finset.range M)).subset ?_
  rintro ⟨j, k⟩ hjk
  simp only [Set.mem_setOf_eq] at hjk
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  refine ⟨hJ j ?_, ?_⟩
  · calc P.p j = P.p j ^ 1 := (pow_one _).symm
      _ ≤ P.p j ^ (k + 1) := pow_le_pow_right₀ (P.one_lt j).le (by omega)
      _ ≤ x := hjk
  · have := hM j (k + 1) hjk; omega

/-- `N_P` is the counting function of the elements (weight `1` at each `val e`). -/
lemma N_eq_cnt (x : ℝ) : P.N x = AbelMellin.cnt P.val (fun _ => (1 : ℝ)) x := by
  have hS := P.finite_val_le x
  unfold N AbelMellin.cnt
  rw [tsum_eq_sum (s := hS.toFinset), Set.ncard_eq_toFinset_card _ hS]
  · rw [Finset.sum_ite_of_true (fun e he => by simpa using he)]
    simp
  · intro e he; simp at he; simp [he]

/-- `ψ_P` is the weighted counting function of the prime powers `p j ^ (k+1)` with weights
`log p j`. -/
lemma psi_eq_cnt (x : ℝ) :
    P.psi x = AbelMellin.cnt (fun jk : ℕ × ℕ => P.p jk.1 ^ (jk.2 + 1))
      (fun jk => Real.log (P.p jk.1)) x := by
  have hS := P.finite_primePow_le x
  unfold psi AbelMellin.cnt
  rw [tsum_eq_sum (s := hS.toFinset)]
  · rw [Finset.sum_ite_of_true (fun e he => by simpa using he)]
    have hT : {jk : ℕ × ℕ | 1 ≤ jk.2 ∧ P.p jk.1 ^ jk.2 ≤ x} =
        (fun jk : ℕ × ℕ => (jk.1, jk.2 + 1)) '' {jk : ℕ × ℕ | P.p jk.1 ^ (jk.2 + 1) ≤ x} := by
      ext ⟨j, k⟩
      simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨j, k - 1, by rw [Nat.sub_add_cancel h1]; exact h2, rfl, by omega⟩
      · rintro ⟨a, b, h, rfl, rfl⟩
        exact ⟨by omega, h⟩
    rw [hT, finsum_mem_image (fun a _ b _ h => by simp_all [Prod.ext_iff]),
      finsum_mem_eq_finite_toFinset_sum _ hS]
  · intro e he; simp at he; simp [he]

lemma summable_N_ite (x : ℝ) :
    Summable fun e : ℕ →₀ ℕ => if P.val e ≤ x then (1 : ℝ) else 0 := by
  apply summable_of_hasFiniteSupport
  refine (P.finite_val_le x).subset fun e he => ?_
  by_contra h
  exact he (if_neg h)

lemma summable_psi_ite (x : ℝ) :
    Summable fun jk : ℕ × ℕ => if P.p jk.1 ^ (jk.2 + 1) ≤ x then Real.log (P.p jk.1) else 0 := by
  apply summable_of_hasFiniteSupport
  refine (P.finite_primePow_le x).subset fun e he => ?_
  by_contra h
  exact he (if_neg h)

end BeurlingSystem

end
