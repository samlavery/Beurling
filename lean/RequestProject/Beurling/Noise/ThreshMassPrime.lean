module

public import RequestProject.Beurling.Noise.ThreshMassDefs

/-!
# Lemma 5.23: the two prime sums of the proof

* `sum_Kset_le_prod` : `∑_k 1/k ≤ ∏_{q t-below p}(1 + 1/q)` (the sum over the `k`-parts);
* `HBS.sum_inv_primesLe_le` : `∑_{p ≤ y} 1/p ≤ log log y + 4.1` for `4 ≤ y ≤ Z`, from
  Lemma 5.1(iv) (in the paper `∑_{p ≤ √x} 1/p ≤ log log x + 1`, by Rosser–Schoenfeld; the weaker
  constant from Lemma 5.1 suffices for the statement of Lemma 5.23).
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

omit P in
lemma sqf_eq_of_support {k k' : ℕ →₀ ℕ} (hk : Sqf k) (hk' : Sqf k')
    (h : k.support = k'.support) : k = k' := by
  ext i
  by_cases hi : i ∈ k.support
  · have hi' : i ∈ k'.support := h ▸ hi
    have h1 := le_antisymm (hk i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    have h2 := le_antisymm (hk' i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi'))
    rw [h1, h2]
  · have hi' : i ∉ k'.support := h ▸ hi
    rw [Finsupp.notMem_support_iff.mp hi, Finsupp.notMem_support_iff.mp hi']

/-- The `k`-sum is at most the Euler product over the primes `t`-below `p_j` (and `≤ x`). -/
theorem sum_Kset_le_prod (t : ℕ → ℝ) (x : ℝ) (j : ℕ) :
    ∑ k ∈ P.Kset t x j, 1 / P.val k ≤
      ∏ i ∈ (P.primesLe x).filter (fun i => t i < t j), (1 + 1 / P.p i) := by
  classical
  set S := (P.primesLe x).filter (fun i => t i < t j)
  have hval : ∀ k ∈ P.Kset t x j, 1 / P.val k = ∏ i ∈ k.support, 1 / P.p i := by
    intro k hk
    have hs := (Finset.mem_filter.mp hk).2.1
    rw [P.val_eq_prod_support hs, Finset.prod_div_distrib, Finset.prod_const_one]
  have hinj : Set.InjOn (fun k : ℕ →₀ ℕ => k.support) (P.Kset t x j) := by
    intro k hk k' hk' h
    exact sqf_eq_of_support (Finset.mem_filter.mp hk).2.1 (Finset.mem_filter.mp hk').2.1 h
  have hsub : (P.Kset t x j).image (fun k => k.support) ⊆ S.powerset := by
    intro A hA
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hkx, -, hlt⟩ := Finset.mem_filter.mp hk
    rw [mem_elems] at hkx
    rw [Finset.mem_powerset]
    intro i hi
    refine Finset.mem_filter.mpr ⟨?_, hlt i hi⟩
    rw [mem_primesLe]
    have h1 : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    calc P.p i = P.p i ^ 1 := (pow_one _).symm
      _ ≤ P.p i ^ k i := pow_le_pow_right₀ (P.one_lt i).le h1
      _ ≤ P.val k := P.pow_le_val k i
      _ ≤ x := hkx
  calc ∑ k ∈ P.Kset t x j, 1 / P.val k
      = ∑ k ∈ P.Kset t x j, ∏ i ∈ k.support, 1 / P.p i := Finset.sum_congr rfl hval
    _ = ∑ A ∈ (P.Kset t x j).image (fun k => k.support), ∏ i ∈ A, 1 / P.p i :=
        (Finset.sum_image (f := fun A => ∏ i ∈ A, 1 / P.p i) hinj).symm
    _ ≤ ∑ A ∈ S.powerset, ∏ i ∈ A, 1 / P.p i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro A _ _
        exact Finset.prod_nonneg fun i _ => (one_div_pos.mpr (P.p_pos i)).le
    _ = ∏ i ∈ S, (1 + 1 / P.p i) := (Finset.prod_one_add S).symm

namespace HBS

variable {P} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma neg_log_log_two_le : -Real.log (Real.log 2) ≤ 0.38 := by
  have hl2 := Real.log_two_gt_d9
  have h0 : (0 : ℝ) < Real.log 2 := by linarith
  have he : Real.exp (-0.38) ≤ Real.log 2 := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := 0.38) (by norm_num)
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) h0]
    have : (Real.log 2)⁻¹ ≤ 1 / 0.6931 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have : (1 : ℝ) / 0.6931 ≤ 1 + 0.38 + 0.38 ^ 2 / 2 := by norm_num
    linarith
  have := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at this
  linarith

/-- `∑_{p ≤ y} 1/p ≤ log log y + 4.1` for `4 ≤ y ≤ Z` (Lemma 5.1(iv) with `y₀ = 2`). -/
theorem sum_inv_primesLe_le (h : P.HBS X0m Z η1 η2 ε1) {y : ℝ} (hy : 4 ≤ y) (hyZ : y ≤ Z) :
    ∑ j ∈ P.primesLe y, 1 / P.p j ≤ Real.log (Real.log y) + 4.1 := by
  classical
  have hX := h.X0m_ge
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe y) (fun j => 2 < P.p j)]
  have hiv := h.mertens_iv (y := 2) (x := y) le_rfl (by linarith) hyZ
  have h1 : ∑ j ∈ (P.primesLe y).filter (fun j => 2 < P.p j), 1 / P.p j ≤
      Real.log (Real.log y / Real.log 2) + 2.20 / Real.log 2 := by
    have := (abs_le.mp hiv).2; linarith
  have hsmall : (P.primesLe y).filter (fun j => ¬ 2 < P.p j) ⊆ {0} := by
    intro j hj
    obtain ⟨-, hj2⟩ := Finset.mem_filter.mp hj
    push_neg at hj2
    have hid := h.ident (x := 2) (by norm_num at hX ⊢; linarith) (by linarith) j (Or.inl hj2)
    rw [hid] at hj2
    have hq : qp j ≤ 2 := by exact_mod_cast hj2
    rw [Finset.mem_singleton]
    by_contra hne
    have h1 : qp 1 ≤ qp j := qp_strictMono.monotone (Nat.one_le_iff_ne_zero.mpr hne)
    have h3 : qp 1 = 3 := by simp [qp, Nat.nth_prime_one_eq_three]
    omega
  have h2 : ∑ j ∈ (P.primesLe y).filter (fun j => ¬ 2 < P.p j), 1 / P.p j ≤ 1 / 2 := by
    calc _ ≤ ∑ j ∈ ({0} : Finset ℕ), 1 / P.p j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsmall
            (fun j _ _ => (one_div_pos.mpr (P.p_pos j)).le)
      _ ≤ 1 / 2 := by
          rw [Finset.sum_singleton]
          have := h.p_ge_two (j := 0) ?_
          · exact one_div_le_one_div_of_le (by norm_num) this
          · have hid := h.ident (x := 2) (by norm_num at hX ⊢; linarith) (by linarith) 0
              (Or.inr (by simp [qp, Nat.nth_prime_zero_eq_two]))
            rw [hid]; simp [qp, Nat.nth_prime_zero_eq_two]; linarith
  have hl2 := Real.log_two_gt_d9
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have e : Real.log (Real.log y / Real.log 2) = Real.log (Real.log y) - Real.log (Real.log 2) :=
    Real.log_div hly.ne' (by linarith)
  have h3 : 2.20 / Real.log 2 ≤ 3.175 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h4 := neg_log_log_two_le
  linarith

end HBS

end BeurlingSystem

end
