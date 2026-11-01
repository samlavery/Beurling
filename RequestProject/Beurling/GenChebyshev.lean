module

public import RequestProject.Beurling.Basic

/-!
# Finite sums over a discrete Beurling system and the Chebyshev identity

For a discrete Beurling system `P` and a bound `x`:

* `P.elems x` : the (finitely many) elements `e` with `val e ≤ x`, so `N(x) = #(P.elems x)`;
* `P.pps x` : the prime powers `p_j^{k+1} ≤ x`, indexed by `(j, k)`;
* `P.ellN x = ∑_{n ≤ x} log n` (over the elements of `P`), the integral `∫_{[1,x]} log v dN(v)`;
* `P.chebyshev_identity` : **the Chebyshev identity** `∫ log v dN = dψ * dN`, i.e.
  `∑_{n ≤ x} log n = ∑_{p_j^{k+1} ≤ x} log p_j · N(x / p_j^{k+1})`.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The elements `e` of `P` with `val e ≤ x`. -/
noncomputable def elems (x : ℝ) : Finset (ℕ →₀ ℕ) := (P.finite_val_le x).toFinset

/-- The prime powers `p_j ^ (k+1) ≤ x`, indexed by `(j, k)`. -/
noncomputable def pps (x : ℝ) : Finset (ℕ × ℕ) := (P.finite_primePow_le x).toFinset

@[simp] lemma mem_elems {x : ℝ} {e : ℕ →₀ ℕ} : e ∈ P.elems x ↔ P.val e ≤ x := by
  simp [elems]

@[simp] lemma mem_pps {x : ℝ} {jk : ℕ × ℕ} : jk ∈ P.pps x ↔ P.p jk.1 ^ (jk.2 + 1) ≤ x := by
  simp [pps]

lemma N_eq_card (x : ℝ) : P.N x = ((P.elems x).card : ℝ) := by
  unfold N elems
  rw [Set.ncard_eq_toFinset_card _ (P.finite_val_le x)]

lemma psi_eq_sum (x : ℝ) : P.psi x = ∑ jk ∈ P.pps x, Real.log (P.p jk.1) := by
  rw [psi_eq_cnt]
  unfold AbelMellin.cnt
  rw [tsum_eq_sum (s := P.pps x)]
  · rw [Finset.sum_ite_of_true (fun e he => by simpa using he)]
  · intro e he; simp at he; simp [he]

lemma elems_mono {x y : ℝ} (h : x ≤ y) : P.elems x ⊆ P.elems y := by
  intro e; simp only [mem_elems]; intro he; linarith

lemma pps_mono {x y : ℝ} (h : x ≤ y) : P.pps x ⊆ P.pps y := by
  intro e; simp only [mem_pps]; intro he; linarith

lemma N_mono : Monotone P.N := by
  intro x y h
  rw [N_eq_card, N_eq_card]
  exact_mod_cast card_le_card (P.elems_mono h)

lemma N_nonneg (x : ℝ) : 0 ≤ P.N x := by rw [N_eq_card]; positivity

lemma elems_eq_empty {x : ℝ} (hx : x < 1) : P.elems x = ∅ := by
  ext e; simp only [mem_elems, notMem_empty, iff_false, not_le]
  linarith [P.one_le_val e]

lemma N_eq_zero {x : ℝ} (hx : x < 1) : P.N x = 0 := by
  rw [N_eq_card, P.elems_eq_empty hx]; simp

lemma pps_eq_empty {x : ℝ} (hx : x < 1) : P.pps x = ∅ := by
  ext e; simp only [mem_pps, notMem_empty, iff_false, not_le]
  linarith [P.one_le_pow' e.1 (e.2 + 1)]

lemma psi_eq_zero {x : ℝ} (hx : x < 1) : P.psi x = 0 := by
  rw [psi_eq_sum, P.pps_eq_empty hx]; simp

lemma log_p_nonneg (j : ℕ) : 0 ≤ Real.log (P.p j) := Real.log_nonneg (P.one_lt j).le

lemma psi_mono : Monotone P.psi := by
  intro x y h
  rw [psi_eq_sum, psi_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (P.pps_mono h) (fun i _ _ => P.log_p_nonneg i.1)

lemma psi_nonneg (x : ℝ) : 0 ≤ P.psi x := by
  rw [psi_eq_sum]; exact sum_nonneg fun i _ => P.log_p_nonneg i.1

/-- `ℓ_N(x) = ∑_{n ≤ x} log n` over the elements of `P`. -/
noncomputable def ellN (x : ℝ) : ℝ := ∑ e ∈ P.elems x, Real.log (P.val e)

lemma pp_pos (jk : ℕ × ℕ) : 0 < P.p jk.1 ^ (jk.2 + 1) := pow_pos (P.p_pos _) _

/-- `log (val e) = ∑_{(j,k) ∈ B, k < e j} log p_j` for any box `B = [0,J) × [0,M)` containing
the support. -/
lemma log_val_eq_sum_box (e : ℕ →₀ ℕ) (J M : ℕ) (hJ : ∀ j ∈ e.support, j < J)
    (hM : ∀ j, e j < M) :
    Real.log (P.val e) = ∑ jk ∈ (range J ×ˢ range M).filter (fun jk => jk.2 < e jk.1),
      Real.log (P.p jk.1) := by
  rw [log_val, Finset.sum_filter, Finset.sum_product]
  have h1 : ∀ j ∈ range J, (∑ k ∈ range M, if k < e j then Real.log (P.p j) else 0) =
      (e j : ℝ) * Real.log (P.p j) := by
    intro j _
    rw [← Finset.sum_filter]
    have : (range M).filter (fun k => k < e j) = range (e j) := by
      ext k; simp only [mem_filter, mem_range]; have := hM j; omega
    rw [this]; simp
  rw [Finset.sum_congr rfl h1]
  unfold Finsupp.sum
  apply Finset.sum_subset
  · intro j hj; exact mem_range.mpr (hJ j hj)
  · intro j _ hj
    rw [Finsupp.notMem_support_iff.mp hj]; simp

lemma val_sub_single {e : ℕ →₀ ℕ} {j k : ℕ} (h : k + 1 ≤ e j) :
    P.val e = P.val (e - Finsupp.single j (k + 1)) * P.p j ^ (k + 1) := by
  have hle : Finsupp.single j (k + 1) ≤ e := (Finsupp.single_le_iff).mpr h
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [val_add, val_single]

/-- **The Chebyshev identity** for a discrete Beurling system:
`∑_{n ≤ x} log n = ∑_{p_j^{k+1} ≤ x} log p_j · N(x / p_j^{k+1})`. -/
theorem chebyshev_identity (x : ℝ) :
    P.ellN x = ∑ jk ∈ P.pps x, Real.log (P.p jk.1) * P.N (x / P.p jk.1 ^ (jk.2 + 1)) := by
  obtain ⟨J, M, hJ, hM⟩ := P.exists_bounds x
  set B := range J ×ˢ range M
  have hsupp : ∀ e ∈ P.elems x, ∀ j ∈ e.support, j < J := by
    intro e he j hj
    rw [mem_elems] at he
    apply hJ
    have h1 : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    calc P.p j = P.p j ^ 1 := (pow_one _).symm
      _ ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le h1
      _ ≤ P.val e := P.pow_le_val e j
      _ ≤ x := he
  have hexp : ∀ e ∈ P.elems x, ∀ j, e j < M := by
    intro e he j
    rw [mem_elems] at he
    exact hM j (e j) ((P.pow_le_val e j).trans he)
  -- left side as a sum over triples
  have hL : P.ellN x = ∑ q ∈ (P.elems x ×ˢ B).filter (fun q => q.2.2 < q.1 q.2.1),
      Real.log (P.p q.2.1) := by
    unfold ellN
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [P.log_val_eq_sum_box e J M (hsupp e he) (hexp e he), Finset.sum_filter]
  have hR : ∑ jk ∈ P.pps x, Real.log (P.p jk.1) * P.N (x / P.p jk.1 ^ (jk.2 + 1)) =
      ∑ q ∈ (P.pps x).sigma (fun jk => P.elems (x / P.p jk.1 ^ (jk.2 + 1))),
        Real.log (P.p q.1.1) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun jk _ => ?_
    simp [N_eq_card, Finset.sum_const, mul_comm]
  rw [hL, hR]
  refine Finset.sum_bij' (fun q _ => ⟨q.2, q.1 - Finsupp.single q.2.1 (q.2.2 + 1)⟩)
    (fun q _ => (q.2 + Finsupp.single q.1.1 (q.1.2 + 1), q.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, j, k⟩ hq
    simp only [mem_filter, mem_product, mem_elems] at hq
    obtain ⟨⟨he, -⟩, hk⟩ := hq
    have hval := P.val_sub_single (e := e) (j := j) (k := k) hk
    have hpos := P.pp_pos (j, k)
    simp only [mem_sigma, mem_pps, mem_elems]
    refine ⟨?_, ?_⟩
    · calc P.p j ^ (k + 1) ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le hk
        _ ≤ P.val e := P.pow_le_val e j
        _ ≤ x := he
    · rw [le_div_iff₀ hpos]; rw [hval] at he; exact he
  · rintro ⟨⟨j, k⟩, e'⟩ hq
    simp only [mem_sigma, mem_pps, mem_elems] at hq
    obtain ⟨hjk, he'⟩ := hq
    have hpos := P.pp_pos (j, k)
    have hval : P.val (e' + Finsupp.single j (k + 1)) = P.val e' * P.p j ^ (k + 1) := by
      rw [val_add, val_single]
    simp only [mem_filter, mem_product, mem_elems, B, mem_range]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hval]; rwa [le_div_iff₀ hpos] at he'
    · apply hJ
      calc P.p j = P.p j ^ 1 := (pow_one _).symm
        _ ≤ P.p j ^ (k + 1) := pow_le_pow_right₀ (P.one_lt j).le (by omega)
        _ ≤ x := hjk
    · have := hM j (k + 1) hjk; omega
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
  · rintro ⟨e, j, k⟩ hq
    simp only [mem_filter] at hq
    have hle : Finsupp.single j (k + 1) ≤ e := (Finsupp.single_le_iff).mpr hq.2
    show (e - Finsupp.single j (k + 1) + Finsupp.single j (k + 1), (j, k)) = (e, (j, k))
    rw [tsub_add_cancel_of_le hle]
  · rintro ⟨⟨j, k⟩, e'⟩ _
    simp
  · rintro ⟨e, j, k⟩ _
    rfl

end BeurlingSystem

end
