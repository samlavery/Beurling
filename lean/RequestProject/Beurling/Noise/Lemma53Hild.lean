module

public import RequestProject.Beurling.Noise.Lemma53Sums

/-!
# Lemma 5.3: Hildebrand's identity

`BeurlingSystem.hildebrand`: since `log n = ∑_{p^k ∥ n} k log p` in the free semigroup, and
writing `n = p^k m`,

  `∑_{n ∈ (Y,2Y], P⁺(n) ≤ z} log n / n = ∑_{p ≤ z, k ≥ 1} (log p / p^k) v(Y/p^k, z)`

(the dyadic window shifts exactly). Here `p^k` runs over `P.pps (2Y)` (the `p_j^{k+1} ≤ 2Y`;
larger prime powers contribute nothing).
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- **Hildebrand's identity** (proof of Lemma 5.3). -/
theorem hildebrand (Y z : ℝ) :
    ∑ e ∈ (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z),
        Real.log (P.val e) / P.val e =
      ∑ jk ∈ (P.pps (2 * Y)).filter (fun jk => P.p jk.1 ≤ z),
        Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) *
          P.vSmooth (Y / P.p jk.1 ^ (jk.2 + 1)) z := by
  set x := 2 * Y
  obtain ⟨J, M, hJ, hM⟩ := P.exists_bounds x
  set B := range J ×ˢ range M
  set A := (P.elems x).filter (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z)
  have hsupp : ∀ e ∈ A, ∀ j ∈ e.support, j < J := by
    intro e he j hj
    simp only [A, mem_filter, mem_elems] at he
    apply hJ
    have h1 : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    calc P.p j = P.p j ^ 1 := (pow_one _).symm
      _ ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le h1
      _ ≤ P.val e := P.pow_le_val e j
      _ ≤ x := he.1
  have hexp : ∀ e ∈ A, ∀ j, e j < M := by
    intro e he j
    simp only [A, mem_filter, mem_elems] at he
    exact hM j (e j) ((P.pow_le_val e j).trans he.1)
  have hL : ∑ e ∈ A, Real.log (P.val e) / P.val e =
      ∑ q ∈ (A ×ˢ B).filter (fun q => q.2.2 < q.1 q.2.1),
        Real.log (P.p q.2.1) / P.val q.1 := by
    conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [P.log_val_eq_sum_box e J M (hsupp e he) (hexp e he), Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun jk _ => ?_
    split_ifs <;> simp
  have hR : ∑ jk ∈ (P.pps x).filter (fun jk => P.p jk.1 ≤ z),
        Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) * P.vSmooth (Y / P.p jk.1 ^ (jk.2 + 1)) z =
      ∑ q ∈ ((P.pps x).filter (fun jk => P.p jk.1 ≤ z)).sigma (fun jk =>
          (P.elems (2 * (Y / P.p jk.1 ^ (jk.2 + 1)))).filter (fun e =>
            Y / P.p jk.1 ^ (jk.2 + 1) < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z)),
        Real.log (P.p q.1.1) / (P.val q.2 * P.p q.1.1 ^ (q.1.2 + 1)) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun jk _ => ?_
    unfold vSmooth
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := P.pp_pos jk
    have := P.val_pos e
    field_simp
  rw [hL, hR]
  refine Finset.sum_bij' (fun q _ => ⟨q.2, q.1 - Finsupp.single q.2.1 (q.2.2 + 1)⟩)
    (fun q _ => (q.2 + Finsupp.single q.1.1 (q.1.2 + 1), q.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, j, k⟩ hq
    simp only [A, mem_filter, mem_product, mem_elems] at hq
    obtain ⟨⟨⟨he, hY, hz⟩, -⟩, hk⟩ := hq
    have hval := P.val_sub_single (e := e) (j := j) (k := k) hk
    have hpos := P.pp_pos (j, k)
    have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr (by omega)
    simp only [mem_sigma, mem_filter, mem_pps, mem_elems]
    refine ⟨⟨?_, hz j hjs⟩, ?_, ?_, ?_⟩
    · calc P.p j ^ (k + 1) ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le hk
        _ ≤ P.val e := P.pow_le_val e j
        _ ≤ x := he
    · rw [show 2 * (Y / P.p j ^ (k + 1)) = x / P.p j ^ (k + 1) by simp only [x]; ring,
        le_div_iff₀ hpos]
      rw [hval] at he; exact he
    · rw [div_lt_iff₀ hpos]; rw [hval] at hY; exact hY
    · intro i hi
      apply hz i
      rw [Finsupp.mem_support_iff] at hi ⊢
      intro h0; apply hi; simp [h0]
  · rintro ⟨⟨j, k⟩, e'⟩ hq
    simp only [mem_sigma, mem_filter, mem_pps, mem_elems] at hq
    obtain ⟨⟨hjk, hjz⟩, he', hY', hz'⟩ := hq
    have hpos := P.pp_pos (j, k)
    have hval : P.val (e' + Finsupp.single j (k + 1)) = P.val e' * P.p j ^ (k + 1) := by
      rw [val_add, val_single]
    simp only [A, mem_filter, mem_product, mem_elems, B, mem_range]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [hval]
      rw [show 2 * (Y / P.p j ^ (k + 1)) = x / P.p j ^ (k + 1) by simp only [x]; ring,
        le_div_iff₀ hpos] at he'
      exact he'
    · rw [hval]; rwa [div_lt_iff₀ hpos] at hY'
    · intro i hi
      by_cases hij : i = j
      · rw [hij]; exact hjz
      · apply hz' i
        rw [Finsupp.mem_support_iff] at hi ⊢
        simpa [Finsupp.single_apply, Ne.symm hij] using hi
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
  · rintro ⟨e, j, k⟩ hq
    simp only [mem_filter] at hq
    have hk := hq.2
    have hval := P.val_sub_single (e := e) (j := j) (k := k) hk
    simp only
    rw [hval]

end BeurlingSystem

end
