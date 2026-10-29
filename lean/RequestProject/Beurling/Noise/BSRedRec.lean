module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Step 1 of the proof of Theorem 5.6: the recursion (bs-rec)

If `n` is `t`-dense and `p = P⁺(n)` (the prime of largest index), then `n/p` is `t`-dense, all its
primes are `≤ p`, and `p ≤ t · n/p`, so `p² ≤ tn ≤ 2tY`. Summing over `p` first gives the
recursion (bs-rec). We split off the elements whose top prime has `log p ≤ s₀`: these are
`e^{s₀}`-smooth (Step 6), so their sum is at most `v(log Y, e^{s₀})`.

`Wsm_le_rec`: for `Y ≥ 1`,
`W_t(Y; Y^{1/u}) ≤ ∑_{p : s₀ < log p, u log p ≤ log Y, p² ≤ 2tY} (1/p) W_t(Y/p; p)
  + v(log Y, e^{s₀})`,
where `W_t(Y/p; p)` is written as `Wsm t (Y/p) w` with `w = (log Y - log p)/log p` (so that the
constraint `w log q ≤ log(Y/p)` is `log q ≤ log p`).
-/

@[expose] public section

open Real Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The index of the top prime of `e` (`0` for `e = 0`). -/
noncomputable def topI (e : ℕ →₀ ℕ) : ℕ :=
  if h : e.support.Nonempty then e.support.max' h else 0

lemma topI_mem {e : ℕ →₀ ℕ} (h : e.support.Nonempty) : topI e ∈ e.support := by
  unfold topI; rw [dif_pos h]; exact max'_mem _ _

lemma le_topI {e : ℕ →₀ ℕ} {i : ℕ} (hi : i ∈ e.support) : i ≤ topI e := by
  have h : e.support.Nonempty := ⟨i, hi⟩
  unfold topI; rw [dif_pos h]; exact le_max' _ _ hi

lemma val_eq_mul_erase {e : ℕ →₀ ℕ} {j : ℕ} (hj : e j = 1) :
    P.val e = P.p j * P.val (e.erase j) := by
  conv_lhs => rw [← Finsupp.single_add_erase j e]
  rw [P.val_add, P.val_single, hj, pow_one]

lemma support_nonempty_of_lt {e : ℕ →₀ ℕ} {Y : ℝ} (hY : 1 ≤ Y) (h : Y < P.val e) :
    e.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  rw [Finsupp.support_eq_empty] at he
  subst he
  have : P.val 0 = 1 := by simp [val]
  linarith

open scoped Classical in
/-- **The recursion (bs-rec)**, with the smooth part split off. -/
theorem Wsm_le_rec (t Y u s0 : ℝ) (hY : 1 ≤ Y)
    (hJ : ∀ j, u * Real.log (P.p j) ≤ Real.log Y → P.p j ^ 2 ≤ 2 * t * Y → P.p j ≤ Y) :
    P.Wsm t Y u ≤
      ∑ j ∈ (P.primesLe (2 * Y)).filter (fun j => s0 < Real.log (P.p j) ∧
          u * Real.log (P.p j) ≤ Real.log Y ∧ P.p j ^ 2 ≤ 2 * t * Y ∧ P.p j ≤ Y),
        1 / P.p j * P.Wsm t (Y / P.p j) ((Real.log Y - Real.log (P.p j)) / Real.log (P.p j))
      + P.vSmooth Y (Real.exp s0) := by
  set S := (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ P.IsDense t e ∧
      ∀ j ∈ e.support, u * Real.log (P.p j) ≤ Real.log Y) with hS
  have hW : P.Wsm t Y u = ∑ e ∈ S, 1 / P.val e := by
    unfold Wsm; rw [hS]
  rw [hW, ← Finset.sum_filter_add_sum_filter_not S (fun e => s0 < Real.log (P.p (topI e)))]
  gcongr ?_ + ?_
  · -- main part
    set J := (P.primesLe (2 * Y)).filter (fun j => s0 < Real.log (P.p j) ∧
          u * Real.log (P.p j) ≤ Real.log Y ∧ P.p j ^ 2 ≤ 2 * t * Y ∧ P.p j ≤ Y)
    have hmaps : ∀ e ∈ S.filter (fun e => s0 < Real.log (P.p (topI e))), topI e ∈ J := by
      intro e he
      simp only [hS, mem_filter, mem_elems] at he
      obtain ⟨⟨hle, hlt, ⟨hsq, hden⟩, hcon⟩, hs0⟩ := he
      have hne := P.support_nonempty_of_lt hY hlt
      set j := topI e
      have hj := topI_mem hne
      have hej : e j = 1 := le_antisymm (hsq j) (Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp hj))
      have hval := P.val_eq_mul_erase hej
      have hden_j := hden j hj
      have hprod : ∏ i ∈ e.support.filter (· < j), P.p i = P.val (e.erase j) := by
        rw [val, Finsupp.prod]
        have hsupp : (e.erase j).support = e.support.filter (· < j) := by
          ext i
          simp only [Finsupp.support_erase, mem_erase, mem_filter]
          constructor
          · rintro ⟨hij, hi⟩; exact ⟨hi, lt_of_le_of_ne (le_topI hi) hij⟩
          · rintro ⟨hi, hij⟩; exact ⟨hij.ne, hi⟩
        rw [hsupp]
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi' : i ∈ e.support := (mem_filter.mp hi).1
        have hij : i ≠ j := (mem_filter.mp hi).2.ne
        rw [Finsupp.erase_ne hij]
        have : e i = 1 := le_antisymm (hsq i) (Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp hi'))
        rw [this, pow_one]
      rw [hprod] at hden_j
      have hp1 := P.one_le_val (e.erase j)
      have hpj := P.p_pos j
      simp only [J, mem_filter, mem_primesLe]
      have h2 : P.p j ^ 2 ≤ 2 * t * Y := by nlinarith
      refine ⟨?_, hs0, hcon j hj, h2, hJ j (hcon j hj) h2⟩
      nlinarith
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun j hj => ?_
    set F := (S.filter (fun e => s0 < Real.log (P.p (topI e)))).filter
      (fun e => topI e = j)
    have hpj := P.p_pos j
    have hσ : 0 < Real.log (P.p j) := Real.log_pos (P.one_lt j)
    have hFe : ∀ e ∈ F, e j = 1 ∧ e.support.Nonempty ∧ topI e = j := by
      intro e he
      simp only [F, hS, mem_filter, mem_elems] at he
      have hne := P.support_nonempty_of_lt hY he.1.1.2.1
      have hj' := topI_mem hne
      rw [he.2] at hj'
      exact ⟨le_antisymm (he.1.1.2.2.1.1 j) (Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp hj')), hne, he.2⟩
    have hrw : ∑ e ∈ F, 1 / P.val e = 1 / P.p j * ∑ e ∈ F, 1 / P.val (e.erase j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [P.val_eq_mul_erase (hFe e he).1]
      field_simp
    rw [hrw]
    gcongr
    have hinj : Set.InjOn (fun e : ℕ →₀ ℕ => e.erase j) F := by
      intro e he e' he' h
      simp only at h
      rw [← Finsupp.single_add_erase j e, ← Finsupp.single_add_erase j e', (hFe e he).1,
        (hFe e' he').1, h]
    rw [← Finset.sum_image (f := fun e' => 1 / P.val e') hinj]
    unfold Wsm
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
      obtain ⟨hej, hne, htop⟩ := hFe e he
      simp only [F, hS, mem_filter, mem_elems] at he
      obtain ⟨⟨⟨hle, hlt, ⟨hsq, hden⟩, hcon⟩, _⟩, _⟩ := he
      have hval := P.val_eq_mul_erase hej
      have hsuppE : ∀ i ∈ (e.erase j).support, i ∈ e.support ∧ i < j := by
        intro i hi
        rw [Finsupp.support_erase, mem_erase] at hi
        exact ⟨hi.2, lt_of_le_of_ne (htop ▸ le_topI hi.2) hi.1⟩
      simp only [mem_filter, mem_elems]
      refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
      · rw [mul_div_assoc', le_div_iff₀ hpj]; nlinarith
      · rw [div_lt_iff₀ hpj]; nlinarith
      · intro i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Finsupp.erase_ne hij]; exact hsq i
      · intro i hi
        obtain ⟨hi', hij⟩ := hsuppE i hi
        have h1 := hden i hi'
        have hfilt : (e.erase j).support.filter (· < i) = e.support.filter (· < i) := by
          ext k
          simp only [Finsupp.support_erase, mem_erase, mem_filter]
          constructor
          · rintro ⟨⟨_, hk⟩, hki⟩; exact ⟨hk, hki⟩
          · rintro ⟨hk, hki⟩; exact ⟨⟨(hki.trans hij).ne, hk⟩, hki⟩
        rw [hfilt]; exact h1
      · intro i hi
        obtain ⟨_, hij⟩ := hsuppE i hi
        have hpi : P.p i ≤ P.p j := P.mono hij.le
        have hli : Real.log (P.p i) ≤ Real.log (P.p j) :=
          Real.log_le_log (P.p_pos i) hpi
        have hmj : 0 ≤ Real.log Y - Real.log (P.p j) := by
          have : P.p j ≤ Y := (mem_filter.mp hj).2.2.2.2
          linarith [Real.log_le_log hpj this]
        rw [Real.log_div (by linarith) hpj.ne']
        calc (Real.log Y - Real.log (P.p j)) / Real.log (P.p j) * Real.log (P.p i)
            ≤ (Real.log Y - Real.log (P.p j)) / Real.log (P.p j) * Real.log (P.p j) :=
              mul_le_mul_of_nonneg_left hli (div_nonneg hmj hσ.le)
          _ = Real.log Y - Real.log (P.p j) := by field_simp
    · intro e' _ _
      exact div_nonneg zero_le_one (P.val_pos e').le
  · -- tail: smooth elements
    unfold vSmooth
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      simp only [hS, mem_filter, mem_elems, not_lt] at he ⊢
      obtain ⟨⟨hle, hlt, _, _⟩, hs0⟩ := he
      refine ⟨hle, hlt, fun i hi => ?_⟩
      have h1 : P.p i ≤ P.p (topI e) := P.mono (le_topI hi)
      have h2 : P.p (topI e) ≤ Real.exp s0 :=
        (Real.log_le_iff_le_exp (P.p_pos _)).mp hs0
      linarith
    · intro e _ _
      exact div_nonneg zero_le_one (P.val_pos e).le

end BeurlingSystem

end
