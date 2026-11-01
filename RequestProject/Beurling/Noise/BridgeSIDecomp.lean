module

public import RequestProject.Beurling.Noise.BSRedRec

/-!
# Lemma 5.32: the decomposition by the top prime

`S_t([N, N(1+η)]) = ∑_{n ∈ 𝒩 ∩ [N, N(1+η)], n squarefree, t-dense} 1/n` (`SIsum`). Write
`p = P⁺(n)` (the prime of largest index) and `m = n/p`. As in Step 1 of the proof of Theorem 5.6,
`m` is squarefree and `t`-dense, its primes are `≤ p`, and `p ≤ t m`, so `m ≥ √(N/t)`.

`SIsum_le_decomp` : for `P₁ > 0`, the elements with `p < P₁` are `P₁`-smooth and lie in
`(N/2, N] ∪ (N, 2N]` (part (B) of the proof); the others are counted by the pairs `(m, p)` with
`m` in the cofactor set `SIcof` (`m ≤ N(1+η)/P₁`, `m ≥ √(N/t)`, `t`-dense, primes
`≤ N(1+η)/m`) and `p ∈ [N/m, N(1+η)/m]`:

  `S_t([N, N(1+η)]) ≤ v(log(N/2), P₁) + v(log N, P₁) + ∑_{m} (1/m) ∑_{N/m ≤ p ≤ N(1+η)/m} 1/p`.
-/

@[expose] public section

open Real Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `S_t([N, N(1+η)])` of Lemma 5.32. -/
noncomputable def SIsum (t N η : ℝ) : ℝ :=
  open scoped Classical in
  ∑ e ∈ (P.elems (N * (1 + η))).filter (fun e => N ≤ P.val e ∧ P.IsDense t e), 1 / P.val e

/-- The cofactors `m = n/P⁺(n)` of Lemma 5.32 (A) with `P⁺(n) ≥ P₁`. -/
noncomputable def SIcof (t N η P1 : ℝ) : Finset (ℕ →₀ ℕ) :=
  open scoped Classical in
  (P.elems (N * (1 + η) / P1)).filter (fun m => √(N / t) ≤ P.val m ∧ P.IsDense t m ∧
    ∀ i ∈ m.support, P.p i ≤ N * (1 + η) / P.val m)

/-- The primes of the window `[N/m, N(1+η)/m]`. -/
noncomputable def SIwin (N η M : ℝ) : Finset ℕ :=
  (P.primesLe (N / M * (1 + η))).filter (fun j => N / M ≤ P.p j)

lemma prod_lt_top {e : ℕ →₀ ℕ} (hsq : ∀ i, e i ≤ 1) (hne : e.support.Nonempty) :
    ∏ i ∈ e.support.filter (· < topI e), P.p i = P.val (e.erase (topI e)) := by
  set j := topI e
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

lemma isDense_erase_top {t : ℝ} {e : ℕ →₀ ℕ} (hd : P.IsDense t e) :
    P.IsDense t (e.erase (topI e)) := by
  obtain ⟨hsq, hden⟩ := hd
  set j := topI e
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · by_cases hij : i = j
    · subst hij; simp
    · rw [Finsupp.erase_ne hij]; exact hsq i
  · rw [Finsupp.support_erase, mem_erase] at hi
    have hij : i < j := lt_of_le_of_ne (le_topI hi.2) hi.1
    have hfilt : (e.erase j).support.filter (· < i) = e.support.filter (· < i) := by
      ext k
      simp only [Finsupp.support_erase, mem_erase, mem_filter]
      constructor
      · rintro ⟨⟨_, hk⟩, hki⟩; exact ⟨hk, hki⟩
      · rintro ⟨hk, hki⟩; exact ⟨⟨(hki.trans hij).ne, hk⟩, hki⟩
    rw [hfilt]; exact hden i hi.2

open scoped Classical in
/-- **The decomposition of Lemma 5.32** by the top prime `p = P⁺(n)` at the threshold `P₁`. -/
theorem SIsum_le_decomp {t N η P1 : ℝ} (hN : 1 < N) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht : 0 < t)
    (hP1 : 0 < P1) :
    P.SIsum t N η ≤ P.vSmooth (N / 2) P1 + P.vSmooth N P1 +
      ∑ m ∈ P.SIcof t N η P1, 1 / P.val m * ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j := by
  set S := (P.elems (N * (1 + η))).filter (fun e => N ≤ P.val e ∧ P.IsDense t e) with hS
  have hSdef : P.SIsum t N η = ∑ e ∈ S, 1 / P.val e := by unfold SIsum; rw [hS]
  rw [hSdef, ← Finset.sum_filter_add_sum_filter_not S (fun e => P.p (topI e) < P1)]
  have hmem : ∀ e ∈ S, P.val e ≤ N * (1 + η) ∧ N ≤ P.val e ∧ P.IsDense t e := by
    intro e he
    simp only [hS, mem_filter, mem_elems] at he
    exact ⟨he.1, he.2.1, he.2.2⟩
  have hne : ∀ e ∈ S, e.support.Nonempty := fun e he =>
    P.support_nonempty_of_lt (le_refl 1) (lt_of_lt_of_le hN (hmem e he).2.1)
  have hnn : ∀ e : ℕ →₀ ℕ, 0 ≤ 1 / P.val e := fun e => div_nonneg zero_le_one (P.val_pos e).le
  have hN0 : 0 < N := by linarith
  refine add_le_add ?_ ?_
  · -- (B): the smooth elements
    set S1 := S.filter (fun e => P.p (topI e) < P1)
    have hsm : ∀ e ∈ S1, ∀ i ∈ e.support, P.p i ≤ P1 := by
      intro e he i hi
      have h1 := (mem_filter.mp he).2
      exact (P.mono (le_topI hi)).trans h1.le
    rw [← Finset.sum_filter_add_sum_filter_not S1 (fun e => P.val e ≤ N)]
    refine add_le_add ?_ ?_
    · unfold vSmooth
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun e _ _ => hnn e)
      intro e he
      have he1 := (mem_filter.mp he).1
      have hS1 := (mem_filter.mp he1).1
      obtain ⟨-, hNe, -⟩ := hmem e hS1
      simp only [mem_filter, mem_elems]
      exact ⟨by linarith [(mem_filter.mp he).2], by linarith, hsm e he1⟩
    · unfold vSmooth
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun e _ _ => hnn e)
      intro e he
      have he1 := (mem_filter.mp he).1
      have hS1 := (mem_filter.mp he1).1
      obtain ⟨hle, -, -⟩ := hmem e hS1
      simp only [mem_filter, mem_elems]
      refine ⟨by nlinarith, by linarith [not_le.mp (mem_filter.mp he).2], hsm e he1⟩
  · -- (A): the pairs `(m, p)`
    set S2 := S.filter (fun e => ¬ P.p (topI e) < P1)
    set T := (P.SIcof t N η P1).sigma (fun m => P.SIwin N η (P.val m))
    have hR : ∑ m ∈ P.SIcof t N η P1, 1 / P.val m * ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j =
        ∑ x ∈ T, 1 / P.val x.1 * (1 / P.p x.2) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
    rw [hR]
    set φ : (ℕ →₀ ℕ) → (Σ _ : ℕ →₀ ℕ, ℕ) := fun e => ⟨e.erase (topI e), topI e⟩
    have hdata : ∀ e ∈ S2, e (topI e) = 1 ∧ topI e ∈ e.support := by
      intro e he
      have hS2 := (mem_filter.mp he).1
      have hj := topI_mem (hne e hS2)
      exact ⟨le_antisymm ((hmem e hS2).2.2.1 _) (Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp hj)), hj⟩
    have hinj : Set.InjOn φ S2 := by
      intro e he e' he' h
      simp only [φ, Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← Finsupp.single_add_erase (topI e) e, ← Finsupp.single_add_erase (topI e') e',
        (hdata e he).1, (hdata e' he').1, h1]
      have : topI e = topI e' := eq_of_heq h2
      rw [this]
    have hval : ∀ e ∈ S2, 1 / P.val e = 1 / P.val (φ e).1 * (1 / P.p (φ e).2) := by
      intro e he
      simp only [φ]
      rw [P.val_eq_mul_erase (hdata e he).1]
      have := P.val_pos (e.erase (topI e))
      have := P.p_pos (topI e)
      field_simp
    rw [Finset.sum_congr rfl hval, ← Finset.sum_image (f := fun x : (Σ _ : ℕ →₀ ℕ, ℕ) =>
      1 / P.val x.1 * (1 / P.p x.2)) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      have hS2 := (mem_filter.mp he).1
      have hP := not_lt.mp (mem_filter.mp he).2
      obtain ⟨hle, hNe, hd⟩ := hmem e hS2
      obtain ⟨hej, hj⟩ := hdata e he
      set j := topI e
      set m := e.erase j
      have hv := P.val_eq_mul_erase hej
      have hpj := P.p_pos j
      have hm0 := P.val_pos m
      have hdj : P.p j ≤ t * P.val m := by
        have := hd.2 j hj
        rwa [P.prod_lt_top hd.1 (hne e hS2)] at this
      simp only [T, φ, Finset.mem_sigma, SIcof, SIwin, mem_filter, mem_elems, mem_primesLe]
      refine ⟨⟨?_, ?_, P.isDense_erase_top hd, ?_⟩, ?_, ?_⟩
      · rw [le_div_iff₀ hP1]; nlinarith
      · have h1 : N / t ≤ P.val m ^ 2 := by
          rw [div_le_iff₀ ht]; nlinarith
        calc √(N / t) ≤ √(P.val m ^ 2) := Real.sqrt_le_sqrt h1
          _ = P.val m := Real.sqrt_sq hm0.le
      · intro i hi
        rw [Finsupp.support_erase, mem_erase] at hi
        have hij : i ≤ j := le_topI hi.2
        rw [le_div_iff₀ hm0]
        nlinarith [P.mono hij]
      · rw [div_mul_eq_mul_div, le_div_iff₀ hm0]; nlinarith
      · rw [div_le_iff₀ hm0]; nlinarith
    · intro x _ _
      exact mul_nonneg (hnn _) (div_nonneg zero_le_one (P.p_pos _).le)

end BeurlingSystem

end
