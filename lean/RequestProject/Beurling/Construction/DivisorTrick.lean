module

public import RequestProject.Beurling.Basic
public import RequestProject.Beurling.Construction.RankinBeurling
public import RequestProject.Beurling.Construction.LocalCount

/-!
# Lemma 6.26, steps (ii), (iii) and the first bullet of (v): the divisor trick

Let `P` be a discrete Beurling system, `z ≥ 1`, `1 ≤ h < u`, and suppose (step (i)) that every
`n ∈ A ∩ [u, u + h]` is the value of a `z`-smooth element of `N`.

* (ii) `exists_split`: multiplying the primes of such an element one at a time and stopping at the
  first partial product `> h` gives a `z`-smooth divisor `d` with `h < d ≤ z h`, and
  `n = d · m` with `m ∈ N`.
* (iii) `localCount_le_divisor`: hence, if (step (iv)) each window
  `I_d = [u/d, (u + h)/d]` holds at most `C` elements of `N` (for the smooth `d ∈ (h, z h]`),

    `#(A ∩ [u, u + h]) ≤ C · Ψ_N(z h, z)`.

* With Rankin's bound for the realised system (`smoothCountN_le_rankin`):
  `#(A ∩ [u, u + h]) ≤ C (z h)^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}` (`localCount_le_rankin`).
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

lemma val_zero : P.val 0 = 1 := by simp [val]

/-- **Step (ii) of Lemma 6.26 (the divisor trick)**: a `z`-smooth element `e` of value `> h ≥ 1`
has a divisor `d ≤ e` with `h < val d ≤ z h`. -/
theorem exists_split {z h : ℝ} (hh : 1 ≤ h) {e : ℕ →₀ ℕ} (he : e ∈ P.smoothElems z)
    (hv : h < P.val e) : ∃ d ≤ e, h < P.val d ∧ P.val d ≤ z * h := by
  classical
  set D := (Finset.Iic e).filter (fun d => P.val d ≤ h) with hD
  have h0 : (0 : ℕ →₀ ℕ) ∈ D := by
    rw [hD, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨zero_le _, by rw [P.val_zero]; exact hh⟩
  obtain ⟨d0, hd0, hmax⟩ := Finset.exists_max_image D P.val ⟨0, h0⟩
  rw [hD, Finset.mem_filter, Finset.mem_Iic] at hd0
  have hne : d0 ≠ e := by
    rintro rfl; linarith [hd0.2]
  obtain ⟨j, hj⟩ : ∃ j, d0 j < e j := by
    by_contra hcon
    push_neg at hcon
    exact hne (le_antisymm hd0.1 (fun j => hcon j))
  set d' := d0 + Finsupp.single j 1 with hd'
  have hd'le : d' ≤ e := by
    intro i
    have hi := hd0.1 i
    rw [hd', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with hij
    · subst hij; omega
    · omega
  have hval : P.val d' = P.val d0 * P.p j := by rw [hd', P.val_add, P.val_single, pow_one]
  have hpj : 1 < P.p j := P.one_lt j
  have hjz : P.p j < z := he j (Finsupp.mem_support_iff.mpr (by omega))
  have hd0pos := P.val_pos d0
  refine ⟨d', hd'le, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hmem : d' ∈ D := by
      rw [hD, Finset.mem_filter, Finset.mem_Iic]; exact ⟨hd'le, hc⟩
    have := hmax d' hmem
    rw [hval] at this
    nlinarith
  · rw [hval]
    have := hd0.2
    calc P.val d0 * P.p j ≤ h * P.p j := mul_le_mul_of_nonneg_right this (by linarith)
      _ ≤ h * z := mul_le_mul_of_nonneg_left hjz.le (by linarith)
      _ = z * h := by ring

/-- The elements `m` with `val d · val m ∈ [u, u + h]` form a finite set. -/
lemma finite_window (d : ℕ →₀ ℕ) (u h : ℝ) :
    {m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.Finite := by
  refine (P.finite_val_le ((u + h) / P.val d)).subset fun m hm => ?_
  simp only [Set.mem_setOf_eq] at hm ⊢
  rw [le_div_iff₀ (P.val_pos d)]
  linarith [hm.2]

open scoped Classical in
/-- **Steps (ii)–(iii) of Lemma 6.26**: if every `n ∈ A ∩ [u, u + h]` is the value of a `z`-smooth
element (step (i)), and each window `[u/d, (u + h)/d]` with `d` smooth in `(h, z h]` holds at most
`C` elements of `N` (step (iv)), then `#(A ∩ [u, u + h]) ≤ C Ψ_N(z h, z)`. -/
theorem localCount_le_divisor {A : Set ℝ} {u h z C : ℝ} (hh : 1 ≤ h) (hu : h < u) (hC : 0 ≤ C)
    (hS : ∀ n ∈ A, u ≤ n → (n : ℝ) ≤ u + h → ∃ e ∈ P.smoothElems z, P.val e = n)
    (hW : ∀ d ∈ P.smoothElems z, h < P.val d → P.val d ≤ z * h →
      ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.ncard : ℝ) ≤ C) :
    (Absorbed.localCountA A u (u + h) : ℝ) ≤ C * P.smoothCountN (z * h) z := by
  have hAfin : (A ∩ Set.Icc u (u + h)).Finite := by
    refine ((P.finite_smooth_le (u + h) z).image P.val).subset fun n hn => ?_
    obtain ⟨e, he, hev⟩ := hS n hn.1 hn.2.1 hn.2.2
    exact ⟨e, ⟨he, by rw [hev]; exact hn.2.2⟩, hev⟩
  set S := hAfin.toFinset with hSdef
  have hmemS : ∀ n ∈ S, n ∈ A ∧ u ≤ n ∧ (n : ℝ) ≤ u + h := by
    intro n hn
    rw [hSdef, Set.Finite.mem_toFinset] at hn
    exact ⟨hn.1, hn.2.1, hn.2.2⟩
  -- the element of each `n ∈ S` and its divisor
  have hrep : ∀ n ∈ S, ∃ e ∈ P.smoothElems z, P.val e = n := fun n hn =>
    hS n (hmemS n hn).1 (hmemS n hn).2.1 (hmemS n hn).2.2
  choose! e he using hrep
  have hsplit : ∀ n ∈ S, ∃ d ≤ e n, h < P.val d ∧ P.val d ≤ z * h := fun n hn =>
    P.exists_split hh (he n hn).1 (by rw [(he n hn).2]; linarith [(hmemS n hn).2.1])
  choose! d hd using hsplit
  -- the divisors range over the smooth `d ∈ (h, z h]`
  set Dset := {d : ℕ →₀ ℕ | d ∈ P.smoothElems z ∧ h < P.val d ∧ P.val d ≤ z * h}
  have hDfin : Dset.Finite := (P.finite_smooth_le (z * h) z).subset fun d hd => ⟨hd.1, hd.2.2⟩
  set DF := hDfin.toFinset
  have hdsmooth : ∀ n ∈ S, d n ∈ P.smoothElems z := fun n hn j hj =>
    (he n hn).1 j (Finsupp.support_mono (hd n hn).1 hj)
  have hmaps : ∀ n ∈ S, d n ∈ DF := fun n hn => by
    rw [Set.Finite.mem_toFinset]; exact ⟨hdsmooth n hn, (hd n hn).2⟩
  -- the cofactor
  have hval : ∀ n ∈ S, (n : ℝ) = P.val (d n) * P.val (e n - d n) := by
    intro n hn
    rw [← P.val_add, add_tsub_cancel_of_le (hd n hn).1, (he n hn).2]
  -- fibres
  have hfib : ∀ δ ∈ DF, ((S.filter (fun n => d n = δ)).card : ℝ) ≤ C := by
    intro δ hδ
    rw [Set.Finite.mem_toFinset] at hδ
    have hfinW := P.finite_window δ u h
    refine le_trans ?_ (hW δ hδ.1 hδ.2.1 hδ.2.2)
    have key := Set.ncard_le_ncard_of_injOn
      (s := ((S.filter (fun n => d n = δ) : Finset ℝ) : Set ℝ)) (fun n => e n - d n) ?_ ?_ hfinW
    · rw [Set.ncard_coe_finset] at key
      exact_mod_cast key
    · intro n hn
      rw [Finset.coe_filter] at hn
      obtain ⟨hnS, hnd⟩ := hn
      simp only [Set.mem_setOf_eq]
      rw [← hnd, ← hval n hnS]
      exact ⟨(hmemS n hnS).2.1, (hmemS n hnS).2.2⟩
    · intro n hn n' hn' heq
      rw [Finset.coe_filter] at hn hn'
      have h1 := hval n hn.1
      have h2 := hval n' hn'.1
      simp only at heq
      rw [heq, hn.2] at h1
      rw [hn'.2] at h1 h2
      exact_mod_cast h1.trans h2.symm
  have hcard : (S.card : ℝ) ≤ DF.card * C := by
    rw [Finset.card_eq_sum_card_fiberwise (fun n hn => Finset.mem_coe.mpr (hmaps n (Finset.mem_coe.mp hn)))]
    push_cast
    calc (∑ δ ∈ DF, ((S.filter (fun n => d n = δ)).card : ℝ)) ≤ ∑ _δ ∈ DF, C :=
          Finset.sum_le_sum hfib
      _ = DF.card * C := by rw [Finset.sum_const, nsmul_eq_mul]
  have hDcard : (DF.card : ℝ) ≤ P.smoothCountN (z * h) z := by
    unfold smoothCountN
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    norm_cast
    exact Set.ncard_le_ncard (fun d hd => ⟨hd.1, hd.2.2⟩) (P.finite_smooth_le (z * h) z)
  unfold Absorbed.localCountA
  rw [Set.ncard_eq_toFinset_card _ hAfin, ← hSdef]
  calc (S.card : ℝ) ≤ DF.card * C := hcard
    _ ≤ P.smoothCountN (z * h) z * C := mul_le_mul_of_nonneg_right hDcard hC
    _ = C * P.smoothCountN (z * h) z := by ring

/-- **Lemma 6.26, steps (i)–(v)**: with Rankin's bound for the realised system,
`#(A ∩ [u, u + h]) ≤ C (z h)^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}` for every `σ > 0`. -/
theorem localCount_le_rankin {A : Set ℝ} {u h z C σ : ℝ} (hh : 1 ≤ h) (hu : h < u) (hz : 0 ≤ z)
    (hC : 0 ≤ C) (hσ : 0 < σ)
    (hS : ∀ n ∈ A, u ≤ n → (n : ℝ) ≤ u + h → ∃ e ∈ P.smoothElems z, P.val e = n)
    (hW : ∀ d ∈ P.smoothElems z, h < P.val d → P.val d ≤ z * h →
      ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.ncard : ℝ) ≤ C) :
    (Absorbed.localCountA A u (u + h) : ℝ) ≤ C * ((z * h) ^ σ * P.rankinProd z σ) :=
  (P.localCount_le_divisor hh hu hC hS hW).trans
    (mul_le_mul_of_nonneg_left (P.smoothCountN_le_rankin hσ (by positivity) z) hC)

/-- **Lemma 6.26 from its steps.** Let `z = 2y`. Suppose
* (i) every `n ∈ A ∩ [u, u + h]` is the value of a `2y`-smooth element of `N`;
* (iv) each window `[u/d, (u + h)/d]`, `d` smooth in `(h, 2yh]`, holds at most `C_d` elements;
* (v) Rankin's estimate for the realised primes at `Y = 2yh`:
  `Ψ_N(2yh, 2y) ≤ 2yh · exp(-0.9 u₀ log u₀)`;
* (81) `0.9 u₀ log u₀ ≥ log(2y) + log C_d + 4 log L`.

Then `#(A ∩ [u, u + h]) ≤ h L^{-4}` (step (vi)). -/
theorem lemma626_of_steps {A : Set ℝ} {u h y Cd u0 L : ℝ} (hh : 1 ≤ h) (hu : h < u)
    (hy : 0 < y) (hCd : 0 < Cd) (hL : 0 < L)
    (hS : ∀ n ∈ A, u ≤ n → (n : ℝ) ≤ u + h → ∃ e ∈ P.smoothElems (2 * y), P.val e = n)
    (hW : ∀ d ∈ P.smoothElems (2 * y), h < P.val d → P.val d ≤ 2 * y * h →
      ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.ncard : ℝ) ≤ Cd)
    (hR : P.smoothCountN (2 * y * h) (2 * y) ≤ 2 * y * h * Real.exp (-(0.9 * u0 * Real.log u0)))
    (h81 : Real.log (2 * y) + Real.log Cd + 4 * Real.log L ≤ 0.9 * u0 * Real.log u0) :
    (Absorbed.localCountA A u (u + h) : ℝ) ≤ h * L ^ (-4 : ℤ) := by
  have h1 := P.localCount_le_divisor hh hu hCd.le hS hW
  have hh0 : 0 < h := by linarith
  have key : Cd * (2 * y * h * Real.exp (-(0.9 * u0 * Real.log u0))) ≤ h * L ^ (-4 : ℤ) := by
    have e1 : Cd * (2 * y * h * Real.exp (-(0.9 * u0 * Real.log u0))) =
        h * Real.exp (Real.log Cd + Real.log (2 * y) - 0.9 * u0 * Real.log u0) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log hCd, Real.exp_log (by positivity),
        Real.exp_neg]
      field_simp
    have e2 : L ^ (-4 : ℤ) = Real.exp (-(4 * Real.log L)) := by
      rw [Real.exp_neg, ← Real.log_rpow hL, Real.exp_log (by positivity), zpow_neg]
      norm_cast
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hh0.le
  exact h1.trans ((mul_le_mul_of_nonneg_left hR hCd.le).trans key)

end BeurlingSystem

end
