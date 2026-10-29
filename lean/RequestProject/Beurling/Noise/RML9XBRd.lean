module

public import RequestProject.Beurling.Noise.RML9XBSI

/-!
# Proposition 5.31(iii): window sums of `R(d)` (eq. (TVD-sums))

* `Dset_val_le`, `div_mem_Dset'` : `Dset` is closed under divisors `> 1`;
* `Rd_win_le` : for a window `M[1-a, 1+a]`,
  `∑_{d ∈ Dset, V(d) ∈ M[1-a,1+a]} R(d) ≤ S(M) + ∑_{m ∈ Dset} H_ord(m) m^{ε-2} S(M/m)`,
  the second line of (TVD-sums) (the reindexing `d = e·m`);
* `SD_le_harm` : the trivial bound `S(M) ≤ log(2y/X₀⁻) + 1` (`|c_e| ≤ 1`, harmonic bound).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma Dset_val_le {n : ℕ} (hn : n ∈ Dset P X0m y) : Vl P n ≤ 2 * y / X0m := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (mem_Dset.mp hn).1
  rw [show Vl P (iota e) = P.val e from P.valN_iota e]
  exact (P.mem_elems).mp he

lemma div_mem_Dset' {n f : ℕ} (hn : n ∈ Dset P X0m y)
    (hf : f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n)) :
    n / f ∈ Dset P X0m y ∧ f ∈ Dset P X0m y := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
  have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
  have hn2 := (mem_Dset.mp hn).2
  have hn0 : n ≠ 0 := by omega
  have hVn := Dset_val_le hn
  have hm2 : 2 ≤ n / f := by
    have hpd : f ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hfn, hfn'⟩
    exact two_le_div_of_mem hpd
  constructor
  · refine mem_Dset.mpr ⟨KR.mem_image_iota P (by omega) ?_, hm2⟩
    exact (LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0).trans hVn
  · refine mem_Dset.mpr ⟨KR.mem_image_iota P (by omega) ?_, by omega⟩
    exact (LemmaM.valN_le_of_dvd _ hval hfn hn0).trans hVn

/-- The window condition for a product: `V(e)V(m) ∈ M[1-a,1+a] ⇔ V(e) ∈ (M/V(m))[1-a,1+a]`. -/
lemma win_prod_iff {a M Ve Vm : ℝ} (hm : 0 < Vm) :
    (M * (1 - a) ≤ Ve * Vm ∧ Ve * Vm ≤ M * (1 + a)) ↔
      (M / Vm * (1 - a) ≤ Ve ∧ Ve ≤ M / Vm * (1 + a)) := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hm, le_div_iff₀ hm]

open scoped Classical in
/-- **(TVD-sums), the window form**:
`∑_{V(d) ∈ M[1∓a]} R(d) ≤ S(M) + ∑_m H_ord(m) m^{ε-2} S(M/m)`. -/
lemma Rd_win_le (ε a M : ℝ) :
    ∑ d ∈ Dset P X0m y, (if M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a)
      then Rd P tw X0m y ε d else 0) ≤
    SD P tw X0m y a M + ∑ m ∈ Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
      SD P tw X0m y a (M / Vl P m) := by
  set G : ℕ → ℕ → ℝ := fun f m => (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
    (if M / Vl P m * (1 - a) ≤ Vl P f ∧ Vl P f ≤ M / Vl P m * (1 + a)
      then |cN P tw X0m y f| / Vl P f else 0) with hG
  have hG0 : ∀ f m, 0 ≤ G f m := by
    intro f m
    have h1 := KR.valN_labelVal_pos P m
    have h2 := KR.valN_labelVal_pos P f
    have h3 : 0 ≤ Vl P m ^ (ε - 2) := Real.rpow_nonneg h1.le _
    simp only [hG]
    split_ifs
    · exact mul_nonneg (by positivity) (div_nonneg (abs_nonneg _) h2.le)
    · simp
  have hpt : ∀ d ∈ Dset P X0m y, (if M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a)
      then Rd P tw X0m y ε d else 0) =
      (if M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a)
        then |cN P tw X0m y d| / Vl P d else 0) +
      ∑ f ∈ d.divisors.filter (fun f => 1 < f ∧ f < d), G f (d / f) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Dset.mp hd).2; omega
    have hsum : ∀ f ∈ d.divisors.filter (fun f => 1 < f ∧ f < d),
        G f (d / f) = if M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a) then
          (BSCert.X0Band.Hord (d / f) : ℝ) * Vl P (d / f) ^ (ε - 2) *
            (|cN P tw X0m y f| / Vl P f) else 0 := by
      intro f hf
      have hfd : f ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
      have hm := KR.valN_labelVal_pos P (d / f)
      have hiff := win_prod_iff (a := a) (M := M) (Ve := Vl P f) hm
      rw [← Vl_eq_mul hfd hd0] at hiff
      simp only [hG]
      by_cases hc : M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a)
      · rw [if_pos hc, if_pos (hiff.mp hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h)), mul_zero]
    rw [Finset.sum_congr rfl hsum]
    split_ifs
    · rfl
    · simp
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  apply add_le_add le_rfl
  calc ∑ d ∈ Dset P X0m y, ∑ f ∈ d.divisors.filter (fun f => 1 < f ∧ f < d), G f (d / f)
      ≤ ∑ m ∈ Dset P X0m y, ∑ f ∈ Dset P X0m y, G f m :=
        sum_divisors_le G hG0 fun n hn f hf => div_mem_Dset' hn hf
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [hG, ← Finset.mul_sum]
        rfl

/-- The trivial bound `S(M) ≤ log(2y/X₀⁻) + 1`. -/
lemma SD_le_harm {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (ht : ∀ r, r.Prime → 0 < tw r) (hX : 0 < X0m) (hy : X0m ≤ y)
    (hZ : 2 * y / X0m ≤ Z) (a M : ℝ) :
    SD P tw X0m y a M ≤ Real.log (2 * y / X0m) + 1 := by
  classical
  have h1 : 1 ≤ 2 * y / X0m := by rw [le_div_iff₀ hX]; linarith
  calc SD P tw X0m y a M
      ≤ ∑ el ∈ P.elems (2 * y / X0m), 1 / P.val el := by
        unfold SD
        refine (sum_Dset_le _ (fun n => ?_)).trans (Finset.sum_le_sum fun el _ => ?_)
        · split_ifs
          · exact div_nonneg (abs_nonneg _) (KR.valN_labelVal_pos P n).le
          · exact le_rfl
        · have hc : |cN P tw X0m y (iota el)| ≤ 1 := by
            unfold cN
            rw [mass_eq_coeff]
            exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht
              (fun r _ => P.one_le_labelVal r) hX.le hy (iota_pos el)
          rw [P.valN_iota]
          split_ifs
          · exact div_le_div_of_nonneg_right hc (P.val_pos el).le
          · exact (one_div_pos.mpr (P.val_pos el)).le
    _ ≤ Real.log (2 * y / X0m) + 1 := h.harm_le h1 hZ

end KR.RML9

end
