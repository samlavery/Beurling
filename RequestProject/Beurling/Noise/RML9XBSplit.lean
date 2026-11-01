module

public import RequestProject.Beurling.Noise.RML9XBBase

/-!
# Proposition 5.31(iii): the split of `𝔅(y)` into `𝔹₀` and the pairs `(d, w)`

`xbB_le_split` : for a start `y ≥ X₀⁻`,

  `𝔅(y) ≤ ½ S(y/X₀) + ∑_{w ∈ Dset} ∑_{d ∈ Dset} G(d, w)`,

with `S = SD … (1.7δ)` and `G(d, w) = stepBd(d, d·w)/V(d·w)`, where `stepBd` bounds a step term of
`𝔅` by its `X₀`-near part `½ TV(D_d)` (if the step is `X₀`-near) plus its `𝔹₂` part
`λ₀ ‖D_d‖_KR/(w H_n)`, both only on the window `Win` (`xbBstep_le_stepBd`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

open scoped Classical in
/-- The bound of a step term of `𝔅`: on the window, `X₀`-near part plus `𝔹₂` part. -/
noncomputable def stepBd (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m y X0 θ lam0 : ℝ)
    (d n : ℕ) : ℝ :=
  if Win P H y X0 n ∧ d ≠ 1 then
    (if X0Near P.labelVal y H X0m d n then 1 / 2 * TVD P H tw X0m y d else 0) +
    (if |posn P.labelVal y n - X0| ≤ (1 + θ) * H (posn P.labelVal y n) / 2 +
          1.02 * H (posn P.labelVal y d) / Vl P (n / d)
      then lam0 * KRD P H tw X0m y d / (Vl P (n / d) * H (posn P.labelVal y n)) else 0)
  else 0

/-- `G(d, w) = stepBd(d, d·w)/V(d·w)`. -/
noncomputable def Gpair (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m y X0 θ lam0 : ℝ)
    (d w : ℕ) : ℝ :=
  stepBd P H tw X0m y X0 θ lam0 d (d * w) / Vl P (d * w)

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma TVD_nonneg (d : ℕ) : 0 ≤ TVD P H tw X0m y d := by
  unfold TVD; positivity

lemma KRD_nonneg (d : ℕ) : 0 ≤ KRD P H tw X0m y d := by
  unfold KRD; positivity

lemma stepBd_nonneg {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hlam0 : 0 ≤ lam0)
    (d n : ℕ) : 0 ≤ stepBd P H tw X0m y X0 θ lam0 d n := by
  classical
  have hT := TVD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
  have hK := KRD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
  have hV := KR.valN_labelVal_pos P (n / d)
  have hHn := hP.reg.pos (posn P.labelVal y n)
  unfold stepBd
  split_ifs <;> positivity

lemma Gpair_nonneg {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hlam0 : 0 ≤ lam0)
    (d w : ℕ) : 0 ≤ Gpair P H tw X0m y X0 θ lam0 d w :=
  div_nonneg (stepBd_nonneg hP hlam0 d (d * w)) (KR.valN_labelVal_pos P _).le

/-- **The step bound.** -/
lemma xbBstep_le_stepBd {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (hlam0 : 0 ≤ lam0) {n d : ℕ}
    (hn : n ∈ levels P X0m y) (hd : d ∈ n.properDivisors) :
    xbBstep P H tw X0m y X0 θ lam0 d n ≤ stepBd P H tw X0m y X0 θ lam0 d n := by
  classical
  by_cases hw : Win P H y X0 n
  · have hT := TVD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
    have hK := KRD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
    have hV := KR.valN_labelVal_pos P (n / d)
    have hHn := hP.reg.pos (posn P.labelVal y n)
    have hb : 0 ≤ lam0 * KRD P H tw X0m y d / (Vl P (n / d) * H (posn P.labelVal y n)) := by
      positivity
    unfold xbBstep stepBd
    by_cases h1 : d = 1
    · simp only [h1, if_true, ne_eq, not_true_eq_false, and_false, if_false, le_refl]
    have hc : Win P H y X0 n ∧ d ≠ 1 := ⟨hw, h1⟩
    simp only [h1, if_false, hw, ne_eq, not_false_eq_true, and_self, if_true]
    split_ifs <;> linarith
  · have hfar : 1.6 * H X0 < |posn P.labelVal y n - X0| := by
      unfold Win at hw; push_neg at hw; exact hw
    rw [xbBstep_eq_zero_far hP hX0e hp2 hn hd hfar]
    exact stepBd_nonneg hP hlam0 d n

open scoped Classical in
/-- The `𝔹₀` term lies on the window. -/
lemma B0_le_win {ε θ X0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    {n : ℕ} (hn : n ∈ levels P X0m y) :
    (if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
      then |cN P tw X0m y n| / 2 else 0) ≤
    (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) := by
  classical
  have hX := hP.X0m_pos
  obtain ⟨hnA, -⟩ := Finset.mem_filter.mp hn
  have hz : X0m / 2 ≤ posn P.labelVal y n := posn_ge_of_mem_NAll hnA (by linarith)
  by_cases hB : |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
  · rw [if_pos hB]
    have hW : Win P H y X0 n := by
      have := near_of_bound hP hX0e hz (c1 := 1 / 2) (by norm_num) (by norm_num)
        (by have := hP.reg.pos X0; linarith)
      exact this
    rw [if_pos hW]
  · rw [if_neg hB]; split_ifs <;> positivity

lemma levels_val_le {n : ℕ} (hn : n ∈ levels P X0m y) (hX : 0 < X0m) :
    LemmaM.valN P.labelVal n ≤ 2 * y / X0m := by
  obtain ⟨hnA, -⟩ := Finset.mem_filter.mp hn
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hnA
  rw [mem_elems] at he
  rw [P.valN_iota]
  have : y / (X0m / 2) = 2 * y / X0m := by field_simp
  linarith

lemma levels_sub_Dset (hX : 0 < X0m) : levels P X0m y ⊆ Dset P X0m y := by
  intro n hn
  obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
  exact mem_Dset.mpr ⟨KR.mem_image_iota P (by omega) (levels_val_le hn hX), hn2⟩

lemma div_mem_Dset (hX : 0 < X0m) {n f : ℕ} (hn : n ∈ levels P X0m y)
    (hf : f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n)) :
    n / f ∈ Dset P X0m y ∧ f ∈ Dset P X0m y := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
  have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
  obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
  have hn0 : n ≠ 0 := by omega
  have hVn := levels_val_le hn hX
  have hm2 : 2 ≤ n / f := by
    have hpd : f ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hfn, hfn'⟩
    exact two_le_div_of_mem hpd
  constructor
  · refine mem_Dset.mpr ⟨KR.mem_image_iota P (by omega) ?_, hm2⟩
    exact (LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0).trans hVn
  · refine mem_Dset.mpr ⟨KR.mem_image_iota P (by omega) ?_, by omega⟩
    exact (LemmaM.valN_le_of_dvd _ hval hfn hn0).trans hVn

open scoped Classical in
/-- The `𝔹₀` sum is at most `½ S(y/X₀)`. -/
lemma B0_sum_le {ε θ X0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : 0 < X0)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hy : 0 < y) :
    ∑ n ∈ levels P X0m y, (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) /
        Vl P n ≤ 1 / 2 * SD P tw X0m y (1.7 * (H X0 / X0)) (y / X0) := by
  classical
  have hX := hP.X0m_pos
  have hH0 := (hP.reg.pos X0).le
  unfold SD
  rw [Finset.mul_sum]
  calc ∑ n ∈ levels P X0m y, (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) / Vl P n
      ≤ ∑ n ∈ Dset P X0m y, (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) / Vl P n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (levels_sub_Dset hX) fun n _ _ => ?_
        have := KR.valN_labelVal_pos P n
        split_ifs <;> positivity
    _ ≤ _ := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hV := KR.valN_labelVal_pos P n
        by_cases hW : Win P H y X0 n
        · rw [if_pos hW, if_pos (win_val hX0 hH0 hδ hy hW)]
          unfold Vl; field_simp; rfl
        · rw [if_neg hW]
          split_ifs
          · have := abs_nonneg (cN P tw X0m y n)
            simp only [zero_div]; positivity
          · simp

open scoped Classical in
/-- **The split of `𝔅(y)`.** -/
theorem xbB_le_split {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (hlam0 : 0 ≤ lam0) (hX0 : 0 < X0)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hy : 0 < y) :
    xbB P H tw X0m y X0 θ lam0 ≤ 1 / 2 * SD P tw X0m y (1.7 * (H X0 / X0)) (y / X0) +
      ∑ w ∈ Dset P X0m y, ∑ d ∈ Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  rw [xbB_eq]
  -- per level
  have hlev : ∀ n ∈ levels P X0m y, xbTerm P H tw X0m y X0 θ lam0 n ≤
      (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) / Vl P n +
      ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
        Gpair P H tw X0m y X0 θ lam0 f (n / f) := by
    intro n hn
    obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by omega
    have hVn := KR.valN_labelVal_pos P n
    unfold xbTerm
    have hpd : n.properDivisors = insert 1 (n.divisors.filter (fun d => 1 < d ∧ d < n)) := by
      ext d
      simp only [Nat.mem_properDivisors, Finset.mem_insert, Finset.mem_filter,
        Nat.mem_divisors]
      constructor
      · rintro ⟨hdn, hlt⟩
        rcases Nat.lt_or_ge d 2 with h | h
        · left
          interval_cases d
          · simp at hdn; omega
          · rfl
        · right; exact ⟨⟨hdn, hn0⟩, by omega, hlt⟩
      · rintro (rfl | ⟨⟨hdn, -⟩, -, hlt⟩)
        · exact ⟨one_dvd n, by omega⟩
        · exact ⟨hdn, hlt⟩
    have h1 : (1 : ℕ) ∉ n.divisors.filter (fun d => 1 < d ∧ d < n) := by simp
    rw [hpd, Finset.sum_insert h1]
    have hs1 : xbBstep P H tw X0m y X0 θ lam0 1 n = 0 := by unfold xbBstep; simp
    rw [hs1, zero_add, add_div, Finset.sum_div]
    apply add_le_add
    · exact div_le_div_of_nonneg_right (B0_le_win hP hX0e hn) hVn.le
    · refine Finset.sum_le_sum fun f hf => ?_
      have hfd := Finset.mem_filter.mp hf
      have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd.1
      have hfp : f ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hfn, hfd.2.2⟩
      unfold Gpair
      rw [Nat.mul_div_cancel' hfn]
      exact div_le_div_of_nonneg_right (xbBstep_le_stepBd hP hX0e hp2 hlam0 hn hfp) hVn.le
  calc ∑ n ∈ levels P X0m y, xbTerm P H tw X0m y X0 θ lam0 n
      ≤ ∑ n ∈ levels P X0m y, ((if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) /
          Vl P n + ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
            Gpair P H tw X0m y X0 θ lam0 f (n / f)) := Finset.sum_le_sum hlev
    _ = ∑ n ∈ levels P X0m y, (if Win P H y X0 n then |cN P tw X0m y n| / 2 else 0) /
          Vl P n + ∑ n ∈ levels P X0m y, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
            Gpair P H tw X0m y X0 θ lam0 f (n / f) := Finset.sum_add_distrib
    _ ≤ _ := by
        apply add_le_add (B0_sum_le hP hX0 hδ hy)
        exact sum_divisors_le _ (fun f m => Gpair_nonneg hP hlam0 f m)
          (fun n hn f hf => div_mem_Dset hX hn hf)

end KR.RML9

end
