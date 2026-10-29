module

public import RequestProject.Beurling.Noise.RML9XBGamma2

/-!
# Proposition 5.31(iii), part (γ′): the dyadic blocks of `R(d)`

`Rd_block_le` : for `X₀⁻/2 ≤ v ≤ y`, by Corollary 5.9 (`cor_5_9_full`) and the reindexing
`d = e·m` (the `m`-sums of Corollary 5.17, `hordSumsB`),
`∑_{y/d ∈ [v, 2v)} R(d) ≤ C_S((1 + A₀) log(2v) + A₁)/log y`, `A₀ = 2.0674`, `A₁ = 9.4091`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- The Saias constant `C_S = max(2.01 Φ_∞(10⁸), 1.4)` of Corollary 5.9. -/
noncomputable abbrev CSc : ℝ := max (2.01 * BSaias.PhiInf 100000000) 1.4

/-- A block of `Dset` lies in `NW y v`, so its sharp sum is `≤ W^sh_y(v)`. -/
lemma block_le_Wsh (hv : 0 < v) :
    ∑ d ∈ (Dset P X0m y).filter (fun d => v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v),
      |cN P tw X0m y d| / Vl P d ≤ P.Wsh tw X0m y v := by
  rw [Wsh_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnD, h1, h2⟩ := Finset.mem_filter.mp hn
    have := (mem_Dset.mp hnD).2
    exact (mem_NW P hv).mpr ⟨by omega, h1, h2⟩
  · intro n _ _; exact div_nonneg (abs_nonneg _) (KR.valN_labelVal_pos P n).le

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **The dyadic blocks of `R`** (Proposition 5.31(iii), (γ′)). -/
theorem Rd_block_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z)
    {ε : ℝ} (hε : ε ≤ 0.03) {v : ℝ} (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) :
    ∑ d ∈ Dset P X0m y, (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v
      then Rd P tw X0m y ε d else 0) ≤
      CSc * (3.0674 * Real.log (2 * v) + 9.4091) / Real.log y := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hXm0 := h.X0m_pos
  have hX1 : 1 < X0m := by
    by_contra hc; push_neg at hc
    have := Real.log_le_log hXm0 hc
    rw [Real.log_one] at this; linarith
  have hv0 : 0 < v := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2v : 0 ≤ Real.log (2 * v) := Real.log_nonneg (by linarith)
  have hCS : 0 ≤ CSc := le_max_of_le_right (by norm_num)
  have hWsh : ∀ w : ℝ, X0m / 2 ≤ w → w ≤ y →
      P.Wsh tw X0m y w ≤ CSc * Real.log (2 * w) / Real.log y := fun w h1 h2 =>
    cor_5_9_full h hXl ht htv hy h1 h2 hZ (P := P)
  set A := (Dset P X0m y).filter (fun d => v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v)
  rw [← Finset.sum_filter]
  unfold Rd
  rw [Finset.sum_add_distrib]
  set G : ℕ → ℕ → ℝ := fun f m => (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
    (|cN P tw X0m y f| / Vl P f) with hG
  have hG0 : ∀ f m, 0 ≤ G f m := by
    intro f m
    have h1 := KR.valN_labelVal_pos P m
    have h2 := KR.valN_labelVal_pos P f
    have h3 : 0 ≤ Vl P m ^ (ε - 2) := Real.rpow_nonneg h1.le _
    simp only [hG]; positivity
  set F : ℕ → Finset ℕ := fun m => (Dset P X0m y).filter (fun f =>
    v * Vl P m ≤ posn P.labelVal y f ∧ posn P.labelVal y f < 2 * (v * Vl P m)) with hF
  have h2 := sum_divisors_le (A := A) (M := Dset P X0m y) (F := F) G hG0 (by
    intro n hn f hf
    obtain ⟨hnD, hb1, hb2⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Dset.mp hnD).2; omega
    obtain ⟨hm, hfD⟩ := div_mem_Dset' hnD hf
    refine ⟨hm, Finset.mem_filter.mpr ⟨hfD, ?_⟩⟩
    have hfn : f ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
    have hpm := posn_mul (x := y) hval hfn hn0
    have hVm := KR.valN_labelVal_pos P (n / f)
    rw [hpm]
    constructor
    · exact mul_le_mul_of_nonneg_right hb1 hVm.le
    · have := mul_lt_mul_of_pos_right hb2 hVm; linarith)
  -- the inner sums
  have hin : ∀ m ∈ Dset P X0m y, ∑ f ∈ F m, G f m ≤
      CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) * Real.log (2 * v) +
      CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
        Real.log (Vl P m)) := by
    intro m _
    have hV := KR.valN_labelVal_pos P m
    have hV1 : 1 ≤ Vl P m := KR.one_le_valN_label P m
    have hHV : 0 ≤ (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hV.le _)
    have hlV := Real.log_nonneg hV1
    have hrhs : 0 ≤ CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) *
        Real.log (2 * v) + CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) *
          Vl P m ^ (ε - 2) * Real.log (Vl P m)) := by positivity
    simp only [hG, hF]
    rw [← Finset.mul_sum]
    by_cases hvm : v * Vl P m ≤ y
    · have hW := hWsh (v * Vl P m) (by nlinarith) hvm
      have hb := block_le_Wsh (P := P) (tw := tw) (X0m := X0m) (y := y)
        (show 0 < v * Vl P m by positivity)
      have hl : Real.log (2 * (v * Vl P m)) = Real.log (2 * v) + Real.log (Vl P m) := by
        rw [← mul_assoc, Real.log_mul (by positivity) hV.ne']
      rw [hl] at hW
      have := mul_le_mul_of_nonneg_left (hb.trans hW) hHV
      have e : (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
          (CSc * (Real.log (2 * v) + Real.log (Vl P m)) / Real.log y) =
          CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) *
            Real.log (2 * v) + CSc / Real.log y * ((BSCert.X0Band.Hord m : ℝ) *
              Vl P m ^ (ε - 2) * Real.log (Vl P m)) := by ring
      linarith
    · push_neg at hvm
      rw [Finset.sum_eq_zero, mul_zero]
      · exact hrhs
      · intro f hf
        exfalso
        obtain ⟨-, hf1, -⟩ := Finset.mem_filter.mp hf
        have hVf : 1 ≤ Vl P f := KR.one_le_valN_label P f
        have : posn P.labelVal y f ≤ y := div_le_self (by linarith) hVf
        linarith
  have hsB := hordSumsB P h hXl hε hZ (Dset P X0m y)
    (fun m hm => ⟨(mem_Dset.mp hm).2, Dset_val_le hm⟩)
  have h3 := Finset.sum_le_sum hin
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h3
  have h1 := (block_le_Wsh (P := P) (tw := tw) (X0m := X0m) (y := y) hv0).trans
    (hWsh v hv1 hv2)
  have hk : 0 ≤ CSc / Real.log y := by positivity
  have h4 : CSc / Real.log y * (∑ m ∈ Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) *
      Vl P m ^ (ε - 2)) * Real.log (2 * v) ≤ CSc / Real.log y * 2.0674 * Real.log (2 * v) := by
    gcongr; exact hsB.1
  have h5 : CSc / Real.log y * ∑ m ∈ Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) *
      Vl P m ^ (ε - 2) * Real.log (Vl P m) ≤ CSc / Real.log y * 9.4091 := by
    gcongr; exact hsB.2
  have e : CSc * (3.0674 * Real.log (2 * v) + 9.4091) / Real.log y =
      CSc * Real.log (2 * v) / Real.log y + (CSc / Real.log y * 2.0674 * Real.log (2 * v) +
        CSc / Real.log y * 9.4091) := by ring
  rw [e]
  apply add_le_add h1
  refine h2.trans (h3.trans ?_)
  linarith

end KR.RML9

end
