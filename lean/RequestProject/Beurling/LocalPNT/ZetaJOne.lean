module

public import RequestProject.Beurling.LocalPNT.HBS

/-!
# Step 2 of the proof of Theorem 5.24: `ζ_J(1) = ∏_{p ≤ y} (1 - 1/p)^{-1} ≪ (log y)^2`

From Lemma 5.1(iii), (iv) on `[1, y]`: `∑_{p ≤ y} 1/p ≤ log log y + 5.3`, hence
`∏_{p ≤ y} (1 - 1/p)^{-1} ≤ e^{11} (log y)^2`. (The paper has `P_y(1) ≤ e^{4.5} log y`; only a
polynomial bound in `log y` is used.)
-/

@[expose] public section

open Set Real Finset Construction

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma p_ge_two' {j : ℕ} (hj : P.p j ≤ y) : 2 ≤ P.p j := h.hbs.p_ge_two hj

/-- `∑_{p ≤ y} 1/p ≤ log log y + 5.3`. -/
theorem sum_inv_p_le : ∑ j ∈ P.primesLe y, 1 / P.p j ≤ Real.log (Real.log y) + 5.3 := by
  have H := h.hbs
  have hy2 : 2 ≤ y := by linarith [h.y_ge, h.Xm_ge_e7, h.Xm_le]
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe y) (fun j => P.p j ≤ 2)]
  -- the primes `p ≤ 2` are `= 2`, at most `1.63/ (1/2)` of them, by Lemma 5.1(iii) at `x = 2`
  have hS := (H.Sp_sub_log_mem (x := 2) (by norm_num) hy2).2
  have hfilt : (P.primesLe y).filter (fun j => P.p j ≤ 2) = P.primesLe 2 := by
    ext j; simp only [mem_filter, BeurlingSystem.mem_primesLe]
    exact ⟨fun h => h.2, fun h2 => ⟨h2.trans hy2, h2⟩⟩
  have h2eq : ∀ j ∈ P.primesLe 2, P.p j = 2 := by
    intro j hj
    rw [BeurlingSystem.mem_primesLe] at hj
    exact le_antisymm hj (h.p_ge_two' (hj.trans hy2))
  have hA : ∑ j ∈ P.primesLe 2, 1 / P.p j ≤ 1.63 := by
    have e1 : ∑ j ∈ P.primesLe 2, 1 / P.p j = (P.primesLe 2).card * (1 / 2) := by
      rw [Finset.sum_congr rfl (fun j hj => by rw [h2eq j hj]), Finset.sum_const, nsmul_eq_mul]
    have e2 : P.Sp 2 = (P.primesLe 2).card * (Real.log 2 / 2) := by
      unfold BeurlingSystem.Sp
      rw [Finset.sum_congr rfl (fun j hj => by rw [h2eq j hj]), Finset.sum_const, nsmul_eq_mul]
    rw [e2] at hS
    rw [e1]
    have hl1 := Real.log_two_gt_d9
    have hl2 := Real.log_two_lt_d9
    have hc : (0 : ℝ) ≤ (P.primesLe 2).card := Nat.cast_nonneg _
    nlinarith
  -- the primes `2 < p ≤ y`, Lemma 5.1(iv)
  have hB := H.mertens_iv (y := 2) (x := y) le_rfl hy2 le_rfl
  have hfilt2 : (P.primesLe y).filter (fun j => ¬ P.p j ≤ 2) =
      (P.primesLe y).filter (fun j => 2 < P.p j) := by
    ext j; simp only [mem_filter, not_le]
  rw [hfilt, hfilt2]
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog : Real.log (Real.log y / Real.log 2) = Real.log (Real.log y) - Real.log (Real.log 2) :=
    Real.log_div hly.ne' (by positivity)
  have hll2 : -0.4 ≤ Real.log (Real.log 2) := by
    have h4 : Real.exp (-0.4) ≤ Real.log 2 := by
      have h3 : (1.48 : ℝ) ≤ Real.exp 0.4 := by
        have := Real.quadratic_le_exp_of_nonneg (x := (0.4 : ℝ)) (by norm_num)
        nlinarith
      have h5 : Real.exp (-0.4) * Real.exp 0.4 = 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (-0.4)]
    have := Real.log_le_log (Real.exp_pos _) h4
    rwa [Real.log_exp] at this
  have hab := (abs_le.mp hB).2
  have h22 : 2.20 / Real.log 2 ≤ 3.18 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`ζ_J(1) = ∏_{p ≤ y} (1 - 1/p)^{-1} ≤ e^{11} (log y)^2`**. -/
theorem zetaJ_one_le :
    ∏ j ∈ P.primesLe y, (1 - P.p j ^ (-1 : ℝ))⁻¹ ≤ Real.exp 11 * Real.log y ^ (2 : ℝ) := by
  have hy2 : 2 ≤ y := by linarith [h.y_ge, h.Xm_ge_e7, h.Xm_le]
  have hly : 1 ≤ Real.log y := by
    have : Real.log 3 ≤ Real.log y := Real.log_le_log (by norm_num) (by
      have := h.y_ge; have := h.Xm_ge_e7; have := h.Xm_le; linarith)
    have h3 : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hpos : ∀ j ∈ P.primesLe y, 0 < (1 - P.p j ^ (-1 : ℝ))⁻¹ := by
    intro j hj
    have h2 := h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)
    rw [Real.rpow_neg_one]
    have : (P.p j)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    exact inv_pos.mpr (by linarith)
  have hprod_pos : 0 < ∏ j ∈ P.primesLe y, (1 - P.p j ^ (-1 : ℝ))⁻¹ :=
    Finset.prod_pos hpos
  rw [← Real.exp_log hprod_pos, Real.log_prod (fun j hj => (hpos j hj).ne')]
  have hterm : ∀ j ∈ P.primesLe y, Real.log (1 - P.p j ^ (-1 : ℝ))⁻¹ ≤ 2 * (1 / P.p j) := by
    intro j hj
    have h2 := h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)
    rw [Real.rpow_neg_one, Real.log_inv]
    set x := (P.p j)⁻¹ with hx
    have hx0 : 0 < x := inv_pos.mpr (by linarith)
    have hx1 : x ≤ 1 / 2 := by rw [hx, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    rw [one_div, ← hx]
    -- `-log(1 - x) ≤ x/(1 - x) ≤ 2x`, and in fact `≤ x + x² ≤ 3x/2`
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - x) by
      apply div_pos one_pos; linarith)
    rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub] at hl
    have hx2 : 1 - x ≠ 0 := by linarith
    have e : 1 / (1 - x) - 1 = x / (1 - x) := by field_simp; ring
    rw [e] at hl
    have : x / (1 - x) ≤ x + 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hsum := h.sum_inv_p_le
  have hS : ∑ j ∈ P.primesLe y, Real.log (1 - P.p j ^ (-1 : ℝ))⁻¹ ≤
      2 * (Real.log (Real.log y) + 5.3) := by
    calc _ ≤ ∑ j ∈ P.primesLe y, 2 * (1 / P.p j) := Finset.sum_le_sum hterm
      _ = 2 * ∑ j ∈ P.primesLe y, 1 / P.p j := by rw [Finset.mul_sum]
      _ ≤ _ := by nlinarith
  have hpow : Real.log y ^ (2 : ℝ) = Real.exp (2 * Real.log (Real.log y)) := by
    rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end LPHyp

end LocalPNT

end
