module

public import RequestProject.Beurling.Noise.RML9XBGamma4

/-!
# Proposition 5.31(iii), part (γ′): the pairs with a large cofactor `w > W₁ = e^{100}`

`gamma_le` : `∑_{w > W₁} ∑_d G(d, w) ≤ e^{-62} Λ/log y` (`Gpair_le_gamma`, `near_part_le`,
`win_part_le`, `dyadic_le` with `V₀ = W₁X₀/3`, `C_S ≤ 77`). The paper's bound is
`e^{-60} τ₀/J`; here `τ₀` is replaced by `Λ = log X₀` and `J` by `log y ≥ J`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma exp10_ge : 22000 ≤ Real.exp 10 := by
  have h := Real.exp_one_gt_d9
  rw [show (10 : ℝ) = (10 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  calc (22000 : ℝ) ≤ 2.718 ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith) 10

/-- `(W₁/3)^{-0.74} ≤ e^{-72.52}`. -/
lemma W1_rpow_le : (Real.exp 100 / 3) ^ (-(0.74 : ℝ)) ≤ Real.exp (-72.52) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have h98 : Real.exp 98 ≤ Real.exp 100 / 3 := by
    rw [le_div_iff₀ (by norm_num)]
    calc Real.exp 98 * 3 ≤ Real.exp 98 * Real.exp 2 :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = Real.exp 100 := by rw [← Real.exp_add]; norm_num
  calc (Real.exp 100 / 3) ^ (-(0.74 : ℝ)) ≤ Real.exp 98 ^ (-(0.74 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h98 (by norm_num)
    _ = Real.exp (-72.52) := by rw [← Real.exp_mul]; norm_num

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Proposition 5.31(iii), (γ′)**: the pairs with `w > W₁`. -/
theorem gamma_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {ε θ X0 lam0 : ℝ}
    (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2) (hδ : H X0 / X0 ≤ 1 / 1000)
    (hp2 : ∀ j, 2 ≤ P.p j) (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z) (hSR : ShortRecip P y) :
    ∑ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100), ∑ d ∈ Dset P X0m y,
        Gpair P H tw X0m y X0 θ lam0 d w ≤ Real.exp (-62) * Real.log X0 / Real.log y := by
  have hXm0 := hP.X0m_pos
  have hX1 : 1 < X0m := by
    by_contra hc; push_neg at hc
    have := Real.log_le_log hXm0 hc
    rw [Real.log_one] at this; linarith
  have hH0 := hP.reg.pos X0
  have hXm : X0m ≤ X0 := by rw [hX0e]; linarith
  have hX0 : 0 < X0 := lt_of_lt_of_le hXm0 hXm
  have hΛ : 100000000 ≤ Real.log X0 := hXl.trans (Real.log_le_log hXm0 hXm)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hε : ε ≤ 0.03 := by linarith [hP.eps_le]
  set V0 := X0 * Real.exp 100 / 3 with hV0
  have hW1 : (30 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  have hV0X : X0 ≤ V0 := by rw [hV0]; nlinarith
  set Fbig := (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100)
  -- the per-`d` bound
  have hpt : ∀ d ∈ Dset P X0m y, ∑ w ∈ Fbig,
      ((if X0Near P.labelVal y H X0m d (d * w)
        then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) +
      (if Win P H y X0 (d * w)
        then lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d else 0)) ≤
      if V0 ≤ posn P.labelVal y d then 10.63 * (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) *
        Rd P tw X0m y ε d else 0 := by
    intro d hd
    rw [Finset.sum_add_distrib]
    have h1 := near_part_le hP hX0e hδ hp2 ht hlam (by linarith) hy hX1.le hSR hd (tw := tw)
      (ε := ε)
    have h2 := win_part_le hP hX0e hδ hp2 hlam hlam1 hy hX1.le hSR hd (tw := tw) (ε := ε)
    refine (add_le_add h1 h2).trans ?_
    split_ifs
    · have : 0 ≤ (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d :=
        mul_nonneg (Real.rpow_nonneg (div_nonneg (div_nonneg (by linarith)
          (KR.valN_labelVal_pos P d).le) hX0.le) _) (Rd_nonneg ε d)
      nlinarith
    · simp
  have hD := dyadic_le h hXl ht htv hy hZ hε hXm hV0X (show (0 : ℝ) ≤ 10.63 by norm_num)
    (P := P) (tw := tw)
  have hCS : CSc ≤ 77 := CS_le
  have hCS0 : 0 ≤ CSc := le_max_of_le_right (by norm_num)
  have hVr : V0 / X0 = Real.exp 100 / 3 := by rw [hV0]; field_simp
  rw [hVr] at hD
  have hW := W1_rpow_le
  have hWp : 0 ≤ (Real.exp 100 / 3) ^ (-(0.74 : ℝ)) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ ∑ w ∈ Fbig, ∑ d ∈ Dset P X0m y,
          ((if X0Near P.labelVal y H X0m d (d * w)
            then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) +
          (if Win P H y X0 (d * w)
            then lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d else 0)) := by
        refine Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun d hd => ?_
        exact Gpair_le_gamma hP hX0e hX0 hδ hp2 ht hlam hy (mem_Dset.mp hd).2
          (mem_Dset.mp (Finset.mem_filter.mp hw).1).2
    _ = ∑ d ∈ Dset P X0m y, ∑ w ∈ Fbig,
          ((if X0Near P.labelVal y H X0m d (d * w)
            then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) +
          (if Win P H y X0 (d * w)
            then lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d else 0)) :=
        Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum hpt
    _ ≤ _ := hD
    _ ≤ 4 * (10.63 * 77 * (3.0675 * Real.log X0) / Real.log y * Real.exp (-72.52)) := by
        have hK : 3.0674 * Real.log X0 + 320 ≤ 3.0675 * Real.log X0 := by linarith
        have hK0 : 0 ≤ 3.0674 * Real.log X0 + 320 := by linarith
        gcongr
    _ ≤ Real.exp (-62) * Real.log X0 / Real.log y := by
        have he : Real.exp (-72.52) * Real.exp 10 ≤ Real.exp (-62) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by norm_num)
        have h10 := exp10_ge
        have hl : 0 ≤ Real.log X0 := by linarith
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hly]
        have hp := Real.exp_pos (-72.52)
        nlinarith [mul_le_mul_of_nonneg_left h10 hp.le]

end KR.RML9

end
