module

public import RequestProject.Beurling.Noise.RML9XBGamma

/-!
# Proposition 5.31(iii), part (γ′): the `𝔹₂` pairs with a large cofactor `w > W₁`

Fix `d` with `u = y/d`, `r = u/X₀`. On the window `w ∈ r[1 ∓ 1.7δ]` (`win_val`), so `w > W₁`
forces `u ≥ W₁X₀/3`, `w^{ε-2} ≤ 2 r^{-3/4}/w`, and Lemma 5.29 gives `∑_w 1/w ≤ 7.05`.

* `win_part_le` : `∑_{w > W₁} [Win] (λ₀²/4) w^{ε-2} R(d) ≤ [u ≥ W₁X₀/3] 3.6 r^{-3/4} R(d)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **(γ′), the `𝔹₂` pairs at a fixed `d`.** -/
lemma win_part_le {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hXm1 : 1 ≤ X0m)
    (hSR : ShortRecipLow P X0 y) {d : ℕ} (hd : d ∈ Dset P X0m y) :
    ∑ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      (if Win P H y X0 (d * w)
        then lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d else 0) ≤
    if X0 * Real.exp 100 / 3 ≤ posn P.labelVal y d
      then 3.6 * (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d else 0 := by
  have hXm0 := hP.X0m_pos
  have hy0 : 0 < y := by linarith
  have hd2 := (mem_Dset.mp hd).2
  have hd0 : d ≠ 0 := by omega
  set u := posn P.labelVal y d with hu
  have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
  have hVd := KR.valN_labelVal_pos P d
  have hH0 := hP.reg.pos X0
  have hXm : X0m ≤ X0 := by rw [hX0e]; linarith
  have hX0 : 0 < X0 := lt_of_lt_of_le hXm0 hXm
  have hu0 : 0 < u := div_pos hy0 hVd
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hW1 : (30 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  set a := 1.7 * (H X0 / X0) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 0.0017 := by rw [ha]; linarith
  set r := u / X0 with hr
  have hNr : y / X0 / Vl P d = r := by
    rw [hr, hu]; unfold posn; rw [div_right_comm]
  -- the window of a cofactor
  have hwin : ∀ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      Win P H y X0 (d * w) → r * (1 - a) ≤ Vl P w ∧ Vl P w ≤ r * (1 + a) := by
    intro w hw hW
    have hw2 := (mem_Dset.mp (Finset.mem_filter.mp hw).1).2
    have hv := win_val (P := P) hX0 hH0.le hδ hy0 hW
    rw [show LemmaM.valN P.labelVal (d * w) = Vl P w * Vl P d by
      rw [mul_comm d w]; exact Vl_mul_eq (by omega) hd0] at hv
    have := (win_prod_iff hVd).mp hv
    rwa [hNr] at this
  by_cases hex : ∃ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      Win P H y X0 (d * w)
  · obtain ⟨w0, hw0F, hw0W⟩ := hex
    have hW0 := hwin w0 hw0F hw0W
    have hVw0 : Real.exp 100 < Vl P w0 := not_le.mp (Finset.mem_filter.mp hw0F).2
    have hr3 : Real.exp 100 / 3 ≤ r := by nlinarith
    have hu3 : X0 * Real.exp 100 / 3 ≤ u := by
      have : u = X0 * r := by rw [hr]; field_simp
      rw [this]; nlinarith
    rw [if_pos hu3]
    have hr1 : 1 ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    have hr34' : 0 < r ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hr0 _
    have hr34 : r ^ (-(3 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    set T := ((Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100)).filter
      (fun w => Win P H y X0 (d * w)) with hT
    have hrY : r ≤ y / X0 := by
      have := posn_le_half hp2 hy0 hd2 (P := P)
      have hX0p : 0 < X0 := by
        have := (hP.reg.pos X0).le; rw [hX0e] at hXm0; linarith
      rw [hr]
      exact div_le_div_of_nonneg_right (by linarith) hX0p.le
    have hSRT := sum_labels_le_SRL hSR hr1 hrY ha0 (by linarith) T
      (fun w hw => by
        have := (mem_Dset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2; omega)
      (fun w hw => by
        obtain ⟨hwF, hwW⟩ := Finset.mem_filter.mp hw
        exact hwin w hwF hwW)
    have hsum : ∑ w ∈ T, 1 / Vl P w ≤ 7.05 := by nlinarith
    -- `w^{ε-2} ≤ 2 r^{-3/4}/w`
    have hpt : ∀ w ∈ T, Vl P w ^ (ε - 2) ≤ 2 * r ^ (-(3 / 4 : ℝ)) * (1 / Vl P w) := by
      intro w hw
      obtain ⟨hwF, hwW⟩ := Finset.mem_filter.mp hw
      have hW := hwin w hwF hwW
      have hVw := KR.valN_labelVal_pos P w
      have hr2 : r / 2 ≤ Vl P w := by nlinarith
      have e1 : Vl P w ^ (ε - 2) = Vl P w ^ (ε - 1) * (1 / Vl P w) := by
        rw [show ε - 2 = (ε - 1) - 1 by ring, Real.rpow_sub_one hVw.ne']; ring
      rw [e1]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hVw1 : 1 ≤ Vl P w := by linarith
      calc Vl P w ^ (ε - 1) ≤ Vl P w ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hVw1 (by linarith [hP.eps_le])
        _ ≤ (r / 2) ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hr2 (by norm_num)
        _ = r ^ (-(3 / 4 : ℝ)) * (1 / 2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
            rw [div_eq_mul_one_div r 2, Real.mul_rpow hr0.le (by norm_num)]
        _ ≤ r ^ (-(3 / 4 : ℝ)) * 2 := by
            apply mul_le_mul_of_nonneg_left _ hr34'.le
            rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
            norm_num
            calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
        _ = 2 * r ^ (-(3 / 4 : ℝ)) := by ring
    have hl2 : lam0 ^ 2 / 4 ≤ 0.2506 := by nlinarith
    rw [← Finset.sum_filter]
    calc ∑ w ∈ T, lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d
        ≤ ∑ w ∈ T, lam0 ^ 2 / 4 * (2 * r ^ (-(3 / 4 : ℝ)) * (1 / Vl P w)) *
            Rd P tw X0m y ε d := by
          refine Finset.sum_le_sum fun w hw => ?_
          gcongr
          exact hpt w hw
      _ = lam0 ^ 2 / 4 * 2 * r ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d *
            ∑ w ∈ T, 1 / Vl P w := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_; ring
      _ ≤ 0.2506 * 2 * r ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d * 7.05 := by
          apply mul_le_mul _ hsum (Finset.sum_nonneg fun w _ =>
            (one_div_pos.mpr (KR.valN_labelVal_pos P w)).le) (by positivity)
          gcongr
      _ ≤ 3.6 * r ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d := by
          have : 0 ≤ r ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d := by positivity
          nlinarith
  · rw [Finset.sum_eq_zero fun w hw => if_neg (fun hN => hex ⟨w, hw, hN⟩)]
    split_ifs with hc
    · have : 0 ≤ (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_nonneg (div_nonneg hu0.le hX0.le) _
      positivity
    · exact le_rfl

end KR.RML9

end
