module

public import RequestProject.Beurling.Noise.RML9XBBeta3

/-!
# Proposition 5.31(iii), part (γ′): the `X₀`-near pairs with a large cofactor `w > W₁`

Fix `d` with `u = y/d`. The `X₀`-near condition `|y/(dw) - X₀⁻| ≤ 1.02 H(u)/w` puts `w` in
`(u/X₀⁻)[1 ∓ ρ]`, `ρ = 1.02 H(u)/u ≤ 1.02 δ (u/X₀)^{ε-1}` (eq. (RH)), and forces
`u ≥ W₁X₀/3`; Lemma 5.29 (`ShortRecip`) then gives `∑_w 1/w ≤ 7.03 (u/X₀)^{-3/4}`, and
`½ TV(D_d)/d ≤ R(d)` (`TVD_div_le_Rd`).

* `near_part_le` : `∑_{w > W₁} [X₀-near] ½ TV(D_d)/(d w) ≤ [u ≥ W₁X₀/3] 7.03 (u/X₀)^{-3/4} R(d)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- `y/d ≥ X₀⁻/2` on `Dset`. -/
lemma posn_ge_of_Dset (hX : 0 < X0m) {d : ℕ} (hd : d ∈ Dset P X0m y) :
    X0m / 2 ≤ posn P.labelVal y d := by
  have hV := Dset_val_le hd
  have hVp := KR.valN_labelVal_pos P d
  unfold posn
  rw [le_div_iff₀ hVp]
  rw [le_div_iff₀ hX] at hV
  change X0m / 2 * Vl P d ≤ y
  nlinarith

/-- `y/d ≤ y/2` for `d ≥ 2`. -/
lemma posn_le_half (hp2 : ∀ j, 2 ≤ P.p j) (hy : 0 < y) {d : ℕ} (hd : 2 ≤ d) :
    posn P.labelVal y d ≤ y / 2 := by
  have h2 : (2 : ℝ) ≤ LemmaM.valN P.labelVal d := two_le_valN (fun p _ => hp2 _) hd
  unfold posn
  exact div_le_div_of_nonneg_left hy.le (by norm_num) h2

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **(γ′), the `X₀`-near pairs at a fixed `d`.** -/
lemma near_part_le {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam4 : lam0 ≤ 4) (hy : X0m ≤ y) (hXm1 : 1 ≤ X0m)
    (hSR : ShortRecipLow P X0 y) {d : ℕ} (hd : d ∈ Dset P X0m y) :
    ∑ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      (if X0Near P.labelVal y H X0m d (d * w)
        then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) ≤
    if X0 * Real.exp 100 / 3 ≤ posn P.labelVal y d
      then 7.03 * (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d else 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hXm0 := hP.X0m_pos
  have hy0 : 0 < y := by linarith
  have hd2 := (mem_Dset.mp hd).2
  have hd0 : d ≠ 0 := by omega
  set u := posn P.labelVal y d with hu
  have hu2 : X0m / 2 ≤ u := posn_ge_of_Dset hXm0 hd
  have hHu := hP.reg.pos u
  have hHsmall := hP.small u hu2
  have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
  have hTV := TVD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
  have hVd := KR.valN_labelVal_pos P d
  have hH0 := hP.reg.pos X0
  have hXm : X0m ≤ X0 := by rw [hX0e]; linarith
  have hX0 : 0 < X0 := lt_of_lt_of_le hXm0 hXm
  have hHX : H X0 ≤ X0 / 1000 := by rw [div_le_iff₀ hX0] at hδ; linarith
  have hXm2 : X0 ≤ 2 * X0m := by rw [hX0e]; linarith
  have hW1 : (30 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  -- the window of a near cofactor
  have hwin : ∀ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      X0Near P.labelVal y H X0m d (d * w) →
      |u - Vl P w * X0m| ≤ 1.02 * H u := by
    intro w hw hN
    have hw2 := (mem_Dset.mp (Finset.mem_filter.mp hw).1).2
    have hVw := KR.valN_labelVal_pos P w
    unfold X0Near at hN
    have hdw : d * w / d = w := Nat.mul_div_cancel_left w (by omega)
    have hpm := posn_mul (x := y) hval (Dvd.intro w rfl) (mul_ne_zero hd0 (by omega))
    rw [hdw] at hpm hN
    rw [← hu] at hpm hN
    have e : u - Vl P w * X0m = (posn P.labelVal y (d * w) - X0m) * Vl P w := by
      rw [hpm]; ring
    rw [e, abs_mul, abs_of_pos hVw]
    have := mul_le_mul_of_nonneg_right hN hVw.le
    rwa [div_mul_cancel₀ _ hVw.ne'] at this
  by_cases hex : ∃ w ∈ (Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100),
      X0Near P.labelVal y H X0m d (d * w)
  · obtain ⟨w0, hw0F, hw0N⟩ := hex
    have hW0 := hwin w0 hw0F hw0N
    have hVw0 : Real.exp 100 < Vl P w0 := not_le.mp (Finset.mem_filter.mp hw0F).2
    rw [abs_le] at hW0
    -- `u ≥ W₁ X₀/3`
    have hu3 : X0 * Real.exp 100 / 3 ≤ u := by
      have : Real.exp 100 * X0m ≤ 1.102 * u := by nlinarith
      nlinarith
    rw [if_pos hu3]
    have huX : X0 ≤ u := by nlinarith
    set r := u / X0 with hr
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hX0]; linarith
    have hr0 : 0 < r := by linarith
    -- `ρ = 1.02 H(u)/u ≤ 1.02 δ r^{-3/4}`
    have hRH : H u ≤ r ^ ε * H X0 := by
      have := hP.RH X0 r (by linarith) hr1
      rwa [show X0 * r = u by rw [hr]; field_simp] at this
    have hu0 : 0 < u := by linarith
    set ρ := 1.02 * H u / u with hρ
    have hρ0 : 0 < ρ := by positivity
    have hpow : r ^ (ε - 1) ≤ r ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [hP.eps_le])
    have hρδ : ρ ≤ 1.02 * (H X0 / X0) * r ^ (-(3 / 4 : ℝ)) := by
      have e : r ^ ε * H X0 / u = H X0 / X0 * r ^ (ε - 1) := by
        rw [Real.rpow_sub_one hr0.ne', hr]; field_simp
      have h1 : H u / u ≤ r ^ ε * H X0 / u := div_le_div_of_nonneg_right hRH hu0.le
      rw [e] at h1
      have h2 : H X0 / X0 * r ^ (ε - 1) ≤ H X0 / X0 * r ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      rw [hρ, mul_div_assoc]; nlinarith
    have hr34 : r ^ (-(3 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    have hr34' : 0 < r ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hr0 _
    have hρ1 : ρ ≤ 0.01 := by
      have : 1.02 * (H X0 / X0) * r ^ (-(3 / 4 : ℝ)) ≤ 1.02 * (1 / 1000) * 1 := by
        apply mul_le_mul (by linarith) hr34 hr34'.le (by norm_num)
      linarith
    -- Lemma 5.29 on `(u/X₀⁻)[1 ∓ ρ]`
    set M := u / X0m with hM
    set T := ((Dset P X0m y).filter (fun w => ¬ Vl P w ≤ Real.exp 100)).filter
      (fun w => X0Near P.labelVal y H X0m d (d * w)) with hT
    have hM1 : 1 ≤ M := by rw [hM, le_div_iff₀ hXm0]; nlinarith
    have hMY : M ≤ y / X0 := by
      have := posn_le_half hp2 hy0 hd2 (P := P)
      have hHX0 : 0 ≤ H X0 := (hP.reg.pos X0).le
      have hX0p : 0 < X0 := by rw [hX0e] at hXm0; linarith
      have hX2 : X0 ≤ 2 * X0m := by
        have : H X0 ≤ X0 / 1000 := by rw [div_le_iff₀ hX0p] at hδ; linarith
        rw [hX0e]; linarith
      rw [hM, div_le_div_iff₀ hXm0 hX0p]; nlinarith
    have hSRT := sum_labels_le_SRL hSR hM1 hMY hρ0 hρ1 T
      (fun w hw => by
        have := (mem_Dset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2; omega)
      (fun w hw => by
        obtain ⟨hwF, hwN⟩ := Finset.mem_filter.mp hw
        have hW := hwin w hwF hwN
        rw [abs_le] at hW
        have e1 : M * (1 - ρ) = (u - 1.02 * H u) / X0m := by
          rw [hM, hρ]; field_simp
        have e2 : M * (1 + ρ) = (u + 1.02 * H u) / X0m := by
          rw [hM, hρ]; field_simp
        rw [e1, e2, div_le_iff₀ hXm0, le_div_iff₀ hXm0]
        exact ⟨by linarith, by linarith⟩)
    have hMr : M ^ (-(3 / 4 : ℝ)) ≤ r ^ (-(3 / 4 : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos hr0 _ (by norm_num)
      rw [hM, hr]; exact div_le_div_of_nonneg_left hu0.le hXm0 hXm
    have hsum : ∑ w ∈ T, 1 / Vl P w ≤ 7.03 * r ^ (-(3 / 4 : ℝ)) := by
      have : 28 * ρ ≤ 0.03 * r ^ (-(3 / 4 : ℝ)) := by nlinarith
      linarith
    have hTR := TVD_div_le_Rd hP hp2 ht hlam hlam4 hy hd2 hu2 (tw := tw) (ε := ε)
    rw [← Finset.sum_filter]
    calc ∑ w ∈ T, 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w
        = 1 / 2 * TVD P H tw X0m y d / Vl P d * ∑ w ∈ T, 1 / Vl P w := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_; ring
      _ ≤ Rd P tw X0m y ε d * (7.03 * r ^ (-(3 / 4 : ℝ))) := by
          apply mul_le_mul hTR hsum (Finset.sum_nonneg fun w _ =>
            (one_div_pos.mpr (KR.valN_labelVal_pos P w)).le) hRd
      _ = 7.03 * r ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d := by ring
  · rw [Finset.sum_eq_zero fun w hw => if_neg (fun hN => hex ⟨w, hw, hN⟩)]
    split_ifs
    · have : 0 ≤ (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_nonneg (div_nonneg (by linarith) hX0.le) _
      positivity
    · exact le_rfl

end KR.RML9

end
