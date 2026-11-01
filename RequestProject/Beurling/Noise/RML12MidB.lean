module

public import RequestProject.Beurling.Noise.RML12Mid

/-!
# Proposition 5.31(ii) (the `X₀` band, middle range): the bound on `𝔅(y)`

`xbB_mid` : for a start `y ≥ X₀⁻` with `N = y/X₀`, `δ = H(X₀)/X₀`,
`𝔅(y) ≤ 31000 δ + 12200 e^{19.5} N^{-0.195} + e^{-62} Λ/log y`.

It is the split of `𝔅(y)` (`xbB_le_split`) into (α) `½ S(N)`, (β) the pairs with
`w ≤ e^{100}` and (γ′) the pairs with `w > e^{100}` (`gamma_le`, which uses only Lemma 5.29).
In (α) and (β) the short sums are bounded by Lemma 5.29 (`SD_le_SR`, `Rdwin_mid`); this is the
proof of the paper's middle range, with cruder constants (the paper has `200δ + 400N^{-1/10}`).
No height above `y` is read: all sums run over the levels of the start `y`, and Lemma 5.29 is
used at heights `M ≤ y/X₀ ≤ y/2`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML12

open KR.RML9 KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **(β), middle range**: the pairs with `w ≤ e^{100}`. -/
theorem beta_mid {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {ε θ lam0 : ℝ}
    (hP : PaperWidth H X0m ε θ) {X0 : ℕ} (hX0e : X0m = X0 - H X0 / 2)
    (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z) (hSR : ShortRecipLow P X0 y)
    (hN100 : Real.exp 100 ≤ y / X0) :
    ∑ w ∈ (RML9.Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100),
        ∑ d ∈ RML9.Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w ≤
      2 * 101 * (90.2 * (1.7 * (H X0 / X0)) +
        60 * Real.exp 19.5 * (y / X0) ^ (-(0.195 : ℝ))) := by
  set δ := H X0 / X0 with hδdef
  have hXm0 := hP.X0m_pos
  have hHp : 0 < H X0 := by linarith
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  have hy0 : 0 < y := by linarith
  have hδpos : 0 < δ := by positivity
  have hε : ε ≤ 0.005 := by linarith [hP.eps_le]
  have hX2 : (2 : ℝ) ≤ X0 := by
    have := h.X0m_ge; norm_num at this; linarith
  have hNy : y / X0 ≤ y / 2 := div_le_div_of_nonneg_left hy0.le (by norm_num) hX2
  set K := 90.2 * (1.7 * δ) + 60 * Real.exp 19.5 * (y / X0) ^ (-(0.195 : ℝ)) with hK
  have hK0 : 0 ≤ K := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ y / X0 by positivity) (-(0.195 : ℝ))
    positivity
  have hw : ∀ w ∈ (RML9.Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100),
      ∑ d ∈ RML9.Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w ≤ 2 * K * (1 / Vl P w) := by
    intro w hwF
    obtain ⟨hwD, hwB⟩ := Finset.mem_filter.mp hwF
    have hw2 := (RML9.mem_Dset.mp hwD).2
    have hVw := KR.valN_labelVal_pos P w
    have hVw1 : 1 ≤ Vl P w := KR.one_le_valN_label P w
    have hMw0 : 0 < y / X0 / Vl P w := by positivity
    have hMwy : y / X0 / Vl P w ≤ y / X0 := div_le_self (by positivity) hVw1
    have hR := Rdwin_mid (tw := tw) h hXl hSR ht hXm0 hy hp2 hZ hP.eps_nonneg hε
      (a := 1.7 * δ) (by positivity) (by linarith) hMw0 hMwy (P := P)
    have hpw : (y / X0 / Vl P w) ^ (-(0.195 : ℝ)) ≤ Real.exp 19.5 * (y / X0) ^ (-(0.195 : ℝ)) := by
      rw [Real.div_rpow (by positivity) hVw.le, div_eq_mul_inv, ← Real.rpow_neg hVw.le, neg_neg,
        mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      calc Vl P w ^ (0.195 : ℝ) ≤ (Real.exp 100) ^ (0.195 : ℝ) :=
            Real.rpow_le_rpow hVw.le hwB (by norm_num)
        _ = Real.exp 19.5 := by rw [← Real.exp_mul]; norm_num
    have hR' : ∑ d ∈ RML9.Dset P X0m y, (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
        Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) ≤ K := by
      refine hR.trans ?_
      rw [hK]; nlinarith
    calc ∑ d ∈ RML9.Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w
        ≤ ∑ d ∈ RML9.Dset P X0m y, 2 / Vl P w * (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
            Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) := by
          refine Finset.sum_le_sum fun d hdD => ?_
          have hd2 := (RML9.mem_Dset.mp hdD).2
          refine (Gpair_le_beta hP hX0e hX0 hδ hp2 ht hlam hlam1 hy hd2 hw2).trans ?_
          by_cases hW : Win P H y X0 (d * w)
          · rw [if_pos hW]
            have hv := win_val (P := P) hX0 hHp.le hδ hy0 hW
            rw [show LemmaM.valN P.labelVal (d * w) = Vl P d * Vl P w from
              Vl_mul_eq (by omega) (by omega)] at hv
            rw [if_pos ((win_prod_iff hVw).mp hv)]
          · rw [if_neg hW]
            have := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
            split_ifs <;> positivity
      _ = 2 / Vl P w * ∑ d ∈ RML9.Dset P X0m y, (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
            Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 2 / Vl P w * K := mul_le_mul_of_nonneg_left hR' (by positivity)
      _ = 2 * K * (1 / Vl P w) := by ring
  have hW1Z : Real.exp 100 ≤ Z := by
    have : y / X0 ≤ 2 * y / X0m := by
      rw [div_le_div_iff₀ hX0 hXm0]; nlinarith
    linarith
  have hharm := sum_Dset_recip_le (y := y) h (Real.one_le_exp (by norm_num)) hW1Z (P := P)
  rw [Real.log_exp] at hharm
  calc _ ≤ ∑ w ∈ (RML9.Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100),
          2 * K * (1 / Vl P w) := Finset.sum_le_sum hw
    _ = 2 * K * ∑ w ∈ (RML9.Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100), 1 / Vl P w :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * K * (100 + 1) := mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by rw [hK]; ring

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.31(ii), first claim** (middle range; Lean constants):
`𝔅(y) ≤ 31000 δ + 12200 e^{19.5} N^{-0.195} + e^{-62} Λ/log y`. -/
theorem xbB_mid {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {ε θ lam0 : ℝ}
    (hP : PaperWidth H X0m ε θ) {X0 : ℕ} (hX0e : X0m = X0 - H X0 / 2)
    (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z) (hSR : ShortRecipLow P X0 y)
    (hN100 : Real.exp 100 ≤ y / X0) :
    xbB P H tw X0m y X0 θ lam0 ≤
      31000 * (H X0 / X0) + 12200 * Real.exp 19.5 * (y / X0) ^ (-(0.195 : ℝ)) +
        Real.exp (-62) * Real.log X0 / Real.log y := by
  set δ := H X0 / X0 with hδdef
  have hXm0 := hP.X0m_pos
  have hHp : 0 < H X0 := by linarith
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  have hy0 : 0 < y := by linarith
  have hδpos : 0 < δ := by positivity
  have hX2 : (2 : ℝ) ≤ X0 := by
    have := h.X0m_ge; norm_num at this; linarith
  have hNy : y / X0 ≤ y / 2 := div_le_div_of_nonneg_left hy0.le (by norm_num) hX2
  have hN0 : 0 < y / X0 := by positivity
  have hsplit := xbB_le_split (tw := tw) (θ := θ) (lam0 := lam0) hP hX0e hp2
    (by linarith [hP.theta_nonneg]) hX0 hδ hy0
  rw [← Finset.sum_filter_add_sum_filter_not (RML9.Dset P X0m y)
    (fun w => Vl P w ≤ Real.exp 100)] at hsplit
  have hα := SD_le_SR (P := P) (tw := tw) hSR ht hXm0.le hy hp2 (a := 1.7 * δ) (by positivity)
    (by linarith) (le_refl (y / X0))
  have hNp : 0 ≤ (y / X0) ^ (-(0.195 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hα' : SD P tw X0m y (1.7 * δ) (y / X0) ≤ 28 * (1.7 * δ) + 7 * (y / X0) ^ (-(0.195 : ℝ)) := by
    refine hα.trans ?_
    split_ifs with hM
    · have := rpow_le_of_ge_one hM; linarith
    · positivity
  have hβ := beta_mid h hP hX0e hH1 hδ hp2 hXl ht hlam hlam1 hy hZ hSR hN100 (tw := tw)
  have hγ := gamma_le h hP hX0e hδ hp2 hXl ht htv hlam hlam1 hy hZ hSR (tw := tw)
  have he : (1 : ℝ) ≤ Real.exp 19.5 := Real.one_le_exp (by norm_num)
  nlinarith

end KR.RML12

end
