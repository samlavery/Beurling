module

public import RequestProject.Beurling.Noise.RML9XBBeta2

/-!
# Proposition 5.31(iii), parts (β): the pairs with small cofactor `w ≤ W₁ = e^{100}`

`beta_le` : `∑_{w ≤ W₁} ∑_d G(d, w) ≤ 202·(250δ((Λ+101.4)(1+A₀)+A₁) + e^{-Λ})/J`
(`Gpair_le_beta`, the window `win_val`, `Rdwin_bound`, and `∑_{w ≤ W₁} 1/w ≤ log W₁ + 1`).
The pairs in `𝔹₁` and `𝔹₂` are bounded together on the window `Win`, so the constant is
coarser than the paper's `138 + 72` (it is still `O(δΛ/J)`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- `∑_{w ∈ Dset, w ≤ B} 1/w ≤ log B + 1`. -/
lemma sum_Dset_recip_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {B : ℝ}
    (hB1 : 1 ≤ B) (hBZ : B ≤ Z) :
    ∑ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ B), 1 / Vl P w ≤ Real.log B + 1 := by
  have hsub : (Dset P X0m y).filter (fun w => Vl P w ≤ B) ⊆ (P.elems B).image iota := by
    intro w hw
    obtain ⟨hwD, hwB⟩ := Finset.mem_filter.mp hw
    exact KR.mem_image_iota P (by have := (mem_Dset.mp hwD).2; omega) hwB
  calc ∑ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ B), 1 / Vl P w
      ≤ ∑ w ∈ (P.elems B).image iota, 1 / Vl P w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
          (one_div_pos.mpr (KR.valN_labelVal_pos P w)).le
    _ = ∑ e ∈ P.elems B, 1 / P.val e := by
        rw [Finset.sum_image (fun a _ b _ h => iota_injective h)]
        exact Finset.sum_congr rfl fun e _ => by
          rw [show Vl P (iota e) = P.val e from P.valN_iota e]
    _ ≤ _ := h.harm_le hB1 hBZ

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **Proposition 5.31(iii), (β₁) + (β₂)**: the pairs with `w ≤ W₁ = e^{100}`. -/
theorem beta_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {ε θ lam0 : ℝ}
    (hP : PaperWidth H X0m ε θ) {X0 : ℕ} (hX0e : X0m = X0 - H X0 / 2)
    (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hJ : 600 * Real.log X0 ^ 4 ≤ Real.log (y / X0))
    (hZ : 2 * y / X0m ≤ Z) (hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ))) :
    ∑ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100), ∑ d ∈ Dset P X0m y,
        Gpair P H tw X0m y X0 θ lam0 d w ≤
      202 * (250 * (H X0 / X0) * ((Real.log X0 + 101.4) * 3.0674 + 9.4091) +
        Real.exp (-Real.log X0)) / Real.log (y / X0) := by
  set δ := H X0 / X0 with hδdef
  set Λ := Real.log X0 with hΛdef
  set J := Real.log (y / X0) with hJdef
  have hXm0 := hP.X0m_pos
  have hHp : 0 < H X0 := by linarith
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  have hHX : H X0 ≤ X0 / 1000 := by rw [div_le_iff₀ hX0] at hδ; linarith
  have hXm2 : (X0 : ℝ) ≤ 2 * X0m := by rw [hX0e]; linarith
  have hΛ : 100000000 ≤ Λ := hXl.trans (Real.log_le_log hXm0 hXm)
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJ0 : 2000 ≤ J := by nlinarith
  have hy0 : 0 < y := by linarith
  have hδ0 : Real.exp (-Λ) ≤ δ := by
    rw [hΛdef, Real.exp_neg, Real.exp_log hX0, hδdef]
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hH1 hX0.le
  have hδpos : 0 < δ := by positivity
  have hε : ε ≤ 0.005 := by linarith [hP.eps_le]
  set K := 250 * δ * ((Λ + 101.4) * 3.0674 + 9.4091) / J + Real.exp (-Λ) / J with hK
  have hJpos : 0 < J := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hw : ∀ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100),
      ∑ d ∈ Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w ≤ 2 * K * (1 / Vl P w) := by
    intro w hwF
    obtain ⟨hwD, hwB⟩ := Finset.mem_filter.mp hwF
    have hw2 := (mem_Dset.mp hwD).2
    have hVw := KR.valN_labelVal_pos P w
    have hVw1 : 1 ≤ Vl P w := KR.one_le_valN_label P w
    have hRw := Rdwin_bound (tw := tw) h hXl ht htv hXm0 hXm hXm2 hy hJ hδ0 (by linarith) hZ hT
      hε hVw1 hwB (P := P)
    have hlw : Real.log (Vl P w) ≤ 100 := by
      calc Real.log (Vl P w) ≤ Real.log (Real.exp 100) := Real.log_le_log hVw hwB
        _ = 100 := Real.log_exp 100
    have hRw' : ∑ d ∈ Dset P X0m y, (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
        Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) ≤ K := by
      refine hRw.trans ?_
      rw [hK]
      have : 250 * δ * ((Λ + Real.log (Vl P w) + 1.4) * 3.0674 + 9.4091) ≤
          250 * δ * ((Λ + 101.4) * 3.0674 + 9.4091) := by
        have : 0 ≤ 250 * δ := by positivity
        nlinarith
      have := div_le_div_of_nonneg_right this hJpos.le
      linarith
    calc ∑ d ∈ Dset P X0m y, Gpair P H tw X0m y X0 θ lam0 d w
        ≤ ∑ d ∈ Dset P X0m y, 2 / Vl P w * (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
            Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) := by
          refine Finset.sum_le_sum fun d hdD => ?_
          have hd2 := (mem_Dset.mp hdD).2
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
      _ = 2 / Vl P w * ∑ d ∈ Dset P X0m y, (if y / X0 / Vl P w * (1 - 1.7 * δ) ≤ Vl P d ∧
            Vl P d ≤ y / X0 / Vl P w * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 2 / Vl P w * K := mul_le_mul_of_nonneg_left hRw' (by positivity)
      _ = 2 * K * (1 / Vl P w) := by ring
  have hW1Z : Real.exp 100 ≤ Z := by
    have hN : Real.exp 100 ≤ y / X0 := by
      rw [← Real.exp_log (show 0 < y / X0 by positivity)]
      exact Real.exp_le_exp.mpr (by linarith)
    have : y / X0 ≤ 2 * y / X0m := by
      rw [div_le_div_iff₀ hX0 hXm0]; nlinarith
    linarith
  have hharm := sum_Dset_recip_le (y := y) h (Real.one_le_exp (by norm_num)) hW1Z (P := P)
  rw [Real.log_exp] at hharm
  calc _ ≤ ∑ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100), 2 * K * (1 / Vl P w) :=
        Finset.sum_le_sum hw
    _ = 2 * K * ∑ w ∈ (Dset P X0m y).filter (fun w => Vl P w ≤ Real.exp 100), 1 / Vl P w :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * K * (100 + 1) := mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by rw [hK]; field_simp; ring

end KR.RML9

end
