module

public import RequestProject.Beurling.Noise.RML9HJ
public import RequestProject.Beurling.Noise.RML6Var2Tail

/-!
# Proposition 5.31(ii) (the `X₀` band, middle range): the short sums

In the middle range only Lemma 5.29 (`ShortRecip`, reciprocal sums over short intervals) is
used, with `|c_e| ≤ 1`:

* `SD_le_SR` : `S(M) ≤ 1[M ≥ 1] (28a + 7M^{-3/4})` for `0 < M ≤ y/2`, `0 < a ≤ 0.01`;
* `Rdwin_mid` : the window sum of `R` (eq. (TVD-sums)) at height `M`:
  `∑_{V(d) ∈ M[1∓a]} R(d) ≤ 90.2 a + 60 M^{-0.195}`, from `S(M)`, `A₀(ε) ≤ 2.2181`
  (`hordA0_1955`) and `∑ H_ord(m) m^{-1.8} ≤ 7.55` (`hord18_set`) for the shifted sums.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML12

open KR.RML9 KR.XB7

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma abs_cN_le_one (ht : ∀ r, r.Prime → 0 < tw r) (hX : 0 ≤ X0m) (hy : X0m ≤ y) {e : ℕ}
    (he : 1 ≤ e) : |cN P tw X0m y e| ≤ 1 := by
  unfold cN
  rw [mass_eq_coeff]
  exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht (fun r _ => P.one_le_labelVal r) hX hy
    he

open scoped Classical in
/-- **`S(M)` by Lemma 5.29**: `S(M) ≤ 1[M ≥ 1] (28a + 7M^{-3/4})`. -/
lemma SD_le_SR {X0 : ℝ} (hSR : ShortRecipLow P X0 y) (ht : ∀ r, r.Prime → 0 < tw r) (hX : 0 ≤ X0m)
    (hy : X0m ≤ y) (hp2 : ∀ j, 2 ≤ P.p j) {a M : ℝ} (ha0 : 0 < a) (ha : a ≤ 0.01)
    (hMy : M ≤ y / X0) :
    SD P tw X0m y a M ≤ if 1 ≤ M then 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) else 0 := by
  unfold SD
  split_ifs with hM
  · set T := (RML9.Dset P X0m y).filter (fun e => M * (1 - a) ≤ LemmaM.valN P.labelVal e ∧
      LemmaM.valN P.labelVal e ≤ M * (1 + a))
    calc ∑ e ∈ RML9.Dset P X0m y, (if M * (1 - a) ≤ LemmaM.valN P.labelVal e ∧
          LemmaM.valN P.labelVal e ≤ M * (1 + a)
          then |cN P tw X0m y e| / LemmaM.valN P.labelVal e else 0)
        = ∑ e ∈ T, |cN P tw X0m y e| / LemmaM.valN P.labelVal e := (Finset.sum_filter _ _).symm
      _ ≤ ∑ e ∈ T, 1 / LemmaM.valN P.labelVal e := by
          refine Finset.sum_le_sum fun e he => ?_
          have he2 := (RML9.mem_Dset.mp (Finset.mem_filter.mp he).1).2
          exact div_le_div_of_nonneg_right (abs_cN_le_one ht hX hy (by omega))
            (KR.valN_labelVal_pos P e).le
      _ ≤ 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) := by
          refine sum_labels_le_SRL hSR hM hMy ha0 ha T (fun w hw => ?_) (fun w hw =>
            (Finset.mem_filter.mp hw).2)
          have := (RML9.mem_Dset.mp (Finset.mem_filter.mp hw).1).2; omega
  · push_neg at hM
    refine (Finset.sum_eq_zero fun e he => ?_).le
    have he2 := (RML9.mem_Dset.mp he).2
    have hno := not_val_le_of_small hp2 he2 (B := M * (1 + a)) (by nlinarith)
    rw [if_neg (fun h => hno h.2)]

lemma rpow_le_of_ge_one {M : ℝ} (hM : 1 ≤ M) : M ^ (-(3 / 4 : ℝ)) ≤ M ^ (-(0.195 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le hM (by norm_num)

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **The window sum of `R` in the middle range**: `∑_{V(d) ∈ M[1∓a]} R(d) ≤ 90.2a + 60M^{-0.195}`
(eq. (TVD-sums) with Lemma 5.29). -/
theorem Rdwin_mid {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℝ} (hXl : 100000000 ≤ Real.log X0m) (hSR : ShortRecipLow P X0 y)
    (ht : ∀ r, r.Prime → 0 < tw r)
    (hX : 0 < X0m) (hy : X0m ≤ y) (hp2 : ∀ j, 2 ≤ P.p j) (hZ : 2 * y / X0m ≤ Z) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 0.005) {a M : ℝ} (ha0 : 0 < a) (ha : a ≤ 0.01) (hM0 : 0 < M)
    (hMy : M ≤ y / X0) :
    ∑ d ∈ RML9.Dset P X0m y, (if M * (1 - a) ≤ Vl P d ∧ Vl P d ≤ M * (1 + a)
      then Rd P tw X0m y ε d else 0) ≤ 90.2 * a + 60 * M ^ (-(0.195 : ℝ)) := by
  refine (Rd_win_le ε a M).trans ?_
  set V := LemmaM.valN P.labelVal with hVdef
  have hV0 : ∀ m, 0 < V m := fun m => KR.valN_labelVal_pos P m
  have hMp : 0 ≤ M ^ (-(0.195 : ℝ)) := Real.rpow_nonneg hM0.le _
  -- the term `m = 1`
  have h1 := SD_le_SR (P := P) (tw := tw) hSR ht hX.le hy hp2 ha0 ha hMy
  have h1' : SD P tw X0m y a M ≤ 28 * a + 7 * M ^ (-(0.195 : ℝ)) := by
    refine h1.trans ?_
    split_ifs with hM
    · have := rpow_le_of_ge_one hM; linarith
    · positivity
  -- the shifted terms
  have hpt : ∀ m ∈ RML9.Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
      SD P tw X0m y a (M / Vl P m) ≤
      28 * a * ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) +
        7 * M ^ (-(3 / 4 : ℝ)) * M ^ (0.555 : ℝ) *
          (if V m ≤ M then (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.8 : ℝ)) else 0) := by
    intro m hm
    have hVm := hV0 m
    have hHo : 0 ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hVm.le _)
    have hMm : M / V m ≤ y / X0 := by
      have hV1 : 1 ≤ V m := KR.one_le_valN_label P m
      calc M / V m ≤ M := div_le_self hM0.le hV1
        _ ≤ y / X0 := hMy
    have hS := SD_le_SR (P := P) (tw := tw) hSR ht hX.le hy hp2 ha0 ha hMm
    have hS' : Vl P m ^ (ε - 2) = V m ^ (ε - 2) := rfl
    rw [hS']
    split_ifs at hS with hc
    · -- `V(m) ≤ M`
      have hVM : V m ≤ M := by rwa [le_div_iff₀ hVm, one_mul] at hc
      rw [if_pos hVM]
      have hkey : V m ^ (ε - 2) * (M / V m) ^ (-(3 / 4 : ℝ)) ≤
          M ^ (-(3 / 4 : ℝ)) * M ^ (0.555 : ℝ) * V m ^ (-(1.8 : ℝ)) := by
        rw [Real.div_rpow hM0.le hVm.le]
        have e0 : V m ^ (ε - 2) / V m ^ (-(3 / 4 : ℝ)) = V m ^ (-(1.8 : ℝ)) * V m ^ (ε + 0.55) := by
          rw [← Real.rpow_sub hVm, ← Real.rpow_add hVm]; ring_nf
        have e1 : V m ^ (ε - 2) * (M ^ (-(3 / 4 : ℝ)) / V m ^ (-(3 / 4 : ℝ))) =
            M ^ (-(3 / 4 : ℝ)) * (V m ^ (-(1.8 : ℝ)) * V m ^ (ε + 0.55)) := by
          rw [← e0]; ring
        rw [e1]
        have hVM' : V m ^ (ε + 0.55) ≤ M ^ (0.555 : ℝ) := by
          have hV1 : 1 ≤ V m := KR.one_le_valN_label P m
          calc V m ^ (ε + 0.55) ≤ M ^ (ε + 0.55) :=
                Real.rpow_le_rpow hVm.le hVM (by linarith)
            _ ≤ M ^ (0.555 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (hV1.trans hVM) (by linarith)
        have h18 : 0 ≤ V m ^ (-(1.8 : ℝ)) := Real.rpow_nonneg hVm.le _
        have hM34 : 0 ≤ M ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hM0.le _
        calc M ^ (-(3 / 4 : ℝ)) * (V m ^ (-(1.8 : ℝ)) * V m ^ (ε + 0.55))
            ≤ M ^ (-(3 / 4 : ℝ)) * (V m ^ (-(1.8 : ℝ)) * M ^ (0.555 : ℝ)) := by gcongr
          _ = _ := by ring
      have hH := (Nat.cast_nonneg (α := ℝ) (BSCert.X0Band.Hord m))
      calc (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) * SD P tw X0m y a (M / V m)
          ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
              (28 * a + 7 * (M / V m) ^ (-(3 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hS hHo
        _ = 28 * a * ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) +
              7 * (BSCert.X0Band.Hord m : ℝ) * (V m ^ (ε - 2) * (M / V m) ^ (-(3 / 4 : ℝ))) := by
            ring
        _ ≤ 28 * a * ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) +
              7 * (BSCert.X0Band.Hord m : ℝ) *
                (M ^ (-(3 / 4 : ℝ)) * M ^ (0.555 : ℝ) * V m ^ (-(1.8 : ℝ))) := by gcongr
        _ = _ := by ring
    · have h0 : SD P tw X0m y a (M / V m) ≤ 0 := hS
      have hSD0 := SD_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) a (M / V m)
      have : SD P tw X0m y a (M / V m) = 0 := le_antisymm h0 hSD0
      rw [this, mul_zero]
      have hif : 0 ≤ (if V m ≤ M then (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.8 : ℝ)) else 0) := by
        split_ifs
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hVm.le _)
        · exact le_rfl
      have := Real.rpow_nonneg hM0.le (-(3 / 4 : ℝ))
      have := Real.rpow_nonneg hM0.le (0.555 : ℝ)
      positivity
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  -- the two Hord sums
  have hsD : ∀ m ∈ RML9.Dset P X0m y, 2 ≤ m ∧ V m ≤ 2 * y / X0m := fun m hm =>
    ⟨(RML9.mem_Dset.mp hm).2, Dset_val_le hm⟩
  have hA := hordA0_1955 P h hXl (ε := ε) (by linarith) hZ (RML9.Dset P X0m y) hsD
  have hB : ∑ m ∈ RML9.Dset P X0m y,
      (if V m ≤ M then (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.8 : ℝ)) else 0) ≤ 7.55 := by
    rw [← Finset.sum_filter]
    exact hord18_set P h hXl hZ _ fun m hm => hsD m (Finset.mem_filter.mp hm).1
  have hMM : 7 * M ^ (-(3 / 4 : ℝ)) * M ^ (0.555 : ℝ) = 7 * M ^ (-(0.195 : ℝ)) := by
    rw [mul_assoc, ← Real.rpow_add hM0]; norm_num
  rw [hMM] at hsum
  have hB0 : 0 ≤ ∑ m ∈ RML9.Dset P X0m y,
      (if V m ≤ M then (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.8 : ℝ)) else 0) :=
    Finset.sum_nonneg fun m _ => by
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hV0 m).le _)
      · exact le_rfl
  have hA0 : 0 ≤ ∑ m ∈ RML9.Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hV0 m).le _)
  have hlhs : ∑ m ∈ RML9.Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
      SD P tw X0m y a (M / Vl P m) ≤ 28 * a * 2.2181 + 7 * M ^ (-(0.195 : ℝ)) * 7.55 := by
    refine hsum.trans ?_
    have := mul_le_mul_of_nonneg_left hA (show 0 ≤ 28 * a by linarith)
    have := mul_le_mul_of_nonneg_left hB (show 0 ≤ 7 * M ^ (-(0.195 : ℝ)) by positivity)
    linarith
  linarith

end KR.RML12

end
