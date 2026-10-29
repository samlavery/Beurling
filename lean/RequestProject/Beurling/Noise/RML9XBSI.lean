module

public import RequestProject.Beurling.Noise.RML9XBPair2

/-!
# Proposition 5.31(iii): the short sums `S(M)` by Lemma 5.32

* `SD_le_SIsum` : by Lemma 5.5 (`c_e ≠ 0` forces `e` squarefree and `4v`-dense with
  `y/e < 2v`), `S(M) ≤ S_t([N', N'(1+η)])` with `N' = M(1-a)`, `η = 2a/(1-a)`, `t = 4y/N'`;
* `SD_le_SI` : Lemma 5.32 then gives, for `M ∈ [N^{0.95}, N]` (`N = y/X₀`, `J = log N ≥ 600Λ⁴`,
  `a = 1.7δ`), `S(M) ≤ 250 δ (Λ + log(N/M) + 1.4)/J`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma cN_iota (e : ℕ →₀ ℕ) :
    cN P tw X0m y (iota e) = (LemmaM.coeff tw P.labelVal X0m y (iota e) : ℝ) :=
  mass_eq_coeff _ _ _ _ _

/-- `S(M)` is a sum over the elements: `∑_{e ∈ Dset} g(e) ≤ ∑_{el ∈ 𝒩, val ≤ 2y/X₀⁻} g(ι el)`. -/
lemma sum_Dset_le (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    ∑ e ∈ Dset P X0m y, g e ≤ ∑ el ∈ P.elems (2 * y / X0m), g (iota el) := by
  unfold Dset
  calc ∑ e ∈ ((P.elems (2 * y / X0m)).image iota).filter (2 ≤ ·), g e
      ≤ ∑ e ∈ (P.elems (2 * y / X0m)).image iota, g e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => hg n
    _ = _ := Finset.sum_image fun a _ b _ h => iota_injective h

/-- **The density reduction**: `S(M) ≤ S_t([N', N'(1+η)])`. -/
lemma SD_le_SIsum (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hX0 : 0 ≤ X0m) (hy : X0m ≤ y)
    (hy0 : 0 < y) {a M : ℝ} (ha : a < 1) (hM : 0 < M) :
    SD P tw X0m y a M ≤
      P.SIsum (4 * (y / (M * (1 - a)))) (M * (1 - a)) (2 * a / (1 - a)) := by
  classical
  have hval : ∀ r, r.Prime → 1 ≤ P.labelVal r := fun r _ => P.one_le_labelVal r
  set N' := M * (1 - a) with hN'
  set η := 2 * a / (1 - a) with hη
  set v := y / N' with hv
  have h1a : 0 < 1 - a := by linarith
  have hN'0 : 0 < N' := mul_pos hM h1a
  have hN'η : N' * (1 + η) = M * (1 + a) := by
    rw [hN', hη]; field_simp; ring
  unfold SD
  refine (sum_Dset_le _ fun n => by
    split_ifs
    · exact div_nonneg (abs_nonneg _) (KR.valN_labelVal_pos P n).le
    · exact le_rfl).trans ?_
  -- termwise
  have hterm : ∀ el ∈ P.elems (2 * y / X0m),
      (if M * (1 - a) ≤ LemmaM.valN P.labelVal (iota el) ∧
          LemmaM.valN P.labelVal (iota el) ≤ M * (1 + a)
        then |cN P tw X0m y (iota el)| / LemmaM.valN P.labelVal (iota el) else 0) ≤
      if N' ≤ P.val el ∧ P.val el ≤ N' * (1 + η) ∧ P.IsDense (4 * v) el
        then 1 / P.val el else 0 := by
    intro el _
    rw [P.valN_iota, cN_iota]
    have hval0 := P.val_pos el
    by_cases hw : M * (1 - a) ≤ P.val el ∧ P.val el ≤ M * (1 + a)
    · rw [if_pos hw]
      rw [LemmaM.lemma_M tw P.labelVal ht hval hX0 hy (iota_pos el)]
      by_cases hchi : LemmaM.chi tw P.labelVal y (iota el)
      · have hd : P.IsDense (4 * v) el := by
          refine P.isDense_of_chi ht htv hchi ?_
          have h1 : N' ≤ P.val el := hw.1
          have : 2 * v * P.val el ≥ 2 * y := by
            rw [hv]
            have := div_mul_cancel₀ y hN'0.ne'
            calc 2 * (y / N') * P.val el ≥ 2 * (y / N') * N' :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = 2 * y := by field_simp
          linarith
        have hR : (if N' ≤ P.val el ∧ P.val el ≤ N' * (1 + η) ∧ P.IsDense (4 * v) el
            then 1 / P.val el else 0) = 1 / P.val el :=
          if_pos ⟨hw.1, by rw [hN'η]; exact hw.2, hd⟩
        rw [hR]
        apply div_le_div_of_nonneg_right _ hval0.le
        have hmu : |(ArithmeticFunction.moebius (iota el) : ℝ)| ≤ 1 := by
          rcases ArithmeticFunction.moebius_eq_or (iota el) with h | h | h <;> simp [h]
        simp only [hchi, if_true, mul_one]
        push_cast
        split_ifs <;> simp [hmu]
      · simp only [hchi, if_false, mul_zero, zero_mul, Int.cast_zero, abs_zero, zero_div]
        split_ifs
        · exact (one_div_pos.mpr hval0).le
        · exact le_rfl
    · rw [if_neg hw]; split_ifs <;> positivity
  calc ∑ el ∈ P.elems (2 * y / X0m),
        (if M * (1 - a) ≤ LemmaM.valN P.labelVal (iota el) ∧
            LemmaM.valN P.labelVal (iota el) ≤ M * (1 + a)
          then |cN P tw X0m y (iota el)| / LemmaM.valN P.labelVal (iota el) else 0)
      ≤ ∑ el ∈ P.elems (2 * y / X0m), (if N' ≤ P.val el ∧ P.val el ≤ N' * (1 + η) ∧
          P.IsDense (4 * v) el then 1 / P.val el else 0) := Finset.sum_le_sum hterm
    _ = ∑ el ∈ (P.elems (2 * y / X0m)).filter (fun el => N' ≤ P.val el ∧
          P.val el ≤ N' * (1 + η) ∧ P.IsDense (4 * v) el), 1 / P.val el :=
        (Finset.sum_filter _ _).symm
    _ ≤ P.SIsum (4 * v) N' η := by
        unfold SIsum
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro el hel
          obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.mp hel
          exact Finset.mem_filter.mpr ⟨(P.mem_elems).mpr h2, h1, h3⟩
        · intro el _ _; exact (one_div_pos.mpr (P.val_pos el)).le


lemma concl_mono {X0 : ℕ} {y1 y2 : ℝ} (h12 : y1 ≤ y2)
    (h : LocalPNT.Theorem524Concl P X0 y2) : LocalPNT.Theorem524Concl P X0 y1 :=
  ⟨fun v hv1 hv2 => h.1 v hv1 (hv2.trans h12),
    fun v η h1 h2 h3 h4 => h.2 v η h1 h2 h3 (h4.trans h12)⟩

/-- `log(1-a) ≥ -0.0018` for `0 ≤ a ≤ 0.0017`. -/
lemma log_one_sub_ge {a : ℝ} (ha : a ≤ 0.0017) : -0.0018 ≤ Real.log (1 - a) := by
  have h1 : 0 < 1 - a := by linarith
  have := Real.add_one_le_exp (-0.0018)
  have h2 : Real.exp (-0.0018) ≤ 1 - a := by
    have h3 := Real.exp_le_one_iff.mpr (show (-0.0018 : ℝ) ≤ 0 by norm_num)
    -- `e^{-x} ≤ 1/(1+x)`
    have h4 : Real.exp (-0.0018) * (1 + 0.0018) ≤ 1 := by
      have := Real.add_one_le_exp (0.0018 : ℝ)
      have e : Real.exp (-0.0018) * Real.exp 0.0018 = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (-0.0018 : ℝ)]
    nlinarith [Real.exp_pos (-0.0018 : ℝ)]
  calc (-0.0018 : ℝ) = Real.log (Real.exp (-0.0018)) := (Real.log_exp _).symm
    _ ≤ Real.log (1 - a) := Real.log_le_log (Real.exp_pos _) h2

set_option maxHeartbeats 1000000 in
/-- **`S(M)` by Lemma 5.32**: for `log M ≥ 0.95 J` and `M ≤ N` (`N = y/X₀`, `J = log N`),
`S(M) ≤ 250 δ (Λ + log(N/M) + 1.4)/J`, `a = 1.7δ`. -/
theorem SD_le_SI {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hΛ : 100000000 ≤ Real.log X0) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hXm0 : 0 < X0m)
    (hXm : X0m ≤ (X0 : ℝ)) (hy : X0m ≤ y)
    (hJ : 600 * Real.log X0 ^ 4 ≤ Real.log (y / X0)) {δ : ℝ}
    (hδ0 : Real.exp (-Real.log X0) ≤ δ) (hδ1 : δ ≤ 1 / 1000) (hZ : 2 * y / X0m ≤ Z)
    (hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ))) {M : ℝ}
    (hM0 : 0 < M) (hM1 : 0.95 * Real.log (y / X0) ≤ Real.log M) (hM2 : M ≤ y / X0) :
    SD P tw X0m y (1.7 * δ) M ≤
      250 * δ * (Real.log X0 + Real.log (y / X0 / M) + 1.4) / Real.log (y / X0) := by
  set Λ := Real.log X0 with hΛdef
  set N := y / X0 with hNdef
  set J := Real.log N with hJdef
  have hX0 : (0 : ℝ) < X0 := by
    by_contra hc; push_neg at hc
    have : (X0 : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have hy0 : 0 < y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hΛΛ4 : Λ ≤ Λ ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hΛ2 : 100000000 * Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ24 : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hJbig : Λ + 1.5 ≤ 0.0001 * J := by nlinarith
  have hJ0 : 0 < J := by nlinarith
  have hN0 : 0 < N := by positivity
  have hδpos : 0 < δ := lt_of_lt_of_le (Real.exp_pos _) hδ0
  set a := 1.7 * δ with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 0.0017 := by rw [ha]; linarith
  set N' := M * (1 - a) with hN'
  set η := 2 * a / (1 - a) with hη
  set t := 4 * (y / N') with htdef
  have h1a : 0 < 1 - a := by linarith
  have hN'0 : 0 < N' := mul_pos hM0 h1a
  have hN'M : N' ≤ M := by rw [hN']; nlinarith
  have hla := log_one_sub_ge ha1
  have hla' : Real.log (1 - a) ≤ 0 := Real.log_nonpos h1a.le (by linarith)
  have hlogN' : Real.log N' = Real.log M + Real.log (1 - a) :=
    Real.log_mul hM0.ne' h1a.ne'
  have hJ' : 0.95 * J - 0.0018 ≤ Real.log N' := by rw [hlogN']; linarith
  -- `log t`
  have hlogt : Real.log t = Real.log 4 + Λ + Real.log (N / M) - Real.log (1 - a) := by
    rw [htdef, Real.log_mul (by norm_num) (by positivity), Real.log_div hy0.ne' hN'0.ne',
      hlogN', Real.log_div hN0.ne' hM0.ne', hNdef, Real.log_div hy0.ne' hX0.ne']
    ring
  have hl4 : Real.log 4 ≤ 1.3863 := by
    have := Real.log_two_lt_d9
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [e]; linarith
  have hl4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlNM : Real.log (N / M) ≤ 0.05 * J := by
    rw [Real.log_div hN0.ne' hM0.ne']; linarith
  have hlNM0 : 0 ≤ Real.log (N / M) := Real.log_nonneg (by rw [le_div_iff₀ hM0]; linarith)
  have hτ : Real.log t ≤ Λ + Real.log (N / M) + 1.4 := by rw [hlogt]; linarith
  have hτ0 : 0 ≤ Real.log t := by rw [hlogt]; linarith
  -- the hypotheses of Lemma 5.32
  have hJ5 : 300 * Λ ^ 4 ≤ Real.log N' := by linarith
  have ht1 : (X0 : ℝ) ≤ t := by
    have : y / N ≤ y / N' := div_le_div_of_nonneg_left hy0.le hN'0 (hN'M.trans hM2)
    have e : y / N = X0 := by rw [hNdef]; field_simp
    rw [htdef]; linarith
  have ht2 : t ≤ N' ^ (1 / 10 : ℝ) := by
    have htpos : 0 < t := by positivity
    rw [← Real.exp_log htpos, Real.rpow_def_of_pos hN'0]
    apply Real.exp_le_exp.mpr
    rw [hlogt]; nlinarith
  have hη0 : Real.exp (-(2 * Λ)) ≤ η := by
    have h1 : Real.exp (-(2 * Λ)) ≤ Real.exp (-Λ) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 * a ≤ η := by
      rw [hη, le_div_iff₀ h1a]; nlinarith
    rw [ha] at h2; linarith
  have hη1 : η ≤ 1 / 2 := by rw [hη, div_le_iff₀ h1a]; linarith
  have hZ' : 2 * N' ≤ Z := by
    have : N' ≤ y / X0m := by
      calc N' ≤ N := hN'M.trans hM2
        _ ≤ y / X0m := div_le_div_of_nonneg_left hy0.le hXm0 hXm
    calc 2 * N' ≤ 2 * (y / X0m) := by linarith
      _ = 2 * y / X0m := by ring
      _ ≤ Z := hZ
  have hT' : LocalPNT.Theorem524Concl P X0 (2 * N' ^ (0.55 : ℝ)) := by
    refine concl_mono ?_ hT
    have := Real.rpow_le_rpow hN'0.le (hN'M.trans hM2) (by norm_num : (0 : ℝ) ≤ 0.55)
    linarith
  have hSI := h.lemma_5_32 hΛ hN'0 hJ5 ht1 ht2 hη0 hη1 hZ' hT'
  have hS := SD_le_SIsum (P := P) (tw := tw) ht htv hXm0.le hy hy0 (a := a) (by linarith) hM0
  -- arithmetic
  have hJ'pos : 0.9499 * J ≤ Real.log N' := by linarith
  have hJN0 : 0 < Real.log N' := by linarith
  have hfac : 1 + 2.1 * Real.log t / Real.log N' ≤ 1.1108 := by
    have : 2.1 * Real.log t ≤ 2.1 * (Λ + 0.05 * J + 1.4) := by linarith
    have : 1 + 2.1 * Real.log t / Real.log N' ≤ 1 + 2.1 * (Λ + 0.05 * J + 1.4) / (0.9499 * J) := by
      have : 2.1 * Real.log t / Real.log N' ≤ 2.1 * (Λ + 0.05 * J + 1.4) / (0.9499 * J) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity) hJ'pos
      linarith
    refine this.trans ?_
    rw [← sub_nonneg]
    have : 1.1108 - (1 + 2.1 * (Λ + 0.05 * J + 1.4) / (0.9499 * J)) =
        (0.1108 * (0.9499 * J) - 2.1 * (Λ + 0.05 * J + 1.4)) / (0.9499 * J) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ (by positivity); nlinarith
  have hηδ : η ≤ 3.406 * δ := by
    rw [hη, div_le_iff₀ h1a, ha]; nlinarith
  have hη0' : 0 ≤ η := by positivity
  calc SD P tw X0m y a M ≤ P.SIsum t N' η := hS
    _ ≤ 61.1 * (1 + 2.1 * Real.log t / Real.log N') * (η * Real.log t / Real.log N') := hSI
    _ ≤ 61.1 * 1.1108 * (3.406 * δ * (Λ + Real.log (N / M) + 1.4) / (0.9499 * J)) := by
        have hfac0 : 0 ≤ 1 + 2.1 * Real.log t / Real.log N' := by positivity
        apply mul_le_mul (by nlinarith) _ (by positivity) (by positivity)
        apply div_le_div₀ (by positivity) _ (by positivity) hJ'pos
        exact mul_le_mul hηδ hτ hτ0 (by positivity)
    _ ≤ 250 * δ * (Λ + Real.log (N / M) + 1.4) / J := by
        rw [le_div_iff₀ hJ0]
        have h0 : 0 ≤ δ * (Λ + Real.log (N / M) + 1.4) := by positivity
        have e : 61.1 * 1.1108 * (3.406 * δ * (Λ + Real.log (N / M) + 1.4) / (0.9499 * J)) * J =
            61.1 * 1.1108 * 3.406 / 0.9499 * (δ * (Λ + Real.log (N / M) + 1.4)) := by
          field_simp
        rw [e]
        have : 61.1 * 1.1108 * 3.406 / 0.9499 ≤ (250 : ℝ) := by norm_num
        nlinarith

end KR.RML9

end
