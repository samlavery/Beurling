module

public import RequestProject.Beurling.Noise.BridgeSIPrime
public import RequestProject.Beurling.Noise.BridgeSINum
public import RequestProject.Beurling.Noise.BridgeSIInt

/-!
# Lemma 5.32 (short-interval Saias bound)

`HBS.lemma_5_32` : let `Λ = log X₀ ≥ 10⁸`, `J = log N ≥ J₁ = 300Λ⁴`, `t ∈ [X₀, N^{1/10}]`,
`τ = log t`, `e^{-2Λ} ≤ η ≤ 1/2`. If the system satisfies (HBS) on `[1, Z]` with `2N ≤ Z` and
Theorem 5.24 holds at the height `y' = 2N^{0.55}` (`LocalPNT.Theorem524Concl P X₀ y'`; on
`Good(<y)`, `y ≥ N`, this is Theorem 5.24 below the certified horizon), then

  `S_t([N, N(1+η)]) ≤ 61.1 (1 + 2.1τ/J) ητ/J`.

The proof is the paper's: the decomposition by the top prime (`SIsum_le_decomp`), part (B) by
Lemma 5.30 (`partB_small`), part (A) by the prime-window bound from Theorem 5.24(iii)
(`sum_inv_window_le`), the dyadic blocks (`SIblocks_le`), Lemma 5.8 or Lemma 5.30 in each block
(`block_term_le`, `tail_small`), and the comparison of the block sum with
`J̃⁻¹ ∫ ρ(u-1) du/u ≤ J̃⁻¹ (1 + log(1/u_min))` (`block_sum_le`, `log_ratio_le`).
The constant comes out as `1.1001 · 38.3 · 1.002/log 2 < 60.95`.
-/

@[expose] public section

open Real Finset

namespace BridgeSI

/-- The lower limit of the `u`-integral: `max(0, log(1/u_min)) ≤ 2.1τ/J + 7.3/J`. -/
lemma umin_bound {J τ ℓ0 Jt : ℝ} (hJ : 30000000000000000000000000000000000 ≤ J)
    (hτ : 100000000 ≤ τ) (hτJ : τ ≤ J / 10) (hℓ0 : ℓ0 = (J - τ) / 2 - Real.log 2)
    (hJt : Jt = J + Real.log 2) :
    max 0 (Real.log (1 / uOf Jt (ℓ0 - Real.log 2))) ≤ 2.1 * τ / J + 7.3 / J := by
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hJ0 : 0 < J := by linarith
  set y := (τ + 5 * Real.log 2) / (J + Real.log 2) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy6 : y ≤ 1 / 6 := by
    rw [hy, div_le_iff₀ (by positivity)]; linarith
  have hu_min : 1 / uOf Jt (ℓ0 - Real.log 2) = (1 + y) / (1 - y) := by
    unfold uOf
    rw [hℓ0, hJt, hy]
    have h1 : (J - τ) / 2 - Real.log 2 - Real.log 2 ≠ 0 := by linarith
    have h2 : J + Real.log 2 ≠ 0 := by linarith
    have h3 : J + Real.log 2 - (τ + 5 * Real.log 2) ≠ 0 := by linarith
    field_simp
    ring
  have hlogu : max 0 (Real.log (1 / uOf Jt (ℓ0 - Real.log 2))) ≤ 2.1 * y := by
    rw [hu_min]
    exact max_le (by positivity) (log_ratio_le hy0 hy6)
  refine hlogu.trans ?_
  rw [hy, ← add_div, mul_div_assoc', div_le_div_iff₀ (by positivity) hJ0]
  nlinarith

/-- The Rankin terms of all blocks together: `1.1001 η |K| E ≤ 0.01 ητ/J`. -/
lemma tailK_bound {J τ η s0 : ℝ} (hJ : 30000000000000000000000000000000000 ≤ J)
    (hτ : 100000000 ≤ τ) (hη : 0 < η) (hs0 : s0 = BSaias.u0 (0.449 * J)) (c E : ℝ)
    (hE : E = Real.exp 14 * (J + 1) * Real.exp (-s0)) (hc : c ≤ 2 * J) :
    1.1001 * η * (c * E) ≤ 0.01 * η * τ / J := by
  have hJ0 : 0 < J := by linarith
  have hs0big : 300000000 ≤ s0 := by
    have h1 : (300000000 : ℝ) ^ 4 ≤ 0.449 * J := by nlinarith
    rw [hs0]
    unfold BSaias.u0 BSCert.Z2.u0
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num)
      (by positivity)]
    nlinarith
  have hs04 : s0 ^ 4 = 0.449 * J := by
    rw [hs0]; unfold BSaias.u0 BSCert.Z2.u0
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity)]
  have htail := tail_small hs0big hJ0.le (by rw [hs04, mul_div_cancel_left₀ _ (by norm_num)])
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hc' : c * E ≤ 2 * J * E := mul_le_mul_of_nonneg_right hc hE0
  have h2 : 2.2002 * J * E * J ≤ 0.01 := by
    have : 2.2002 * J * E * J = 2.2002 * Real.exp 14 * (J ^ 2 * (J + 1)) * Real.exp (-s0) := by
      rw [hE]; ring
    rw [this]; exact htail
  have h3 : 2.2002 * J * E ≤ 0.01 / J := by rw [le_div_iff₀ hJ0]; exact h2
  have h4 : 0.01 / J ≤ 0.01 * τ / J := by
    apply div_le_div_of_nonneg_right _ hJ0.le; nlinarith
  have h5 : 1.1001 * (c * E) ≤ 0.01 * τ / J := by nlinarith
  calc 1.1001 * η * (c * E) = η * (1.1001 * (c * E)) := by ring
    _ ≤ η * (0.01 * τ / J) := mul_le_mul_of_nonneg_left h5 hη.le
    _ = 0.01 * η * τ / J := by ring

/-- The final arithmetic of Lemma 5.32. -/
lemma si_final_arith {J τ η L1 G Mx B c E : ℝ} (hJ : 30000000000000000000000000000000000 ≤ J)
    (hτ : 100000000 ≤ τ) (hτJ : τ ≤ J / 10) (hη : 0 < η) (hL1 : 10000000000 ≤ L1)
    (hG0 : 0 ≤ G)
    (hG : G ≤ (1 + 3 * Real.log 2 / (L1 - 2)) / Real.log 2 *
      ((J + Real.log 2)⁻¹ * (Mx + 1)))
    (hMx : Mx ≤ 2.1 * τ / J + 7.3 / J) (hB : B ≤ 0.01 * η * τ / J)
    (htail : 1.1001 * η * (c * E) ≤ 0.01 * η * τ / J) :
    B + 1.1001 * η * (1.002 * 38.3 * τ * G + c * E) ≤
      61.1 * (1 + 2.1 * τ / J) * (η * τ / J) := by
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hJ0 : 0 < J := by linarith
  have hτ0 : 0 < τ := by linarith
  have hS0 : 0 < L1 - 2 := by linarith
  set κ := (1 + 3 * Real.log 2 / (L1 - 2)) / Real.log 2 with hκ
  have hconst : 1.1001 * (1.002 * 38.3) * κ ≤ 60.95 := by
    have h1 : 3 * Real.log 2 / (L1 - 2) ≤ 0.000001 := by
      rw [div_le_iff₀ hS0]; have := Real.log_two_lt_d9; linarith
    have h2 : κ ≤ 1.000001 / 0.6931471803 :=
      div_le_div₀ (by norm_num) (by linarith) (by norm_num) hl2.le
    calc 1.1001 * (1.002 * 38.3) * κ ≤ 1.1001 * (1.002 * 38.3) * (1.000001 / 0.6931471803) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 60.95 := by norm_num
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    have : 0 ≤ 3 * Real.log 2 / (L1 - 2) := div_nonneg (by linarith) hS0.le
    exact div_nonneg (by linarith) (by linarith)
  have hinv : (J + Real.log 2)⁻¹ ≤ J⁻¹ := inv_anti₀ hJ0 (by linarith)
  have hMx1 : 0 ≤ Mx + 1 ∨ Mx + 1 < 0 := le_or_gt 0 (Mx + 1)
  have hG2 : G ≤ κ * (J⁻¹ * (1 + 2.1 * τ / J + 7.3 / J)) := by
    refine hG.trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    rcases hMx1 with h | h
    · calc (J + Real.log 2)⁻¹ * (Mx + 1) ≤ J⁻¹ * (Mx + 1) :=
            mul_le_mul_of_nonneg_right hinv h
        _ ≤ J⁻¹ * (1 + 2.1 * τ / J + 7.3 / J) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have : (J + Real.log 2)⁻¹ * (Mx + 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
      have : 0 ≤ J⁻¹ * (1 + 2.1 * τ / J + 7.3 / J) := by positivity
      linarith
  have hmain : 1.1001 * η * (1.002 * 38.3 * τ * G) ≤
      60.95 * (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) := by
    have e : 1.1001 * η * (1.002 * 38.3 * τ * (κ * (J⁻¹ * (1 + 2.1 * τ / J + 7.3 / J)))) =
        (1.1001 * (1.002 * 38.3) * κ) * (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) := by
      ring
    have hR0 : 0 ≤ (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) := by positivity
    calc 1.1001 * η * (1.002 * 38.3 * τ * G)
        ≤ 1.1001 * η * (1.002 * 38.3 * τ * (κ * (J⁻¹ * (1 + 2.1 * τ / J + 7.3 / J)))) := by
          gcongr
      _ = (1.1001 * (1.002 * 38.3) * κ) * (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) := e
      _ ≤ 60.95 * (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) := by
          rw [mul_assoc, mul_assoc 60.95]
          exact mul_le_mul_of_nonneg_right hconst hR0
  have hX : 0 ≤ η * τ / J := by positivity
  have h73 : 60.95 * (7.3 / J) ≤ 0.01 := by
    rw [mul_div_assoc', div_le_iff₀ hJ0]; nlinarith
  have e1 : 0.01 * η * τ / J = 0.01 * (η * τ / J) := by ring
  rw [e1] at hB htail
  have e2 : 60.95 * (1 + 2.1 * τ / J + 7.3 / J) * (η * τ / J) =
      60.95 * (1 + 2.1 * τ / J) * (η * τ / J) + 60.95 * (7.3 / J) * (η * τ / J) := by ring
  rw [e2] at hmain
  have h1 : 60.95 * (7.3 / J) * (η * τ / J) ≤ 0.01 * (η * τ / J) :=
    mul_le_mul_of_nonneg_right h73 hX
  have h2 : 0 ≤ 2.1 * τ / J := by positivity
  have h3 : 0 ≤ (1 + 2.1 * τ / J) * (η * τ / J) := by positivity
  rw [mul_add]
  nlinarith

end BridgeSI

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

set_option maxHeartbeats 4000000 in
/-- **Lemma 5.32 (short-interval Saias bound).** -/
theorem lemma_5_32 (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ} {N t η : ℝ}
    (hΛ : 100000000 ≤ Real.log X0) (hN0 : 0 < N) (hJ : 300 * Real.log X0 ^ 4 ≤ Real.log N)
    (ht1 : (X0 : ℝ) ≤ t) (ht2 : t ≤ N ^ (1 / 10 : ℝ))
    (hη0 : Real.exp (-(2 * Real.log X0)) ≤ η) (hη1 : η ≤ 1 / 2) (hZ : 2 * N ≤ Z)
    (hT : LocalPNT.Theorem524Concl P X0 (2 * N ^ (0.55 : ℝ))) :
    P.SIsum t N η ≤
      61.1 * (1 + 2.1 * Real.log t / Real.log N) * (η * Real.log t / Real.log N) := by
  -- notation and sizes
  set Λ := Real.log X0 with hΛdef
  set J := Real.log N with hJdef
  set τ := Real.log t with hτdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X0 := by
    by_contra hc; push_neg at hc
    have : (X0 : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have ht0 : 0 < t := lt_of_lt_of_le hX0 ht1
  have hτΛ : Λ ≤ τ := Real.log_le_log hX0 ht1
  have hτ8 : 100000000 ≤ τ := hΛ.trans hτΛ
  have hΛ4 : Λ ≤ Λ ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hΛ4' : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJbig : 30000000000000000000000000000000000 ≤ J := by nlinarith
  have hJ0 : 0 < J := by linarith
  have hNe : N = Real.exp J := (Real.exp_log hN0).symm
  have hτJ : τ ≤ J / 10 := by
    have := Real.log_le_log ht0 ht2
    rw [Real.log_rpow hN0] at this; linarith
  have hN1 : 1 < N := by rw [hNe]; exact Real.one_lt_exp_iff.mpr hJ0
  -- `Λ₁`, `P₁`
  set L1 := 100 * Λ ^ 3 with hL1
  have hΛ3 : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hL1big : 10000000000 ≤ L1 := by rw [hL1]; nlinarith
  set P1 := Real.exp L1 with hP1
  have hP1e10 : Real.exp 10 ≤ P1 := Real.exp_le_exp.mpr (by linarith)
  have hP1_4 : 4 ≤ P1 := by
    have := Real.add_one_le_exp (10 : ℝ); linarith
  have hP10 : 0 < P1 := Real.exp_pos _
  have hL1J : L1 ≤ J / 3000000 := by
    rw [hL1, le_div_iff₀ (by norm_num)]; nlinarith
  have hP1N : P1 ≤ N := by
    rw [hNe]; exact Real.exp_le_exp.mpr (by linarith)
  -- `M₀`
  set M0 := (1 / 2) * √(N / t) with hM0
  have hNt : 0 < N / t := div_pos hN0 ht0
  have hlogNt : Real.log (N / t) = J - τ := Real.log_div hN0.ne' ht0.ne'
  have hlogM0 : Real.log M0 = (J - τ) / 2 - Real.log 2 := by
    rw [hM0, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hNt).ne', Real.log_sqrt hNt.le,
      hlogNt, one_div, Real.log_inv]
    ring
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hM00 : 0 < M0 := by rw [hM0]; positivity
  have hM01 : 1 ≤ M0 := by
    rw [← Real.exp_log hM00]
    exact Real.one_le_exp (by rw [hlogM0]; linarith)
  -- Step 0: the decomposition
  have hdec := P.SIsum_le_decomp (t := t) (N := N) (η := η) (P1 := P1) hN1
    (le_trans (Real.exp_pos _).le hη0) (by linarith) ht0 hP10
  have hη : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hη0
  -- Part (B)
  have hB1 : P.vSmooth (N / 2) P1 ≤
      Real.exp 14 * L1 * Real.exp (-((J - Real.log 2) / L1)) := by
    have hR := rankin_crude h (ℓ := J - Real.log 2) hP1e10 (by linarith)
    rw [show Real.exp (J - Real.log 2) = N / 2 by
      rw [Real.exp_sub, Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← hNe], hP1,
      Real.log_exp] at hR
    exact hR
  have hB2 : P.vSmooth N P1 ≤ Real.exp 14 * L1 * Real.exp (-((J - Real.log 2) / L1)) := by
    have hR := rankin_crude h (ℓ := J) hP1e10 (by linarith)
    rw [← hNe, hP1, Real.log_exp] at hR
    refine hR.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : 0 < L1 := by linarith
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right this]; linarith
  have hB := BridgeSI.partB_small hΛ hJ hη0 hτΛ
  have hpartB : P.vSmooth (N / 2) P1 + P.vSmooth N P1 ≤ 0.01 * η * τ / J := by
    have : P.vSmooth (N / 2) P1 + P.vSmooth N P1 ≤
        2 * Real.exp 14 * (100 * Λ ^ 3) * Real.exp (-((J - Real.log 2) / (100 * Λ ^ 3))) := by
      rw [← hL1]; linarith
    linarith
  -- Part (A), the prime sums
  set M := P.SIcof t N η P1 with hMdef
  have hmemM : ∀ m ∈ M, P.val m ≤ N * (1 + η) / P1 ∧ √(N / t) ≤ P.val m := by
    intro m hm
    simp only [hMdef, SIcof, mem_filter, mem_elems] at hm
    exact ⟨hm.1, hm.2.1⟩
  have hwin : ∀ m ∈ M, ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j ≤
      1.1001 * η / Real.log (N / P.val m) := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmemM m hm
    have hv := P.val_pos m
    have hv0 : 0 < N / P.val m := div_pos hN0 hv
    -- `log(N/m) ≥ 99Λ³`
    have hlv : 99 * Λ ^ 3 ≤ Real.log (N / P.val m) := by
      have hge : P1 / 1.5 ≤ N / P.val m := by
        rw [div_le_div_iff₀ (by norm_num) hv]
        rw [le_div_iff₀ hP10] at h1; nlinarith
      have := Real.log_le_log (by positivity) hge
      rw [Real.log_div hP10.ne' (by norm_num), hP1, Real.log_exp] at this
      have h15 : Real.log 1.5 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.5 by norm_num); linarith
      linarith
    -- `v(1+2η) ≤ 2N^{0.55}`
    have hvy : N / P.val m * (1 + 2 * η) ≤ 2 * N ^ (0.55 : ℝ) := by
      have hlogv : Real.log (N / P.val m) ≤ 0.55 * J := by
        rw [Real.log_div hN0.ne' hv.ne']
        have h3 : (J - τ) / 2 ≤ Real.log (P.val m) := by
          have := Real.log_le_log (Real.sqrt_pos.mpr hNt) h2
          rwa [Real.log_sqrt hNt.le, hlogNt] at this
        linarith
      have hvle : N / P.val m ≤ N ^ (0.55 : ℝ) := by
        rw [Real.rpow_def_of_pos hN0, ← Real.exp_log hv0]
        exact Real.exp_le_exp.mpr (by rw [← hJdef]; linarith)
      have : 1 + 2 * η ≤ 2 := by linarith
      nlinarith [Real.rpow_pos_of_pos hN0 (0.55 : ℝ)]
    exact BridgeSI.sum_inv_window_le P hT hΛ hlv hη0 hη1 hvy
  have hA1 : ∑ m ∈ M, 1 / P.val m * ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j ≤
      1.1001 * η * ∑ m ∈ M, 1 / P.val m * (1 / Real.log (N / P.val m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hv := P.val_pos m
    calc 1 / P.val m * ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j
        ≤ 1 / P.val m * (1.1001 * η / Real.log (N / P.val m)) :=
          mul_le_mul_of_nonneg_left (hwin m hm) (by positivity)
      _ = 1.1001 * η * (1 / P.val m * (1 / Real.log (N / P.val m))) := by ring
  -- the blocks
  have hblocks := P.SIblocks_le (t := t) (N := N) (η := η) (P1 := P1) (M0 := M0) hM01 hP1_4
    (by linarith) hN0 (fun m hm => by rw [hM0]; linarith [(hmemM m hm).2])
  set K := M.image (P.SIidx M0) with hK
  -- each block in `K`
  have hkdata : ∀ k ∈ K, M0 * 2 ^ k < N * (1 + η) / P1 := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    have hM0p : 0 < M0 := hM00
    have h1 : 1 < P.val m / M0 := by
      rw [lt_div_iff₀ hM0p]; linarith [(hmemM m hm).2, hM0]
    have := (GenDyadic.dIdx_spec h1).1
    rw [lt_div_iff₀ hM0p] at this
    unfold SIidx
    linarith [(hmemM m hm).1]
  set Jt := J + Real.log 2 with hJt
  set ℓ0 := Real.log M0 with hℓ0
  have hlk : ∀ k : ℕ, Real.log (M0 * 2 ^ k) = ℓ0 + k * Real.log 2 := by
    intro k
    rw [Real.log_mul hM00.ne' (by positivity), Real.log_pow]
  have hNP : Real.log (N * (1 + η) / P1) ≤ J - L1 + 0.5 := by
    rw [Real.log_div (by positivity) hP10.ne', Real.log_mul hN0.ne' (by linarith), hP1,
      Real.log_exp]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + η by linarith)
    linarith
  have hℓk_up : ∀ k ∈ K, ℓ0 + k * Real.log 2 < J - L1 + 0.5 := by
    intro k hk
    rw [← hlk]
    have := Real.log_lt_log (by positivity) (hkdata k hk)
    linarith
  -- the per-block bound
  set s0 := BSaias.u0 (0.449 * J) with hs0
  have hterm : ∀ k ∈ K, P.Wsm t (M0 * 2 ^ k) (SIu N (M0 * 2 ^ k)) /
        Real.log (N / (2 * (M0 * 2 ^ k))) ≤
      1.002 * 38.3 * τ * (Dickman.rho (BridgeSI.uOf Jt (ℓ0 + k * Real.log 2) - 1) /
          ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2))) +
        Real.exp 14 * (J + 1) * Real.exp (-s0) := by
    intro k hk
    set Mk := M0 * 2 ^ k with hMk
    have hMk1 : 1 ≤ Mk := one_le_mul_of_one_le_of_one_le hM01 (one_le_pow₀ (by norm_num))
    have hMk0 : 0 < Mk := by linarith
    have hMkup := hkdata k hk
    have hℓk := hlk k
    have hℓ0e : ℓ0 = (J - τ) / 2 - Real.log 2 := hlogM0
    have hℓk_lo : (J - τ) / 2 - Real.log 2 ≤ Real.log Mk := by
      rw [hℓk]; have : (0 : ℝ) ≤ k * Real.log 2 := by positivity
      linarith
    have hMkN : Mk ≤ N := by
      have : N * (1 + η) / P1 ≤ N := by
        rw [div_le_iff₀ hP10]; nlinarith
      linarith
    have hMkP : Mk * P1 ≤ N * (1 + η) := by
      have := hMkup; rw [lt_div_iff₀ hP10] at this; linarith
    have hz10 : Real.exp 10 ≤ 2 * N / Mk := by
      rw [le_div_iff₀ hMk0]
      have h1 : Real.exp 10 * Mk ≤ P1 * Mk := mul_le_mul_of_nonneg_right hP1e10 hMk0.le
      have h2 : N * (1 + η) ≤ 2 * N := by nlinarith
      linarith
    have hzZ : 2 * N / Mk ≤ Z := by
      rw [div_le_iff₀ hMk0]; nlinarith
    have hσ1 : 1 ≤ Real.log (N / (2 * Mk)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      have h1 : Real.exp 1 * (2 * Mk) ≤ 6 * Mk := by nlinarith
      have h2 : 6 * Mk * P1 ≤ 9 * N := by nlinarith
      have h3 : 6 * Mk * 9 ≤ 6 * Mk * P1 := by
        have : (9 : ℝ) ≤ P1 := by have := Real.add_one_le_exp (10 : ℝ); linarith
        nlinarith
      nlinarith
    have hbt := BridgeSI.block_term_le h ht0 hτ8 hMk1 (by linarith) (by linarith)
      (by linarith) hz10 hzZ hσ1
    -- rewrite the main term
    have hlz : Real.log (2 * N / Mk) = Jt - Real.log Mk := by
      rw [Real.log_div (by positivity) hMk0.ne', Real.log_mul (by norm_num) hN0.ne', hJt]; ring
    have hlσ : Real.log (N / (2 * Mk)) = Jt - Real.log Mk - 2 * Real.log 2 := by
      rw [Real.log_div hN0.ne' (by positivity), Real.log_mul (by norm_num) hMk0.ne', hJt]; ring
    have hu : SIu N Mk = BridgeSI.uOf Jt (ℓ0 + k * Real.log 2) := by
      unfold SIu BridgeSI.uOf; rw [hlz, hℓk]
    rw [hu, hlσ, hℓk] at hbt
    rw [hu, hlσ, hℓk]
    have hRk : Real.exp 14 * Real.log (2 * N / Mk) * Real.exp (-BSaias.u0 (Real.log Mk)) ≤
        Real.exp 14 * (J + 1) * Real.exp (-s0) := by
      apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [hlz]
        have : 0 ≤ Real.log Mk := Real.log_nonneg hMk1
        linarith
      · apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]
        unfold BSaias.u0 BSCert.Z2.u0
        apply Real.sqrt_le_sqrt; apply Real.sqrt_le_sqrt
        linarith
    have hlMk : Real.log Mk = ℓ0 + k * Real.log 2 := hℓk
    rw [hlMk] at hRk
    calc _ ≤ _ := hbt
      _ = 1.002 * 38.3 * τ * (Dickman.rho (BridgeSI.uOf Jt (ℓ0 + k * Real.log 2) - 1) /
            ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2))) +
          Real.exp 14 * Real.log (2 * N / Mk) *
            Real.exp (-BSaias.u0 (ℓ0 + k * Real.log 2)) := by ring
      _ ≤ _ := add_le_add le_rfl hRk
  -- summing the blocks
  set E := Real.exp 14 * (J + 1) * Real.exp (-s0) with hE
  set g : ℕ → ℝ := fun k => Dickman.rho (BridgeSI.uOf Jt (ℓ0 + k * Real.log 2) - 1) /
      ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2)) with hg
  have hsumK : ∑ k ∈ K, P.Wsm t (M0 * 2 ^ k) (SIu N (M0 * 2 ^ k)) /
        Real.log (N / (2 * (M0 * 2 ^ k))) ≤
      1.002 * 38.3 * τ * ∑ k ∈ K, g k + K.card * E := by
    calc _ ≤ ∑ k ∈ K, (1.002 * 38.3 * τ * g k + E) := Finset.sum_le_sum hterm
      _ = 1.002 * 38.3 * τ * ∑ k ∈ K, g k + K.card * E := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  -- the index range
  set n := K.sup id + 1 with hn
  have hKn : ∀ k ∈ K, k < n := fun k hk => Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hℓ0e : ℓ0 = (J - τ) / 2 - Real.log 2 := hlogM0
  have htop : ℓ0 + n * Real.log 2 < Jt := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · have : n = 1 := by rw [hn, hK0]; rfl
      rw [this, hJt, hℓ0e]; push_cast; linarith
    · obtain ⟨k, hk, hks⟩ := Finset.exists_mem_eq_sup K hKne id
      have h1 := hℓk_up k hk
      have : (n : ℝ) = k + 1 := by rw [hn, hks]; push_cast; rfl
      rw [this, hJt]; linarith
  have hS0 : 0 < L1 - 2 := by linarith
  have hσK : ∀ k ∈ K, L1 - 2 ≤ Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2 := by
    intro k hk
    have := hℓk_up k hk
    rw [hJt]; linarith
  have hbs := BridgeSI.block_sum_le K hKn (by rw [hℓ0e]; linarith) htop hS0 hσK
  -- the lower limit `u_min`
  have hlogu := BridgeSI.umin_bound hJbig hτ8 hτJ hℓ0e hJt
  -- the Rankin terms
  have htailK := BridgeSI.tailK_bound hJbig hτ8 hη hs0 (K.card) E hE (by
    have h1 : K.card ≤ n := by
      calc K.card ≤ (Finset.range n).card :=
            Finset.card_le_card (fun k hk => Finset.mem_range.mpr (hKn k hk))
        _ = n := Finset.card_range n
    have h2 : (n : ℝ) * Real.log 2 ≤ J := by
      have := htop; rw [hJt, hℓ0e] at this; nlinarith
    have h3 : (n : ℝ) ≤ 2 * J := by
      have : (n : ℝ) * 0.69 ≤ (n : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      linarith
    calc (K.card : ℝ) ≤ n := by exact_mod_cast h1
      _ ≤ 2 * J := h3)
  have hg0 : 0 ≤ ∑ k ∈ K, g k := by
    refine Finset.sum_nonneg fun k hk => ?_
    have hσk := hσK k hk
    have hlk0 : 0 < ℓ0 + k * Real.log 2 := by
      rw [hℓ0e]; have : (0 : ℝ) ≤ k * Real.log 2 := by positivity
      linarith
    simp only [hg]
    exact div_nonneg (Dickman.rho_pos _).le (mul_nonneg hlk0.le (by linarith))
  have hfin := BridgeSI.si_final_arith hJbig hτ8 hτJ hη hL1big hg0 (hJt ▸ hbs) hlogu hpartB
    htailK
  calc P.SIsum t N η
      ≤ P.vSmooth (N / 2) P1 + P.vSmooth N P1 +
          ∑ m ∈ M, 1 / P.val m * ∑ j ∈ P.SIwin N η (P.val m), 1 / P.p j := hdec
    _ ≤ (P.vSmooth (N / 2) P1 + P.vSmooth N P1) +
          1.1001 * η * (1.002 * 38.3 * τ * ∑ k ∈ K, g k + K.card * E) := by
        refine add_le_add le_rfl (hA1.trans ?_)
        apply mul_le_mul_of_nonneg_left (hblocks.trans hsumK) (by linarith)
    _ ≤ _ := hfin

end HBS

end BeurlingSystem

end
