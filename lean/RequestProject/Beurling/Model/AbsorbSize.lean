module

public import RequestProject.Beurling.AbsorbEmpty
public import RequestProject.Beurling.Construction.JitterRegular

/-!
# The size of the absorption threshold: `log 3y(x) ≤ 23 √(log x)` above `log x = Λ²`

Theorem 6.23(b),(c) and Remark 6.24 (05-queue.tex): `log H ≤ 8ℓ² + 15Λ + 2` (as `M̄₁ ≤ 2c`,
`log c ≤ 4ℓ² + 7.5Λ`, `γ ≤ 7.5`), `L₀ ≤ 2135 M̄₁ L⁵`, so
`log 3y(x) ≤ 12ℓ² + 11ℓ + 22.5Λ + 12`, and where `Λ² < L` this is `≤ 23 √L`
(`log_three_absorbYAt_le`). Used in Lemma 6.27(b) (`SigmaA.lean`).
-/

@[expose] public section

open Real CaplLink BSCert.Capl AbsorbEmpty

namespace AbsorbSize

/-- `γ ≤ 7.5` (Theorem 6.23: `γ = γ* ≤ γ*(s_H)` below `s_H`, the ramp, `7.5` above). -/
lemma gam_le (s : ℝ) : gam sHroot s ≤ 7.5 := by
  have hsH := sHroot_mem
  have hgH : gstar sHroot = 1 / 3 - 1 / 100000 := by rw [gstar_sHroot]; rfl
  unfold gam
  split_ifs with h1 h2
  · have := gstar_mono h1 (by linarith [hsH.2]); rw [hgH] at this; linarith
  · rw [hgH]
    have : 0 ≤ s - sHroot := by push_neg at h1; linarith
    nlinarith
  · norm_num

/-- `log c ≤ 4ℓ² + 7.5Λ`. -/
lemma logc_le {Λ s : ℝ} (hΛ : 0 ≤ Λ) :
    logc sHroot Λ s ≤ 4 * (2 * Real.log Λ + s) ^ 2 + 7.5 * Λ := by
  unfold logc
  have h1 := gam_le s
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply max_le
  · nlinarith
  · nlinarith

variable {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
include hX0 hX hx

/-- `M̄₁ ≤ 2e^{4ℓ² + 7.5Λ}`. -/
lemma capM1_le : capM1 X₀ x ≤ 2 * Real.exp (4 * Real.log (Real.log x) ^ 2 +
    7.5 * Real.log X₀) := by
  have hℓ : 18 ≤ 2 * Real.log (Real.log X₀) + capS X₀ x := by
    rw [ell_eq]
    obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
    have := log_ge_18 (show (100000000 : ℝ) ≤ Real.log x by norm_num at h1 ⊢; linarith)
    exact this
  have h := Mbar1_le (sH := sHroot) hℓ
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have := logc_le (s := capS X₀ x) (show (0 : ℝ) ≤ Real.log X₀ by linarith)
  rw [ell_eq] at this
  exact this

/-- `H ≤ e^{8ℓ² + 15Λ + 2}`. -/
lemma capH_le_exp : capH X₀ x ≤ Real.exp (8 * Real.log (Real.log x) ^ 2 +
    15 * Real.log X₀ + 2) := by
  unfold capH
  have hΛ : 0 ≤ Real.log X₀ := by linarith
  apply max_le
  · exact Real.exp_le_exp.mpr (by linarith)
  · have hM := capM1_le hX0 hX hx
    have hM0 := capM1_pos hX0 hX hx
    calc capM1 X₀ x ^ 2 ≤ (2 * Real.exp (4 * Real.log (Real.log x) ^ 2 +
          7.5 * Real.log X₀)) ^ 2 := pow_le_pow_left₀ hM0.le hM 2
      _ = 4 * Real.exp (8 * Real.log (Real.log x) ^ 2 + 15 * Real.log X₀) := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (8 * Real.log (Real.log x) ^ 2 + 15 * Real.log X₀ + 2) := by
          rw [Real.exp_add _ 2]
          have : (4 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (1 : ℝ)
            have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
            nlinarith
          nlinarith [Real.exp_pos (8 * Real.log (Real.log x) ^ 2 + 15 * Real.log X₀)]

/-- **`log 3y(x) ≤ 12ℓ² + 11ℓ + 22.5Λ + 12`** (Remark 6.24). -/
lemma log_absorbYAt_le :
    Real.log (3 * absorbYAt X₀ x) ≤ 12 * Real.log (Real.log x) ^ 2 +
      11 * Real.log (Real.log x) + 22.5 * Real.log X₀ + 12 := by
  obtain ⟨hL, -, hℓ0⟩ := logs_of_ge hX0 hX hx
  set L := Real.log x with hLdef
  set ℓ := Real.log L with hℓdef
  set Λ := Real.log X₀ with hΛdef
  have hL0 : 0 < L := by linarith
  have hℓ18 : 18 ≤ ℓ := log_ge_18 (by norm_num at hL ⊢; linarith)
  have hM := capM1_le hX0 hX hx
  have hM0 := capM1_pos hX0 hX hx
  have hH := capH_le_exp hX0 hX hx
  have hH0 : 0 < capH X₀ x := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  have hM1 : 1 ≤ capM1 X₀ x := by
    have hr : 0 ≤ rbar0 (Real.log X₀) (capS X₀ x) := rbar0_nonneg (by rw [ell_eq]; linarith)
    have hc0 := Real.exp_pos (logc sHroot (Real.log X₀) (capS X₀ x))
    show 1 ≤ rbar0 (Real.log X₀) (capS X₀ x) + (Real.exp (logc sHroot (Real.log X₀) (capS X₀ x)) +
      rbar0 (Real.log X₀) (capS X₀ x) *
        Real.sqrt (Real.exp (logc sHroot (Real.log X₀) (capS X₀ x))) +
      rbar0 (Real.log X₀) (capS X₀ x) * (rbar0 (Real.log X₀) (capS X₀ x) + 1) / 2) + 1
    have : 0 ≤ rbar0 (Real.log X₀) (capS X₀ x) *
        Real.sqrt (Real.exp (logc sHroot (Real.log X₀) (capS X₀ x))) := by positivity
    have : 0 ≤ rbar0 (Real.log X₀) (capS X₀ x) * (rbar0 (Real.log X₀) (capS X₀ x) + 1) / 2 := by
      positivity
    linarith
  have hL1 : 1 ≤ L := by linarith
  -- `L₀ ≤ 2135 M̄₁ L⁵`
  have hL0b : absorbL0 X₀ x ≤ 2135 * capM1 X₀ x * L ^ 5 := by
    unfold absorbL0
    rw [← hLdef]
    have hL3 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
    have hL5 : 0 ≤ L ^ 5 := by positivity
    apply max_le
    · nlinarith
    · rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hL0pos : 0 < absorbL0 X₀ x := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hy : 3 * absorbYAt X₀ x ≤ 3 * (Real.exp (8 * ℓ ^ 2 + 15 * Λ + 2) *
      (2135 * (2 * Real.exp (4 * ℓ ^ 2 + 7.5 * Λ)) * L ^ 5) * L ^ 6) := by
    unfold absorbYAt
    rw [← hLdef]
    have h1 : absorbL0 X₀ x ≤ 2135 * (2 * Real.exp (4 * ℓ ^ 2 + 7.5 * Λ)) * L ^ 5 :=
      hL0b.trans (by gcongr)
    gcongr
  have hy0 : 0 < 3 * absorbYAt X₀ x := by unfold absorbYAt; positivity
  have e1 : 3 * (Real.exp (8 * ℓ ^ 2 + 15 * Λ + 2) *
      (2135 * (2 * Real.exp (4 * ℓ ^ 2 + 7.5 * Λ)) * L ^ 5) * L ^ 6) =
      12810 * L ^ 11 * Real.exp (12 * ℓ ^ 2 + 22.5 * Λ + 2) := by
    rw [show 12 * ℓ ^ 2 + 22.5 * Λ + 2 = (8 * ℓ ^ 2 + 15 * Λ + 2) + (4 * ℓ ^ 2 + 7.5 * Λ)
      by ring, Real.exp_add (8 * ℓ ^ 2 + 15 * Λ + 2) (4 * ℓ ^ 2 + 7.5 * Λ)]; ring
  have h1 : Real.log 12810 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (12810 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := by gcongr
  have h2 : Real.log (12810 * L ^ 11 * Real.exp (12 * ℓ ^ 2 + 22.5 * Λ + 2)) =
      Real.log 12810 + 11 * ℓ + (12 * ℓ ^ 2 + 22.5 * Λ + 2) := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  calc Real.log (3 * absorbYAt X₀ x) ≤ Real.log (12810 * L ^ 11 *
        Real.exp (12 * ℓ ^ 2 + 22.5 * Λ + 2)) := by
        rw [← e1]; exact Real.log_le_log hy0 hy
    _ ≤ 12 * ℓ ^ 2 + 11 * ℓ + 22.5 * Λ + 12 := by rw [h2]; linarith

omit hX0 hX hx in
/-- `12ℓ² + 11ℓ + 12 ≤ √L/2` for `L ≥ 10¹⁶`. -/
lemma ell_poly_le {L : ℝ} (hL : 10 ^ 16 ≤ L) :
    12 * Real.log L ^ 2 + 11 * Real.log L + 12 ≤ Real.sqrt L / 2 := by
  have hL0 : 0 < L := by linarith
  set r := L ^ (1 / 8 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hlog : Real.log L ≤ 8 * r := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    rw [← hr] at this; linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt L = r ^ 4 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Real.sqrt_eq_rpow]; norm_num
  have hr4 : (10 : ℝ) ^ 4 ≤ r ^ 2 := by
    have h1 : (10 : ℝ) ^ 16 = ((10 : ℝ) ^ 2) ^ 8 := by norm_num
    have hr8 : r ^ 8 = L := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have h2 : ((10 : ℝ) ^ 2) ^ 8 ≤ r ^ 8 := by rw [hr8]; norm_num at hL ⊢; linarith
    have h3 : (10 : ℝ) ^ 2 ≤ r := by
      by_contra hc; push_neg at hc
      have : r ^ 8 < ((10 : ℝ) ^ 2) ^ 8 := pow_lt_pow_left₀ hc hr0.le (by norm_num)
      linarith
    nlinarith
  rw [hsq]
  have h1 : 12 * Real.log L ^ 2 ≤ 768 * r ^ 2 := by nlinarith
  have h2 : 11 * Real.log L ≤ 88 * r := by linarith
  have hr1 : 1 ≤ r := by nlinarith
  nlinarith

/-- **`log 3y(x) ≤ 23 √(log x)`** where `(log X₀)² < log x`. -/
theorem log_three_absorbYAt_le (hbig : Real.log X₀ ^ 2 < Real.log x) :
    Real.log (3 * absorbYAt X₀ x) ≤ 23 * Real.sqrt (Real.log x) := by
  have h := log_absorbYAt_le hX0 hX hx
  have hΛ0 : 0 ≤ Real.log X₀ := by linarith
  have hL16 : 10 ^ 16 ≤ Real.log x := by
    have : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hX 2; norm_num at this ⊢; linarith
    linarith
  have hp := ell_poly_le hL16
  have hΛ : Real.log X₀ ≤ Real.sqrt (Real.log x) := by
    rw [← Real.sqrt_sq hΛ0]; exact Real.sqrt_le_sqrt hbig.le
  linarith

end AbsorbSize
