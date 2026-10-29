module

public import RequestProject.Beurling.BaseRange.EdgeNum

/-!
# §7.3: where the local prime number theorem is used, and the ranges of Proposition 5.35

With `Λ = log X₀ ≥ 10⁸`, `log X_LP = 10⁵ Λ² log² Λ` (eq. (88), `eq:XLP`, Theorem 5.24) and
`log X_sw = X₀^{1/100}` (the switch point between ranges (A) and (B) of Proposition 5.35):

* `xLP_le_xsw` : `log X_LP ≤ log X_sw`, i.e. `10⁵ Λ² log² Λ ≤ e^{Λ/100}`; so range (B), which
  starts at `X_sw`, lies above `X_LP`, and below `X_LP` only (84) is used;
* `xLP_le_sq` : `log X_LP ≤ X₀²` ("far below `log x₁ ≥ X₀²`");
* `x101_le_xsw` : `X₀^{1.01} ≤ X_sw`, i.e. `1.01 Λ ≤ e^{Λ/100}`;
* `xsw_le_mu0_limit` : `log X_sw ≤ (0.0048/κ)^{1/5}`, the limit of the response bound for `μ₀`
  (stated as `(log X_sw)⁵ κ ≤ 0.0048`);
* `mu0_limit_ge` : `(0.0048/κ)^{1/5} ≥ X₀^{0.079}` (stated as `X₀^{0.395} κ ≤ 0.0048`).
-/

@[expose] public section

open Real

namespace BaseRange

/-- `log X_LP = 10⁵ Λ² log² Λ ≤ e^{Λ/100} = log X_sw` for `Λ ≥ 10⁸`. -/
theorem xLP_le_xsw {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ Real.exp (Λ / 100) := by
  have hΛ0 : 0 < Λ := by linarith
  -- `log Λ ≤ 2√Λ`, so `log² Λ ≤ 4Λ`
  have hl : Real.log Λ ≤ Λ ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hΛ0.le (by norm_num)
  have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hsq : (Λ ^ (1 / 2 : ℝ)) ^ 2 = Λ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hl2 : Real.log Λ ^ 2 ≤ 4 * Λ := by
    have h1 : Real.log Λ ≤ 2 * Λ ^ (1 / 2 : ℝ) := by linarith
    calc Real.log Λ ^ 2 ≤ (2 * Λ ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 h1 2
      _ = 4 * Λ := by rw [mul_pow, hsq]; ring
  set y := Λ / 100 with hy
  have hy0 : 10 ^ 6 ≤ y := by rw [hy]; linarith
  have h6 := Real.pow_div_factorial_le_exp y (by linarith) 6
  have hf : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hΛy : Λ = 100 * y := by rw [hy]; ring
  have h1 : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ 10 ^ 5 * Λ ^ 2 * (4 * Λ) :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  have h2 : 10 ^ 5 * Λ ^ 2 * (4 * Λ) = 4 * 10 ^ 11 * y ^ 3 := by rw [hΛy]; ring
  have hy3 : (10 : ℝ) ^ 18 ≤ y ^ 3 := by
    calc (10 : ℝ) ^ 18 = (10 ^ 6) ^ 3 := by norm_num
      _ ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy0 3
  have h3 : 4 * 10 ^ 11 * y ^ 3 ≤ y ^ 6 / 720 := by
    have : y ^ 6 = y ^ 3 * y ^ 3 := by ring
    rw [this]
    have : 0 ≤ y ^ 3 := by positivity
    nlinarith
  linarith

/-- `log X_LP ≤ e^{2Λ} = X₀²`. -/
theorem xLP_le_sq {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ Real.exp (2 * Λ) :=
  (xLP_le_xsw hΛ).trans (Real.exp_le_exp.mpr (by linarith))

/-- `X₀^{1.01} ≤ X_sw`: `1.01 Λ ≤ e^{Λ/100}`. -/
theorem x101_le_xsw {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : 1.01 * Λ ≤ Real.exp (Λ / 100) := by
  have h := xLP_le_xsw hΛ
  have hl : 1 ≤ Real.log Λ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have : 1.01 * Λ ≤ 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 := by
    have h1 : 1 ≤ Real.log Λ ^ 2 := one_le_pow₀ hl
    nlinarith
  linarith

/-- `log X_sw ≤ (0.0048/κ)^{1/5}`, as `(X₀^{1/100})⁵ κ ≤ 0.0048`. -/
theorem xsw_le_mu0_limit {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) :
    ((X0 : ℝ) ^ (1 / 100 : ℝ)) ^ 5 * Construction.kappaParam X0 ≤ 0.0048 := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  rw [rpow_eq_exp hX0, ← Real.exp_nat_mul, Construction.kappaParam, rpow_eq_exp hX0,
    ← Real.exp_add]
  refine le_trans (Real.exp_le_exp.mpr (by nlinarith : _ ≤ (-100 : ℝ))) ?_
  have := exp_neg_100_le
  linarith

/-- `(0.0048/κ)^{1/5} ≥ X₀^{0.079}`, as `(X₀^{0.079})⁵ κ ≤ 0.0048`. -/
theorem mu0_limit_ge {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) :
    ((X0 : ℝ) ^ (0.079 : ℝ)) ^ 5 * Construction.kappaParam X0 ≤ 0.0048 := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  rw [rpow_eq_exp hX0, ← Real.exp_nat_mul, Construction.kappaParam, rpow_eq_exp hX0,
    ← Real.exp_add]
  refine le_trans (Real.exp_le_exp.mpr (by nlinarith : _ ≤ (-100 : ℝ))) ?_
  have := exp_neg_100_le
  linarith

end BaseRange
