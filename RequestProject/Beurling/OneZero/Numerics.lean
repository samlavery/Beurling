module

public import RequestProject.Beurling.Lemmas

/-!
# Numerics of the design `θ = 0` (Theorem A′, §8 of the paper)

The per-zero exponent `θ_k = 9 ℓ_k²/L_k` (`thK 0`) and the late-lag exponent
`η_k = 17 ℓ_k²/(2 L_k)`, with `L_k = log x⁺_k` and `ℓ_k = log L_k`:

* `late_lag_exp` : `8 (log log y)² + Λ + 2 ≤ η_k log y` for `log y ≥ L_k - 1` (so the lag bound
  `|D(y)| ≤ e^{8ℓ² + Λ + 2}` gives `|D(y)| ≤ y^{η_k}` beyond `a_k`);
* `late_numeric` : `150 Λ x^{-e} ≤ 1/100` when `e log x ≥ 9 log log x ≥ 18 Λ`.
-/

@[expose] public section

namespace OneZero

/-- `log² r ≤ 4 (r - 1)` for `r ≥ 1`. -/
lemma log_sq_le {r : ℝ} (hr : 1 ≤ r) : Real.log r ^ 2 ≤ 4 * (r - 1) := by
  have hs : 1 ≤ Real.sqrt r := by rw [Real.one_le_sqrt]; exact hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hlog : Real.log r = 2 * Real.log (Real.sqrt r) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_pow]; norm_num
  have h1 : Real.log (Real.sqrt r) ≤ Real.sqrt r - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h0 : 0 ≤ Real.log (Real.sqrt r) := Real.log_nonneg hs
  rw [hlog]
  nlinarith

/-- **The late-lag exponent.** For `Λ ≥ 10`, `ℓ = log L ≥ 2Λ` and `log y = M ≥ L - 1`:
`8 (log M)² + Λ + 2 ≤ (17 ℓ²/(2L)) M`. -/
theorem late_lag_exp {Λ L M : ℝ} (hΛ : 10 ≤ Λ) (hL : 1 < L) (hℓ : 2 * Λ ≤ Real.log L)
    (hM : L - 1 ≤ M) :
    8 * Real.log M ^ 2 + Λ + 2 ≤ 17 * Real.log L ^ 2 / (2 * L) * M := by
  set ℓ := Real.log L with hℓdef
  have hL0 : 0 < L := by linarith
  have hℓ20 : 20 ≤ ℓ := by linarith
  have hLe : L = Real.exp ℓ := (Real.exp_log hL0).symm
  have h3 := Real.pow_div_factorial_le_exp ℓ (by linarith) 3
  norm_num [Nat.factorial] at h3
  have hℓL : ℓ ^ 2 ≤ L := by rw [hLe]; nlinarith
  have hL400 : 400 ≤ L := by nlinarith
  set r := M / L with hr
  have hMr : M = r * L := by rw [hr]; field_simp
  have hr0 : 0 < r := by rw [hr]; apply div_pos _ hL0; linarith
  have hlogM : Real.log M = Real.log r + ℓ := by
    rw [hMr, Real.log_mul hr0.ne' hL0.ne']
  have hRHS : 17 * ℓ ^ 2 / (2 * L) * M = 17 / 2 * ℓ ^ 2 * r := by
    rw [hMr]; field_simp
  rw [hlogM, hRHS]
  have hΛℓ : 4 * Λ ^ 2 ≤ ℓ ^ 2 := by nlinarith
  rcases le_or_gt r 1 with h1 | h1
  · -- `r ≤ 1`: `log r ∈ [-1/(L-1), 0]`
    have hlr0 : Real.log r ≤ 0 := Real.log_nonpos hr0.le h1
    have hrL : 1 - 1 / L ≤ r := by
      rw [hr, le_div_iff₀ hL0]; field_simp; linarith
    have hlr1 : -1 ≤ Real.log r := by
      have := Real.one_sub_inv_le_log_of_pos hr0
      have hinv : 1 / r ≤ 2 := by
        rw [div_le_iff₀ hr0]
        have : 1 / L ≤ 1 / 2 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
        linarith
      rw [inv_eq_one_div] at this; linarith
    have hsq : (Real.log r + ℓ) ^ 2 ≤ ℓ ^ 2 := by nlinarith
    have hrr : 17 / 2 * ℓ ^ 2 * (1 - 1 / L) ≤ 17 / 2 * ℓ ^ 2 * r := by gcongr
    have hsmall : ℓ ^ 2 * (1 / L) ≤ 1 := by
      rw [mul_one_div, div_le_one hL0]; exact hℓL
    nlinarith
  · -- `r ≥ 1`
    have hlr0 : 0 ≤ Real.log r := Real.log_nonneg h1.le
    have hlr1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
    have hlr2 := log_sq_le h1.le
    have hsq : (Real.log r + ℓ) ^ 2 ≤ ℓ ^ 2 + 2 * ℓ * (r - 1) + 4 * (r - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hlr1 (show 0 ≤ 2 * ℓ by linarith)]
    have hr1 : 0 ≤ r - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right (show 16 * ℓ + 32 ≤ 17 / 2 * ℓ ^ 2 by nlinarith) hr1]

/-- **Late-noise numerics.** If `x > 1`, `Λ ≥ 10`, `2Λ ≤ ℓ = log log x` and `9ℓ ≤ e log x`, then
`150 Λ x^{-e} ≤ 1/100`. -/
theorem late_numeric {Λ x e : ℝ} (hΛ : 10 ≤ Λ) (hx : 1 < x)
    (hℓ : 2 * Λ ≤ Real.log (Real.log x)) (he : 9 * Real.log (Real.log x) ≤ e * Real.log x) :
    150 * Λ * x ^ (-e) ≤ 1 / 100 := by
  have hx0 : 0 < x := by linarith
  have h18 : 18 * Λ ≤ e * Real.log x := by linarith
  rw [Real.rpow_def_of_pos hx0, show Real.log x * -e = -(e * Real.log x) by ring, Real.exp_neg]
  have hmono : Real.exp (18 * Λ) ≤ Real.exp (e * Real.log x) := Real.exp_le_exp.mpr h18
  have h6 : 6 * Λ ≤ Real.exp (6 * Λ) := by linarith [Real.add_one_le_exp (6 * Λ)]
  have hcube : (6 * Λ) ^ 3 ≤ Real.exp (18 * Λ) := by
    have e3 : Real.exp (18 * Λ) = Real.exp (6 * Λ) ^ 3 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e3]; exact pow_le_pow_left₀ (by linarith) h6 3
  have hpos := Real.exp_pos (e * Real.log x)
  have hΛ3 : 150 * Λ * 100 ≤ (6 * Λ) ^ 3 := by
    have : 100 ≤ Λ ^ 2 := by nlinarith
    have e2 : (6 * Λ) ^ 3 = 216 * Λ * Λ ^ 2 := by ring
    rw [e2]; nlinarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
  linarith

end OneZero

end
