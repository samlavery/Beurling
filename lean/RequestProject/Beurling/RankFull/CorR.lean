module

public import Mathlib

/-!
# Corollary A.13 (the case of rank at least `r₀`): the numerics

Corollary A.13 of Appendix A: with `k = r₀ = ⌈L/(3ℓ)⌉ + 3`, `δ = 4L^{-6}` and `L ≥ 465`, the right
side of Theorem A.12, multiplied by `2z/δ + 1` (a bound for the number of grid windows at height
`z ≤ x = e^L`), is at most `L^{-4}`.

We state it for abstract parameters:
* `θ a b > 0` with `θ a b ≤ 1.01` (in the paper `a = e^{(3H(X₀)+2)/X₀}`, `b = e^{2.2/Λ}`,
  `θ = 1 + 1/Λ`; the bound `1.01` uses `H(X₀)/X₀ ≤ e^{-10⁷}` and `Λ ≥ 10⁸`);
* `0 ≤ A_R ≤ 1.8(L + 4)` (`A_R = 1.8(log z + 4)`, `z ≤ x`);
* `1 ≤ u ≤ 2L` (`u = 1 + r₀/X₀`);
* `L/(3ℓ) + 3 ≤ k` with `ℓ = log L`.

* `RankFull.cor_R_numeric` : `(2z/δ + 1)(eθA_Rδ)^k a^k u^{1.02k} b^k ≤ L^{-4}`.
-/

@[expose] public section

open Real

namespace RankFull

lemma two_rpow_102_le : (2 : ℝ) ^ (1.02 : ℝ) ≤ 2.03 := by
  have h1 : (2 : ℝ) ^ (1.02 : ℝ) = 2 * 2 ^ (0.02 : ℝ) := by
    rw [show (1.02 : ℝ) = 1 + 0.02 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  have h2 : (2 : ℝ) ^ (0.02 : ℝ) ≤ 1.015 := by
    have h3 : ((2 : ℝ) ^ (0.02 : ℝ)) ^ (50 : ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h4 : (2 : ℝ) ≤ (1.015 : ℝ) ^ (50 : ℕ) := by norm_num
    by_contra h
    push_neg at h
    have : (1.015 : ℝ) ^ (50 : ℕ) < ((2 : ℝ) ^ (0.02 : ℝ)) ^ (50 : ℕ) :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    linarith
  rw [h1]; linarith

lemma log_465_ge : (5.9 : ℝ) ≤ Real.log 465 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 5.9 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 := pow_le_pow_left₀ (by positivity) h.le 6
  have : (2.7182818286 : ℝ) ^ 6 ≤ 465 := by norm_num
  linarith

lemma log_15e_le : Real.log (15 * Real.exp 1) ≤ 3.7726 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have h15 : Real.log 15 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

/-- The per-element factor of Corollary A.13: `e θ A_R δ a u^{1.02} b ≤ 15e L^{-3.98}`. -/
lemma per_element_le {L θ a b A_R u : ℝ} (hL : 465 ≤ L)
    (hθab : θ * a * b ≤ 1.01) (hAR0 : 0 ≤ A_R) (hAR : A_R ≤ 1.8 * (L + 4)) (hu1 : 1 ≤ u)
    (hu : u ≤ 2 * L) :
    Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ)) * a * u ^ (1.02 : ℝ) * b ≤
      15 * Real.exp 1 * L ^ (-3.98 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hu102 : u ^ (1.02 : ℝ) ≤ 2.03 * L ^ (1.02 : ℝ) := by
    calc u ^ (1.02 : ℝ) ≤ (2 * L) ^ (1.02 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hu (by norm_num)
      _ = 2 ^ (1.02 : ℝ) * L ^ (1.02 : ℝ) := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ 2.03 * L ^ (1.02 : ℝ) := by
          apply mul_le_mul_of_nonneg_right two_rpow_102_le (by positivity)
  have hpow' : L ^ (-6 : ℝ) * L ^ (1.02 : ℝ) * L = L ^ (-3.98 : ℝ) := by
    rw [← Real.rpow_add hL0]
    have : L ^ ((-6 : ℝ) + 1.02) * L = L ^ ((-6 : ℝ) + 1.02) * L ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hL0]; norm_num
  have hP : 0 < L ^ (-6 : ℝ) * L ^ (1.02 : ℝ) := by positivity
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hL4 : L + 4 ≤ 1.0087 * L := by linarith
  have hupos : 0 ≤ u ^ (1.02 : ℝ) := by positivity
  calc Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ)) * a * u ^ (1.02 : ℝ) * b
      = Real.exp 1 * (θ * a * b) * A_R * (4 * L ^ (-6 : ℝ)) * u ^ (1.02 : ℝ) := by ring
    _ ≤ Real.exp 1 * 1.01 * (1.8 * (1.0087 * L)) * (4 * L ^ (-6 : ℝ)) *
          (2.03 * L ^ (1.02 : ℝ)) := by
        gcongr
        · linarith
    _ = Real.exp 1 * (1.01 * 1.8 * 1.0087 * 4 * 2.03) * (L ^ (-6 : ℝ) * L ^ (1.02 : ℝ) * L) := by
        ring
    _ ≤ Real.exp 1 * 15 * (L ^ (-6 : ℝ) * L ^ (1.02 : ℝ) * L) := by
        gcongr; norm_num
    _ = 15 * Real.exp 1 * L ^ (-3.98 : ℝ) := by rw [hpow']; ring

/-- The final inequality of Corollary A.13:
`L + 6ℓ + (L/(3ℓ) + 3)(3.7726 - 3.98ℓ) ≤ -4ℓ` for `L ≥ 465`, `ℓ = log L`. -/
lemma cor_R_log_ineq {L : ℝ} (hL : 465 ≤ L) :
    L + 6 * Real.log L + (L / (3 * Real.log L) + 3) * (3.7726 - 3.98 * Real.log L) ≤
      -4 * Real.log L := by
  set ℓ := Real.log L with hℓ
  have hℓ0 : 5.9 ≤ ℓ := log_465_ge.trans (Real.log_le_log (by norm_num) hL)
  have hℓpos : 0 < ℓ := by linarith
  have key : 3 * ℓ * L + 18 * ℓ ^ 2 + (L + 9 * ℓ) * (3.7726 - 3.98 * ℓ) ≤ -12 * ℓ ^ 2 := by
    nlinarith
  have h3 : L / (3 * ℓ) + 3 = (L + 9 * ℓ) / (3 * ℓ) := by field_simp; ring
  rw [h3]
  have : (L + 9 * ℓ) / (3 * ℓ) * (3.7726 - 3.98 * ℓ) =
      ((L + 9 * ℓ) * (3.7726 - 3.98 * ℓ)) / (3 * ℓ) := by ring
  rw [this]
  have h3l : 0 < 3 * ℓ := by linarith
  have : ((L + 9 * ℓ) * (3.7726 - 3.98 * ℓ)) / (3 * ℓ) ≤ (-12 * ℓ ^ 2 - 3 * ℓ * L - 18 * ℓ ^ 2) /
      (3 * ℓ) := div_le_div_of_nonneg_right (by linarith) h3l.le
  have h4 : (-12 * ℓ ^ 2 - 3 * ℓ * L - 18 * ℓ ^ 2) / (3 * ℓ) = -4 * ℓ - L - 6 * ℓ := by
    field_simp; ring
  linarith

/-- **Corollary A.13 (numerics).** For `L ≥ 465`, `0 < z ≤ e^L`, `δ = 4L^{-6}`, `k ≥ L/(3ℓ) + 3`
(`ℓ = log L`), and the parameters as in the module docstring,
`(2z/δ + 1) (e θ A_R δ)^k a^k u^{1.02k} b^k ≤ L^{-4}`. -/
theorem cor_R_numeric {L z θ a b A_R u : ℝ} {k : ℕ} (hL : 465 ≤ L) (hz0 : 0 < z)
    (hz : z ≤ Real.exp L) (hθ : 0 < θ) (ha : 0 < a) (hb : 0 < b) (hθab : θ * a * b ≤ 1.01)
    (hAR0 : 0 ≤ A_R) (hAR : A_R ≤ 1.8 * (L + 4)) (hu1 : 1 ≤ u) (hu : u ≤ 2 * L)
    (hk : L / (3 * Real.log L) + 3 ≤ k) :
    (2 * z / (4 * L ^ (-6 : ℝ)) + 1) * (Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ))) ^ k * a ^ k *
        u ^ (1.02 * (k : ℝ)) * b ^ k ≤ L ^ (-4 : ℝ) := by
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ0 : 5.9 ≤ ℓ := log_465_ge.trans (Real.log_le_log (by norm_num) hL)
  -- the window count
  have hL6 : (L ^ (-6 : ℝ))⁻¹ = L ^ (6 : ℕ) := by
    rw [Real.rpow_neg hL0.le, inv_inv]; norm_cast
  have hwin : 2 * z / (4 * L ^ (-6 : ℝ)) + 1 ≤ Real.exp (L + 6 * ℓ) := by
    rw [Real.exp_add, show 6 * ℓ = (6 : ℕ) * Real.log L by push_cast; ring, ← Real.log_pow,
      Real.exp_log (by positivity)]
    have h1 : 2 * z / (4 * L ^ (-6 : ℝ)) = z * L ^ (6 : ℕ) / 2 := by
      rw [div_eq_mul_inv, mul_inv, hL6]; ring
    rw [h1]
    have h2 : (1 : ℝ) ≤ Real.exp L * L ^ (6 : ℕ) / 2 := by
      have : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL0.le
      have : (465 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
      nlinarith
    have h3 : z * L ^ (6 : ℕ) / 2 ≤ Real.exp L * L ^ (6 : ℕ) / 2 := by gcongr
    nlinarith
  -- the per-element factor
  set q := Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ)) * a * u ^ (1.02 : ℝ) * b with hq
  have hq0 : 0 ≤ q := by positivity
  have hqle : q ≤ Real.exp (3.7726 - 3.98 * ℓ) := by
    refine (per_element_le hL hθab hAR0 hAR hu1 hu).trans ?_
    rw [Real.exp_sub, show 3.98 * ℓ = Real.log (L ^ (3.98 : ℝ)) by
      rw [Real.log_rpow hL0]]
    rw [Real.exp_log (by positivity), Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    gcongr
    calc 15 * Real.exp 1 = Real.exp (Real.log (15 * Real.exp 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp 3.7726 := Real.exp_le_exp.mpr log_15e_le
  have hprod : (Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ))) ^ k * a ^ k *
      u ^ (1.02 * (k : ℝ)) * b ^ k = q ^ k := by
    rw [hq, Real.rpow_mul (by linarith), Real.rpow_natCast]
    ring
  have hneg : 3.7726 - 3.98 * ℓ ≤ 0 := by linarith
  have hqk : q ^ k ≤ Real.exp ((L / (3 * ℓ) + 3) * (3.7726 - 3.98 * ℓ)) := by
    calc q ^ k ≤ Real.exp (3.7726 - 3.98 * ℓ) ^ k := pow_le_pow_left₀ hq0 hqle k
      _ = Real.exp (k * (3.7726 - 3.98 * ℓ)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((L / (3 * ℓ) + 3) * (3.7726 - 3.98 * ℓ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hk hneg)
  rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc ((Real.exp 1 * θ * A_R *
    (4 * L ^ (-6 : ℝ))) ^ k), ← mul_assoc _ (u ^ (1.02 * (k : ℝ))), hprod]
  calc (2 * z / (4 * L ^ (-6 : ℝ)) + 1) * q ^ k
      ≤ Real.exp (L + 6 * ℓ) * Real.exp ((L / (3 * ℓ) + 3) * (3.7726 - 3.98 * ℓ)) :=
        mul_le_mul hwin hqk (by positivity) (by positivity)
    _ = Real.exp (L + 6 * ℓ + (L / (3 * ℓ) + 3) * (3.7726 - 3.98 * ℓ)) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (-4 * ℓ) := Real.exp_le_exp.mpr (cor_R_log_ineq hL)
    _ = L ^ (-4 : ℝ) := by
        rw [Real.rpow_def_of_pos hL0, hℓ]; ring_nf

end RankFull
