module

public import Mathlib

/-!
# Positivity of the target (Lemma 3.3)

The continuous part of the target has slope `T'_cont = 1 - ρ_det - ρ̄_A + R'`.

* `Positivity.positivity_margin` : **Lemma 3.3 (7)**, the assembly: from the rigid bound
  `1 - ρ_det(u) ≥ 0.99/log u - 1/(κu)` (short-interval prime number theorem), the cap
  `ρ̄_A = min(ρ_A, 0.1/log u)` and the oscillation slope `|R'(u)| ≤ κ₊/log u`, `κ₊ = 0.8`,
  `T'_cont(u) ≥ 0.09/log u - 1/(κu)`.
* `Positivity.inv_kappa_mul_le` : for `κ = X₀^{-5/12 + 2ε_κ}`, `ε_κ = 0.01`, and `u ≥ X₀` with
  `log X₀ ≥ 10⁸`, `1/(κu) ≤ 0.01/log u`.
* `Positivity.slope_pos` : hence `T'_cont(u) ≥ 0.08/log u > 0`.
-/

@[expose] public section

namespace Positivity

/-- **Lemma 3.3 (positivity margin), the assembly step.** -/
theorem positivity_margin {u κ rhoDet rhoA R' : ℝ} (hL : 0 < Real.log u)
    (hdet : 0.99 / Real.log u - 1 / (κ * u) ≤ 1 - rhoDet)
    (hR : |R'| ≤ 0.8 / Real.log u) :
    0.09 / Real.log u - 1 / (κ * u) ≤ 1 - rhoDet - min rhoA (0.1 / Real.log u) + R' := by
  have h1 : min rhoA (0.1 / Real.log u) ≤ 0.1 / Real.log u := min_le_right _ _
  have h2 := (abs_le.mp hR).1
  have e : 0.09 / Real.log u = 0.99 / Real.log u - 0.1 / Real.log u - 0.8 / Real.log u := by
    field_simp; norm_num
  linarith

/-- `1/(κu) ≤ 0.01/log u` for `κ = X₀^{-(5/12 - 1/50)}`, `u ≥ X₀ > 0`, `log X₀ ≥ 10⁸`. -/
theorem inv_kappa_mul_le {X₀ u : ℝ} (hX0 : 0 < X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hu : X₀ ≤ u) :
    1 / (X₀ ^ (-(5 / 12 - 1 / 50 : ℝ)) * u) ≤ 0.01 / Real.log u := by
  generalize hcdef : (5 / 12 - 1 / 50 : ℝ) = c
  have hu0 : 0 < u := lt_of_lt_of_le hX0 hu
  have hL : 10 ^ 8 ≤ Real.log u := hX.trans (Real.log_le_log hX0 hu)
  have hκ : u ^ (-c) ≤ X₀ ^ (-c) := Real.rpow_le_rpow_of_nonpos hX0 hu (by rw [← hcdef]; norm_num)
  have hpow : u ^ (-c) * u = Real.exp ((1 - c) * Real.log u) := by
    rw [Real.rpow_def_of_pos hu0, ← Real.exp_log hu0, ← Real.exp_add, Real.log_exp]
    ring_nf
  have hc : 1 / 2 ≤ 1 - c := by rw [← hcdef]; norm_num
  have hexp := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ (1 - c) * Real.log u)
  have hbig : 100 * Real.log u ≤ X₀ ^ (-c) * u := by
    have h1 : u ^ (-c) * u ≤ X₀ ^ (-c) * u := mul_le_mul_of_nonneg_right hκ hu0.le
    have hy : Real.log u / 2 ≤ (1 - c) * Real.log u := by nlinarith
    have hy2 : (Real.log u / 2) ^ 2 ≤ ((1 - c) * Real.log u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hy 2
    nlinarith
  have hL0 : 0 < Real.log u := by linarith
  rw [div_le_div_iff₀ (by positivity) hL0, show (0.01 : ℝ) = 1 / 100 by norm_num]
  linarith

/-- **Lemma 3.3**: `T'_cont(u) ≥ 0.08/log u > 0` for `u ≥ X₀`, with `κ = X₀^{-(5/12 - 1/50)}`. -/
theorem slope_pos {X₀ u rhoDet rhoA R' : ℝ} (hX0 : 0 < X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hu : X₀ ≤ u)
    (hdet : 0.99 / Real.log u - 1 / (X₀ ^ (-(5 / 12 - 1 / 50 : ℝ)) * u) ≤ 1 - rhoDet)
    (hR : |R'| ≤ 0.8 / Real.log u) :
    0 < 0.08 / Real.log u ∧
      0.08 / Real.log u ≤ 1 - rhoDet - min rhoA (0.1 / Real.log u) + R' := by
  have hL : 0 < Real.log u := by linarith [hX.trans (Real.log_le_log hX0 hu)]
  have h1 := positivity_margin (rhoA := rhoA) hL hdet hR
  have h2 := inv_kappa_mul_le hX0 hX hu
  have e : 0.08 / Real.log u = 0.09 / Real.log u - 0.01 / Real.log u := by
    field_simp; norm_num
  exact ⟨by positivity, by linarith⟩

end Positivity

end
