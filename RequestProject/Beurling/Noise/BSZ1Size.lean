module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Region Z1 of Theorem 5.6: sizes of the parameters

Standing assumptions `τ ≥ 10⁸` and `ℓ > 30τ` (Step 7(i)). We record:

* `ℓ > 3·10⁹`, `κ_Φ/ℓ ≤ 0.13334`, `w₁ ≥ 0.9`, `w₁ < 1`;
* `μ₀ ≤ log(1/w₁) ≤ 2.0345 (τ + log 2)/ℓ` (`log_inv_w1_le`);
* `u₀ = ℓ^{1/4} ≥ 234`, `u₀ ≤ U(ℓ)`;
* the size of the junction: `(1 + U)² log(3 + U) ≤ 0.0145 ℓ` and `U ≤ 0.036 √ℓ`
  (`U_size`, `U_le_sqrt`); these replace the paper's "slope of `D` at most `0.25`" and are
  uniform in `ℓ`.
-/

@[expose] public section

open Real

namespace BSaias

namespace Z1

variable {τ ℓ : ℝ}

lemma ell_gt (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 3000000000 < ℓ := by linarith

lemma ell_pos (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 0 < ℓ := by linarith

lemma kappa_div_le (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : kappa τ / ℓ ≤ 0.13334 := by
  unfold kappa
  rw [div_le_iff₀ (ell_pos hτ hℓ)]
  nlinarith

lemma kappa_div_nonneg (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 0 ≤ kappa τ / ℓ := by
  unfold kappa; have := ell_pos hτ hℓ; positivity

lemma log_two_bounds : 0.6931471 < Real.log 2 ∧ Real.log 2 < 0.6931472 := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `x = (τ + log 2)/ℓ ≤ 0.03334`. -/
lemma x_le (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : (τ + Real.log 2) / ℓ ≤ 0.03334 := by
  have := log_two_bounds
  rw [div_le_iff₀ (ell_pos hτ hℓ)]; nlinarith

lemma w1_eq (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) :
    w1 τ ℓ = (1 - (τ + Real.log 2) / ℓ) / (1 + (τ + Real.log 2) / ℓ) := by
  have := ell_pos hτ hℓ
  unfold w1; field_simp; ring

lemma w1_ge (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 0.9 ≤ w1 τ ℓ := by
  rw [w1_eq hτ hℓ]
  have hx := x_le hτ hℓ
  have hx0 : 0 ≤ (τ + Real.log 2) / ℓ := by
    have := log_two_bounds; have := ell_pos hτ hℓ; apply div_nonneg <;> linarith
  rw [le_div_iff₀ (by linarith)]; linarith

lemma w1_lt_one (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : w1 τ ℓ < 1 := by
  rw [w1_eq hτ hℓ]
  have hx0 : 0 < (τ + Real.log 2) / ℓ := by
    have := log_two_bounds; have := ell_pos hτ hℓ; apply div_pos <;> linarith
  rw [div_lt_one (by linarith)]; linarith

/-- `log(1/w₁) ≤ 2.0345 (τ + log 2)/ℓ`. -/
lemma log_inv_w1_le (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) :
    Real.log (1 / w1 τ ℓ) ≤ 2.0345 * ((τ + Real.log 2) / ℓ) := by
  set x := (τ + Real.log 2) / ℓ with hxdef
  have hx := x_le hτ hℓ
  have hx0 : 0 < x := by
    have := log_two_bounds; have := ell_pos hτ hℓ; apply div_pos <;> linarith
  have e : 1 / w1 τ ℓ = (1 + x) / (1 - x) := by
    rw [w1_eq hτ hℓ, one_div_div]
  rw [e, Real.log_div (by linarith) (by linarith)]
  have h1 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith); linarith
  have h2 : 1 - 1 / (1 - x) ≤ Real.log (1 - x) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - x by linarith)
    simpa [one_div] using this
  have h3 : 1 / (1 - x) ≤ 1 + 1.0345 * x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-! ## `u₀ = ℓ^{1/4}` -/

lemma u0_nonneg (ℓ : ℝ) : 0 ≤ u0 ℓ := Real.sqrt_nonneg _

lemma u0_sq (ℓ : ℝ) : u0 ℓ ^ 2 = √ℓ := by
  show (√(√ℓ)) ^ 2 = √ℓ
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma u0_pow4 (hℓ : 0 ≤ ℓ) : u0 ℓ ^ 4 = ℓ := by
  have : u0 ℓ ^ 4 = (u0 ℓ ^ 2) ^ 2 := by ring
  rw [this, u0_sq ℓ, Real.sq_sqrt hℓ]

lemma u0_ge (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 234 ≤ u0 ℓ := by
  have h4 := u0_pow4 (ell_pos hτ hℓ).le
  have hl := ell_gt hτ hℓ
  by_contra h
  push_neg at h
  have : u0 ℓ ^ 4 < 234 ^ 4 := pow_lt_pow_left₀ h (u0_nonneg ℓ) (by norm_num)
  norm_num at this; linarith

lemma sqrt_term_nonneg (τ ℓ : ℝ) : 0 ≤ √(2 * Real.log (ℓ / τ) + 4) := Real.sqrt_nonneg _

lemma u0_le_U (τ ℓ : ℝ) : u0 ℓ ≤ Uf τ ℓ := by
  unfold Uf
  have := mul_nonneg (u0_nonneg ℓ) (sqrt_term_nonneg τ ℓ)
  linarith

/-- `log v ≤ v/40` for `v ≥ 234`. -/
lemma log_le_div40 {v : ℝ} (hv : 234 ≤ v) : Real.log v ≤ v / 40 := by
  have h1 : Real.log (v / 234) ≤ v / 234 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  have h2 : Real.log 234 ≤ 8 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have := log_two_bounds
  linarith

/-- The size of the junction (uniform in `ℓ`): `(1 + U)² log(3 + U) ≤ 0.0145 ℓ` and
`U ≤ 0.036 √ℓ`. -/
lemma U_size_both (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) :
    (1 + Uf τ ℓ) ^ 2 * Real.log (3 + Uf τ ℓ) ≤ 0.0145 * ℓ ∧ Uf τ ℓ ≤ 0.036 * √ℓ := by
  have hℓ0 := ell_pos hτ hℓ
  set v := u0 ℓ with hv
  have hv234 : 234 ≤ v := u0_ge hτ hℓ
  set s := √(2 * Real.log (ℓ / τ) + 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- `s² ≤ 8 log v + 4 ≤ 0.22 v`
  have hlogℓ : Real.log (ℓ / τ) ≤ 4 * Real.log v := by
    have h4 : Real.log ℓ = 4 * Real.log v := by
      rw [← u0_pow4 hℓ0.le, Real.log_pow]; push_cast; ring
    rw [← h4]
    exact Real.log_le_log (by positivity) (div_le_self hℓ0.le (by linarith))
  have hs2 : s ^ 2 ≤ 0.22 * v := by
    rw [hs]
    have hlv := log_le_div40 hv234
    have hpos : 0 ≤ 2 * Real.log (ℓ / τ) + 4 ∨ 2 * Real.log (ℓ / τ) + 4 < 0 := le_or_gt _ _
    rcases hpos with hp | hp
    · rw [Real.sq_sqrt hp]; nlinarith
    · rw [Real.sqrt_eq_zero'.mpr hp.le]; nlinarith
  set t := √v with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t ^ 2 = v := Real.sq_sqrt (by linarith)
  have ht15 : 15.29 ≤ t := by nlinarith
  have hst : s ≤ 0.47 * t := by
    by_contra hc; push_neg at hc
    have : (0.47 * t) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    nlinarith
  have hU : Uf τ ℓ = v + v * s := rfl
  have hUle : 1 + Uf τ ℓ ≤ 0.537 * t ^ 3 := by
    rw [hU, ← htt]; nlinarith
  have hU0 : 0 ≤ Uf τ ℓ := by rw [hU]; positivity
  have hℓt : ℓ = t ^ 8 := by
    rw [← u0_pow4 hℓ0.le, ← hv, ← htt]; ring
  have hsqℓ : √ℓ = t ^ 4 := by
    rw [← u0_sq ℓ, ← hv, ← htt]; ring
  constructor
  · have hlog : Real.log (3 + Uf τ ℓ) ≤ t ^ 2 / 20 := by
      have h1 : 3 + Uf τ ℓ ≤ v ^ 2 := by rw [← htt]; nlinarith
      have h2 : Real.log (3 + Uf τ ℓ) ≤ Real.log (v ^ 2) := Real.log_le_log (by linarith) h1
      rw [Real.log_pow] at h2
      have := log_le_div40 hv234
      rw [htt]; push_cast at h2; linarith
    have hlog0 : 0 ≤ Real.log (3 + Uf τ ℓ) := Real.log_nonneg (by linarith)
    have hsq : (1 + Uf τ ℓ) ^ 2 ≤ (0.537 * t ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hUle 2
    calc (1 + Uf τ ℓ) ^ 2 * Real.log (3 + Uf τ ℓ) ≤ (0.537 * t ^ 3) ^ 2 * (t ^ 2 / 20) :=
          mul_le_mul hsq hlog hlog0 (by positivity)
      _ ≤ 0.0145 * ℓ := by rw [hℓt]; nlinarith [pow_nonneg ht0 8]
  · rw [hsqℓ]
    have : Uf τ ℓ ≤ 0.537 * t ^ 3 := by linarith
    nlinarith [pow_nonneg ht0 3]

end Z1

end BSaias

end
