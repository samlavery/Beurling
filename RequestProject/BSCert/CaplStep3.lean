module

public import RequestProject.BSCert.CaplStep2
meta import RequestProject.BSCert.CaplStep2

/-!
# Step 3 of the proof of Theorem 6.23 (Dickman rows)

For `s > s_H + 1` and `ℓ ≤ 0.3Λ`, `caplw_check_independent.py` evaluates the Dickman-row
criterion
* `log D = ℓ - log Λ` (a lower bound for `log D`),
* `g/L = 0.9 (1 - e^{-log D}) log D / Λ`,
* `a = log(1/(3ℓ) + 4e^{-ℓ}) + ℓ + log(2e^ℓ/Λ + 1)` (an upper bound for `log(r₀(D+1))`),
* `1 + j ≥ (log c - 1)/(2a) - 1/2`,

and checks `(1 + j) · g/L ≥ 1 + 10⁻³`. We prove this for all `Λ ≥ 10⁸`, `s > s_H + 1` and
`ℓ ≤ 0.3Λ`, as in the paper (`a ≤ 3 log Λ + 2s - 3 ≤ 0.6Λ`).
-/

@[expose] public section

namespace BSCert.Capl

open Real Set

/-- The quantity `((log c - 1)/(2a) - 1/2) · g/L` of the Dickman-row check, for `log c = X`. -/
noncomputable def step3Ratio (X Λ s : ℝ) : ℝ :=
  let ℓ := 2 * Real.log Λ + s
  let logD := ℓ - Real.log Λ
  let gL := 0.9 * (1 - Real.exp (-logD)) * logD / Λ
  let a := Real.log (1 / (3 * ℓ) + 4 * Real.exp (-ℓ)) + ℓ + Real.log (2 * Real.exp ℓ / Λ + 1)
  ((X - 1) / (2 * a) - 0.5) * gL

set_option maxHeartbeats 1000000 in
/-- **Step 3 of the proof of Theorem 6.23** (checked at random points by
`caplw_check_independent.py`): for `Λ ≥ 10⁸`, `s > s_H + 1` and `ℓ = 2 log Λ + s ≤ 0.3Λ`,
the Dickman-row criterion `(1 + j) · g/L ≥ 1.001` holds with `log c = max(4ℓ² - log 4, γ(s)Λ)`. -/
theorem step3 {sH Λ s : ℝ} (hsH : 5.9745 ≤ sH) (hΛ : 100000000 ≤ Λ) (hs : sH + 1 < s)
    (hl : 2 * Real.log Λ + s ≤ 0.3 * Λ) : 1.001 ≤ step3Ratio (logc sH Λ s) Λ s := by
  have hΛ0 : 0 < Λ := by linarith
  have hx : 18.42 ≤ Real.log Λ := le_trans log1e8_bounds.1 (Real.log_le_log (by norm_num) hΛ)
  set x := Real.log Λ with hxdef
  set ℓ := 2 * x + s with hℓ
  have hs7 : 6.9745 ≤ s := by linarith
  have hl44 : 43.8 ≤ ℓ := by linarith
  -- `log c ≥ 7.5 Λ`
  have hX : 7.5 * Λ ≤ logc sH Λ s := by
    have : gam sH s = 7.5 := by
      unfold gam; rw [if_neg (by linarith), if_neg (by linarith)]
    unfold logc; rw [this]; exact le_max_right _ _
  set X := logc sH Λ s
  -- `e^ℓ/Λ = Λ eˢ ≥ 1`, and `e^ℓ ≥ 12ℓ`
  have heℓ : Real.exp ℓ = Λ * Λ * Real.exp s := by
    rw [hℓ, exp_two_log_add hΛ0]; ring
  have hes : 1 ≤ Real.exp s := Real.one_le_exp (by linarith)
  have hratio1 : Λ ≤ Real.exp ℓ / Λ := by
    rw [le_div_iff₀ hΛ0, heℓ]; nlinarith
  have hsq : ℓ ^ 2 / 2 ≤ Real.exp ℓ := by
    have h := Real.sum_le_exp_of_nonneg (x := ℓ) (by linarith) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have h12 : 12 * ℓ ≤ Real.exp ℓ := by nlinarith
  -- the three pieces of `a`
  have hT1 : Real.log (1 / (3 * ℓ) + 4 * Real.exp (-ℓ)) ≤ Real.log 2 - Real.log 3 - Real.log ℓ := by
    have h4 : 4 * Real.exp (-ℓ) ≤ 1 / (3 * ℓ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      linarith
    have hpos : 0 < 1 / (3 * ℓ) + 4 * Real.exp (-ℓ) := by positivity
    calc Real.log (1 / (3 * ℓ) + 4 * Real.exp (-ℓ)) ≤ Real.log (2 / (3 * ℓ)) :=
          Real.log_le_log hpos (by
            have : 2 / (3 * ℓ) = 1 / (3 * ℓ) + 1 / (3 * ℓ) := by ring
            linarith)
      _ = Real.log 2 - Real.log 3 - Real.log ℓ := by
          rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) (by linarith)]
          ring
  have hT1' : Real.log (1 / (3 * ℓ)) ≤ Real.log (1 / (3 * ℓ) + 4 * Real.exp (-ℓ)) :=
    Real.log_le_log (by positivity) (by have := Real.exp_pos (-ℓ); linarith)
  have hT3 : Real.log (2 * Real.exp ℓ / Λ + 1) ≤ Real.log 3 + ℓ - x := by
    have hq : 2 * Real.exp ℓ / Λ + 1 ≤ 3 * (Real.exp ℓ / Λ) := by
      have : 1 ≤ Real.exp ℓ / Λ := le_trans (by linarith) hratio1
      rw [mul_div_assoc]; linarith
    calc Real.log (2 * Real.exp ℓ / Λ + 1) ≤ Real.log (3 * (Real.exp ℓ / Λ)) :=
          Real.log_le_log (by positivity) hq
      _ = Real.log 3 + ℓ - x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (Real.exp_pos _).ne'
            hΛ0.ne', Real.log_exp]; ring
  have hT3' : 0 ≤ Real.log (2 * Real.exp ℓ / Λ + 1) := Real.log_nonneg (by
    have : 0 ≤ 2 * Real.exp ℓ / Λ := by positivity
    linarith)
  set a := Real.log (1 / (3 * ℓ) + 4 * Real.exp (-ℓ)) + ℓ + Real.log (2 * Real.exp ℓ / Λ + 1)
    with ha
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlogl : 3.68 ≤ Real.log ℓ := by
    have : Real.log 40 ≤ Real.log ℓ := Real.log_le_log (by norm_num) (by linarith)
    have h40 : (3.68 : ℝ) ≤ Real.log 40 := by
      have h := FX.logLoQF_le (a := 40) (by norm_num)
      have hc : (368 / 100 : ℚ) ≤ FX.logLoQF 40 := by decide +kernel
      have hc' : ((368 / 100 : ℚ) : ℝ) ≤ ((FX.logLoQF 40 : ℚ) : ℝ) := by exact_mod_cast hc
      push_cast at h hc'; linarith
    linarith
  have hapos : 0 < a := by
    have h1 : Real.log (1 / (3 * ℓ)) = -(Real.log 3 + Real.log ℓ) := by
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (by linarith)]
    have htan : Real.log ℓ ≤ ℓ / 40 + Real.log 40 - 1 := by
      have := Real.log_le_sub_one_of_pos (x := ℓ / 40) (by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at this; linarith
    have := log40_le
    have h3 : Real.log 3 ≤ 1.2 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this; linarith
    rw [ha]; linarith
  have hau : a ≤ 3 * x + 2 * s - 2.9 := by rw [ha]; linarith
  have ha06 : a ≤ 0.6 * Λ := by linarith
  -- `1 + j`
  have hj : 6.89 * Λ / (2 * a) ≤ (X - 1) / (2 * a) - 0.5 := by
    have e : (X - 1) / (2 * a) - 0.5 = (X - 1 - a) / (2 * a) := by field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  -- `g/L`
  have hD : ℓ - x = x + s := by rw [hℓ]; ring
  have hδ : Real.exp (-(ℓ - x)) ≤ 0.001 := by
    rw [hD, Real.exp_neg]
    have : 1000 ≤ Real.exp (x + s) := by
      rw [Real.exp_add, hxdef, Real.exp_log hΛ0]; nlinarith
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; linarith
  have hg : 0.9 * 0.999 * (x + s) / Λ ≤ 0.9 * (1 - Real.exp (-(ℓ - x))) * (ℓ - x) / Λ := by
    rw [hD] at hδ ⊢
    apply div_le_div_of_nonneg_right _ hΛ0.le
    have : 0 ≤ x + s := by linarith
    nlinarith
  -- combine
  show 1.001 ≤ ((X - 1) / (2 * a) - 0.5) * (0.9 * (1 - Real.exp (-(ℓ - x))) * (ℓ - x) / Λ)
  have hprod := mul_le_mul hj hg (by positivity) (le_trans (by positivity) hj)
  refine le_trans ?_ hprod
  have e : 6.89 * Λ / (2 * a) * (0.9 * 0.999 * (x + s) / Λ) = 6.89 * 0.9 * 0.999 / 2 * ((x + s) / a) := by
    field_simp
  rw [e]
  have : (x + s) / a ≥ 1 / 3 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hapos]; linarith
  nlinarith

end BSCert.Capl
