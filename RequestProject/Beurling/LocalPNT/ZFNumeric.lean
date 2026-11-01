module

public import Mathlib

/-!
# Step 7 of the proof of Theorem 5.24: the numerical contradiction

With `r = 6.8/Λ`, `κ_L = 3.79`, `X = L_t + 442 + 2 log Λ`, `Y = X + log X + 0.7` and
`η = 0.33769/(ΛY)`, the inequality obtained from (eq. lp-341), (eq. lp-pole) and Landau's lemma,

  `-512 ε ≤ 35 (1/η + 0.43 + 3e + 4ε) + 56 ((2/r) Q - 1/d + d/r²) + 37 (2/r) Q`,

with `log M_k ≤ Q ≤ L_t + log Λ + log(1/η) + 439`, `0 < d = 1 + η - β ≤ η(1 + 1/κ_L)`, `0 ≤ e ≤ 1`
and `εη ≤ 10^{-30}`, is impossible (`zf_contra`). Here `56 κ_L/(κ_L + 1) - 35 = 9.3090…` beats
`(2·93/6.8)·0.33769 = 9.2367…`.
-/

@[expose] public section

open Real

namespace LocalPNT

lemma log_033769_ge : -1.09 ≤ Real.log 0.33769 := by
  have h : Real.exp (-1.09) ≤ 0.33769 := by
    have h1 : (2.97 : ℝ) ≤ Real.exp 1.09 := by
      have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.09 by norm_num) 6
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have h2 : Real.exp (-1.09) * Real.exp 1.09 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1.09)]
  have := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at this

/-- `log Y ≤ log X + 1` for `Y = X + log X + 0.7`, `X ≥ 1`. -/
lemma log_Y_le {X : ℝ} (hX : 1 ≤ X) : Real.log (X + Real.log X + 0.7) ≤ Real.log X + 1 := by
  have hX0 : 0 < X := by linarith
  have hl : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hX0
  have hl0 : 0 ≤ Real.log X := Real.log_nonneg hX
  rw [← Real.log_exp 1, ← Real.log_mul hX0.ne' (Real.exp_pos 1).ne']
  apply Real.log_le_log (by positivity)
  have := Real.exp_one_gt_d9
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The numerical contradiction of Step 7.** -/
theorem zf_contra {Λ Lt η Q d e ε : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hLt : 0 ≤ Lt)
    (hη : η = 0.33769 / (Λ * (Lt + 442 + 2 * Real.log Λ +
      Real.log (Lt + 442 + 2 * Real.log Λ) + 0.7)))
    (hQ : Q ≤ Lt + Real.log Λ + Real.log (1 / η) + 439) (hd0 : 0 < d)
    (hd : d ≤ η * (1 + 1 / 3.79)) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hε : 0 ≤ ε)
    (hεη : ε * η ≤ (1 / 10 ^ 30 : ℝ))
    (hineq : -512 * ε ≤ 35 * (1 / η + 0.43 + 3 * e + 4 * ε) +
      56 * (2 / (6.8 / Λ) * Q - 1 / d + d / (6.8 / Λ) ^ 2) + 37 * (2 / (6.8 / Λ) * Q)) :
    False := by
  set X := Lt + 442 + 2 * Real.log Λ with hXdef
  set Y := X + Real.log X + 0.7 with hYdef
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hX : 442 ≤ X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hY : 442 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hΛη : Λ * η = 0.33769 / Y := by rw [hη]; field_simp
  have hηs : η ≤ (1 / 10 ^ 10 : ℝ) := by
    rw [hη, div_le_iff₀ (by positivity)]
    have : (1 / 10 ^ 10 : ℝ) * (Λ * Y) ≥ (1 / 10 ^ 10 : ℝ) * (10 ^ 8 * 442) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hΛ hY (by norm_num) hΛ0.le
    norm_num at this ⊢; linarith
  -- `Q ≤ Y`
  have hlog1η : Real.log (1 / η) = Real.log Λ + Real.log Y - Real.log 0.33769 := by
    rw [hη, one_div_div, Real.log_div (by positivity) (by norm_num),
      Real.log_mul hΛ0.ne' hY0.ne']
  have hlY := log_Y_le (X := X) (by linarith)
  rw [← hYdef] at hlY
  have hl33 := log_033769_ge
  have hQY : Q ≤ Y := by
    have : Q ≤ X - 1.91 + Real.log Y := by rw [hlog1η] at hQ; linarith
    linarith
  -- multiply the inequality by `η`
  have hmul := mul_le_mul_of_nonneg_left hineq hη0.le
  have e1 : η * (35 * (1 / η + 0.43 + 3 * e + 4 * ε) +
      56 * (2 / (6.8 / Λ) * Q - 1 / d + d / (6.8 / Λ) ^ 2) + 37 * (2 / (6.8 / Λ) * Q)) =
      35 + 35 * 0.43 * η + 105 * e * η + 140 * (ε * η) + 93 * 2 / 6.8 * (Λ * η) * Q -
        56 * (η / d) + 56 * (d * η) * Λ ^ 2 / 6.8 ^ 2 := by
    field_simp; ring
  rw [e1] at hmul
  have hηd : 3.79 / 4.79 ≤ η / d := by
    rw [le_div_iff₀ hd0]
    have := mul_le_mul_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 3.79 / 4.79)
    have e : η * (1 + 1 / 3.79) * (3.79 / 4.79) = η := by ring
    linarith
  have hdη : d * η * Λ ^ 2 ≤ 1.27 * (Λ * η) ^ 2 := by
    have : d * η ≤ 1.27 * η ^ 2 := by nlinarith
    nlinarith [sq_nonneg Λ]
  have hΛη2 : (Λ * η) ^ 2 ≤ (1 / 10 ^ 5 : ℝ) := by
    rw [hΛη, div_pow]
    rw [div_le_iff₀ (by positivity)]
    have : (442 : ℝ) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by norm_num) hY 2
    norm_num at this ⊢; linarith
  have hQterm : 93 * 2 / 6.8 * (Λ * η) * Q ≤ 93 * 2 / 6.8 * 0.33769 := by
    rw [hΛη]
    have hQ0 : Q / Y ≤ 1 := by rw [div_le_one hY0]; exact hQY
    have : 93 * 2 / 6.8 * (0.33769 / Y) * Q = 93 * 2 / 6.8 * 0.33769 * (Q / Y) := by ring
    rw [this]
    have h0 : (0 : ℝ) ≤ 93 * 2 / 6.8 * 0.33769 := by norm_num
    calc 93 * 2 / 6.8 * 0.33769 * (Q / Y) ≤ 93 * 2 / 6.8 * 0.33769 * 1 :=
          mul_le_mul_of_nonneg_left hQ0 h0
      _ = _ := by ring
  have hεη' : ε * η ≥ 0 := mul_nonneg hε hη0.le
  have hrhs1 : 105 * e * η ≤ 105 * (1 / 10 ^ 10 : ℝ) := by
    have : e * η ≤ 1 * (1 / 10 ^ 10 : ℝ) := mul_le_mul he1 hηs hη0.le (by norm_num)
    linarith
  have hA : 56 * (3.79 / 4.79) ≤ 56 * (η / d) := by linarith
  have hB : 56 * (d * η) * Λ ^ 2 / 6.8 ^ 2 ≤ 56 * 1.27 * (1 / 10 ^ 5 : ℝ) / 6.8 ^ 2 := by
    have : d * η * Λ ^ 2 ≤ 1.27 * (1 / 10 ^ 5 : ℝ) := by linarith [hdη, hΛη2]
    have e : 56 * (d * η) * Λ ^ 2 / 6.8 ^ 2 = 56 * (d * η * Λ ^ 2) / 6.8 ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 56)
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hC : 140 * (ε * η) ≤ 140 * (1 / 10 ^ 30 : ℝ) := by linarith
  have hD : 35 * 0.43 * η ≤ 35 * 0.43 * (1 / 10 ^ 10 : ℝ) := by linarith
  have hL : η * (-512 * ε) = -512 * (ε * η) := by ring
  rw [hL] at hmul
  linarith

/-- `log(A + B) ≤ log A + log B - 2.95` for `A ≥ 19.2`, `B ≥ e^{10}`. -/
lemma log_add_le {A B : ℝ} (hA : 19.2 ≤ A) (hB : Real.exp 10 ≤ B) :
    Real.log (A + B) ≤ Real.log A + Real.log B - 2.95 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hB
  have he10 : (10000 : ℝ) ≤ Real.exp 10 := by
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 10 by norm_num) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h3 : Real.exp 2.95 ≤ 19.11 := by
    have h1 : Real.exp 2.95 * Real.exp 0.05 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    have h2 : Real.exp 3 ≤ 20.0856 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
        _ ≤ 20.0856 := by norm_num
    have h5 : (1.05127 : ℝ) ≤ Real.exp 0.05 := by
      have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.05 by norm_num) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
    nlinarith [Real.exp_pos 2.95]
  rw [show Real.log A + Real.log B - 2.95 = Real.log (A * B / Real.exp 2.95) by
    rw [Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_mul hA0.ne' hB0.ne',
      Real.log_exp]]
  apply Real.log_le_log (by positivity)
  rw [le_div_iff₀ (Real.exp_pos _)]
  have hiA : 1 / A ≤ 1 / 19.2 := one_div_le_one_div_of_le (by norm_num) hA
  have hiB : 1 / B ≤ 1 / 10000 := one_div_le_one_div_of_le (by norm_num) (he10.trans hB)
  have key : Real.exp 2.95 * (1 / A + 1 / B) ≤ 1 := by
    have : 1 / A + 1 / B ≤ 1 / 19.2 + 1 / 10000 := by linarith
    calc Real.exp 2.95 * (1 / A + 1 / B) ≤ 19.11 * (1 / 19.2 + 1 / 10000) :=
          mul_le_mul h3 this (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have e : (A + B) * Real.exp 2.95 = A * B * (Real.exp 2.95 * (1 / A + 1 / B)) := by
    field_simp; ring
  rw [e]
  calc A * B * (Real.exp 2.95 * (1 / A + 1 / B)) ≤ A * B * 1 :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = A * B := by ring

end LocalPNT

end
