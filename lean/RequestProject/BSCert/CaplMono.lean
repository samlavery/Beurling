module

public import RequestProject.BSCert.CaplRaise

/-!
# Monotonicity of `γ`, `c` and `M̄₁` in the capacity parameter `s` (Theorem 6.23(c))

Theorem 6.23(c) of the paper states that `c(z)`, `M̄₁(z)` and `H(z)` are non-decreasing in the
height `z`. The argument (Steps 1 and 6 of its proof) is:

* **Step 1.** At fixed `s`, `G(Λ, s)` is non-increasing in `Λ` on the admissible range
  (`G_anti_lam`); at fixed `Λ` it is non-decreasing in `s`, since `e^{s/2}` and `A` increase
  with `s` (`G_mono_s`). As `Λ_s = max(10⁸, e^{-s})` is non-increasing in `s`, `γ*(s) = 1.3 G(Λ_s, s)`
  is non-decreasing (`gstar_mono`).
* **Step 6.** `γ` is continuous at the break points `s_H`, `s_H + 1` and non-decreasing
  (`gam_monotone`); hence `log c = max(4ℓ² - log 4, γ(s) Λ)`, `r̄₀ = e^ℓ/(3ℓ) + 4` and
  `M̄₁ = r̄₀ + φ(r̄₀) + 1` are non-decreasing in `s` (`logc_mono`, `rbar0_mono`, `Mbar1_mono`).

All statements are on the admissible range `ℓ = 2 log Λ + s ≥ log Λ`, `Λ ≥ 10⁸` (that is,
`z ≥ X₀`), and below `s ≤ 6` for the pieces of `γ*` (used only for `s ≤ s_H < 6`).
-/

@[expose] public section

namespace BSCert.Capl

open Real

/-- `log Λ ≥ 18` for `Λ ≥ 10⁸`. -/
lemma log_ge_18 {Λ : ℝ} (hΛ : 100000000 ≤ Λ) : 18 ≤ Real.log Λ := by
  have h : Real.exp 18 ≤ 100000000 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 18 ≤ 2.7182818286 ^ 18 := by gcongr
      _ ≤ 100000000 := by norm_num
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- `3 log Λ + 14 < Λ` for `Λ ≥ 10⁸`. -/
lemma lin_log_lt {Λ : ℝ} (hΛ : 100000000 ≤ Λ) : 3 * Real.log Λ + 14 < Λ := by
  have h := Real.log_le_rpow_div (x := Λ) (ε := 1/2) (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have hs : 10000 ≤ Real.sqrt Λ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsq : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt (by linarith)
  nlinarith

/-- `log w ≤ w/8 + 1.08` (tangent line at `w = 8`). -/
lemma log_le_eighth {w : ℝ} (hw : 0 < w) : Real.log w ≤ w / 8 + 1.08 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < w / 8 by positivity)
  rw [Real.log_div hw.ne' (by norm_num)] at h1
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

/-- `A ≥ 6` on the admissible range `s ≥ -log Λ`, `Λ ≥ 10⁸`. -/
lemma A_ge_six {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) : 6 ≤ A Λ s := by
  have hL := log_ge_18 hΛ
  have hl : 0 < 2 * Real.log Λ + s := by linarith
  rw [A_eq (by linarith) hl]
  have := log_le_eighth hl
  have := Real.log_two_gt_d9
  linarith

/-- `A ≤ 3 log Λ + 13` for `-log Λ ≤ s ≤ 6`. -/
lemma A_le_lin {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs6 : s ≤ 6) :
    A Λ s ≤ 3 * Real.log Λ + 13 := by
  have hL := log_ge_18 hΛ
  have hl : 0 < 2 * Real.log Λ + s := by linarith
  rw [A_eq (by linarith) hl]
  have : 0 ≤ Real.log (2 * Real.log Λ + s) := Real.log_nonneg (by linarith)
  have := Real.log_two_lt_d9
  linarith

/-- `G = 2 √(A(A+1) e^s / (Λ - A - 1))` when `A ≥ 0` and `Λ - A - 1 > 0`. -/
lemma G_eq_sqrt {Λ s : ℝ} (hA : 0 ≤ A Λ s) (hD : 0 < Λ - A Λ s - 1) :
    G Λ s = 2 * Real.sqrt (A Λ s * (A Λ s + 1) * Real.exp s / (Λ - A Λ s - 1)) := by
  unfold G
  rw [Real.sqrt_div' _ hD.le, Real.sqrt_mul (by positivity : 0 ≤ A Λ s * (A Λ s + 1)),
    Real.exp_half]
  ring

/-- **`G` is non-decreasing in `s` at fixed `Λ`** (proof of Theorem 6.23, Step 1): `A` and
`e^{s/2}` increase with `s`, and `Λ - A - 1` decreases. -/
lemma G_mono_s {Λ s t : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hst : s ≤ t)
    (ht : t ≤ 6) : G Λ s ≤ G Λ t := by
  have hL := log_ge_18 hΛ
  have hls : 0 < 2 * Real.log Λ + s := by linarith
  have hlt : 0 < 2 * Real.log Λ + t := by linarith
  have hAs := A_ge_six hΛ hs
  have hAt' := A_le_lin hΛ (hs.trans hst) ht
  have hlin := lin_log_lt hΛ
  have hmono : A Λ s ≤ A Λ t := by
    rw [A_eq (by linarith) hls, A_eq (by linarith) hlt]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hlt hls)
    rw [Real.log_div hlt.ne' hls.ne'] at h1
    have h2 : (2 * Real.log Λ + t) / (2 * Real.log Λ + s) - 1 ≤ t - s := by
      rw [div_sub_one hls.ne', div_le_iff₀ hls]; nlinarith
    linarith
  have hDt : 0 < Λ - A Λ t - 1 := by linarith
  have hDs : 0 < Λ - A Λ s - 1 := by linarith
  rw [G_eq_sqrt (by linarith) hDs, G_eq_sqrt (by linarith) hDt]
  gcongr 2 * ?_
  apply Real.sqrt_le_sqrt
  have hAt0 : 0 ≤ A Λ t * (A Λ t + 1) := by nlinarith
  apply div_le_div₀ (mul_nonneg hAt0 (Real.exp_pos _).le) _ hDt (by linarith)
  have : A Λ s * (A Λ s + 1) ≤ A Λ t * (A Λ t + 1) := by nlinarith
  exact mul_le_mul this (Real.exp_le_exp.mpr hst) (Real.exp_pos _).le hAt0

/-- **`G` is non-increasing in `Λ` at fixed `s`** (proof of Theorem 6.23, Step 1). With
`r = Λ'/Λ = e^u`: `A(Λ') ≤ A(Λ) + 3u`, so `Λ' - A(Λ') - 1 ≥ r (Λ - A(Λ) - 1)` and
`A(Λ')(A(Λ') + 1) ≤ r A(Λ)(A(Λ) + 1)` (as `A(Λ) ≥ 6` and `r ≥ 1 + u + u²/2`). -/
lemma G_anti_lam {Λ Λ' s : ℝ} (hΛ : 100000000 ≤ Λ) (hΛΛ : Λ ≤ Λ') (hs : -Real.log Λ ≤ s)
    (hs6 : s ≤ 6) : G Λ' s ≤ G Λ s := by
  have hL := log_ge_18 hΛ
  have hΛ' : 100000000 ≤ Λ' := hΛ.trans hΛΛ
  have hLL : Real.log Λ ≤ Real.log Λ' := Real.log_le_log (by linarith) hΛΛ
  have hs' : -Real.log Λ' ≤ s := by linarith
  set u := Real.log Λ' - Real.log Λ with hu
  have hu0 : 0 ≤ u := by linarith
  set r := Λ' / Λ with hr
  have hru : r = Real.exp u := by
    rw [hu, ← Real.log_div (by linarith) (by linarith), Real.exp_log (by positivity)]
  have hl : 0 < 2 * Real.log Λ + s := by linarith
  have hl' : 0 < 2 * Real.log Λ' + s := by linarith
  set a := A Λ s
  set a' := A Λ' s
  have ha := A_ge_six hΛ hs
  have ha' := A_ge_six hΛ' hs'
  have haup := A_le_lin hΛ hs hs6
  have haa : a' ≤ a + 3 * u := by
    have e1 : a = _ := A_eq (by linarith) hl
    have e2 : a' = _ := A_eq (by linarith) hl'
    have : Real.log (2 * Real.log Λ + s) ≤ Real.log (2 * Real.log Λ' + s) :=
      Real.log_le_log hl (by linarith)
    rw [e1, e2]; linarith
  have hr1 : 1 + u + u ^ 2 / 2 ≤ r := hru ▸ Real.quadratic_le_exp_of_nonneg hu0
  have hlin := lin_log_lt hΛ
  have hD : 0 < Λ - a - 1 := by linarith
  have hΛpos : 0 < Λ := by linarith
  have hD' : r * (Λ - a - 1) ≤ Λ' - a' - 1 := by
    have : r * Λ = Λ' := by rw [hr]; field_simp
    nlinarith
  have hrpos : 0 < r := by rw [hru]; exact Real.exp_pos _
  have hD'pos : 0 < Λ' - a' - 1 := lt_of_lt_of_le (by positivity) hD'
  have hN : a' * (a' + 1) ≤ r * (a * (a + 1)) := by
    have h1 : a' * (a' + 1) ≤ (a + 3 * u) * (a + 3 * u + 1) := by nlinarith
    have h2 : (a + 3 * u) * (a + 3 * u + 1) ≤ (1 + u + u ^ 2 / 2) * (a * (a + 1)) := by
      have h1 : 0 ≤ a * a - 5 * a - 3 := by nlinarith
      have h2 : 0 ≤ (a * a + a) / 2 - 9 := by nlinarith
      nlinarith [mul_nonneg hu0 h1, mul_nonneg (mul_nonneg hu0 hu0) h2]
    have h3 : (1 + u + u ^ 2 / 2) * (a * (a + 1)) ≤ r * (a * (a + 1)) :=
      mul_le_mul_of_nonneg_right hr1 (by positivity)
    linarith
  rw [G_eq_sqrt (by linarith) hD, G_eq_sqrt (by linarith) hD'pos]
  gcongr 2 * ?_
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hD'pos hD]
  have he := Real.exp_pos s
  calc a' * (a' + 1) * Real.exp s * (Λ - a - 1)
      ≤ r * (a * (a + 1)) * Real.exp s * (Λ - a - 1) := by gcongr
    _ = a * (a + 1) * Real.exp s * (r * (Λ - a - 1)) := by ring
    _ ≤ a * (a + 1) * Real.exp s * (Λ' - a' - 1) := by gcongr

lemma LamS_ge (s : ℝ) : 100000000 ≤ LamS s := le_max_left _ _

lemma neg_log_LamS_le (s : ℝ) : -Real.log (LamS s) ≤ s := by
  have : Real.log (Real.exp (-s)) ≤ Real.log (LamS s) :=
    Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  rw [Real.log_exp] at this; linarith

lemma LamS_anti {s t : ℝ} (hst : s ≤ t) : LamS t ≤ LamS s :=
  max_le_max le_rfl (Real.exp_le_exp.mpr (by linarith))

/-- **`γ*` is non-decreasing** on `(-∞, 6]` (proof of Theorem 6.23, Step 1). -/
theorem gstar_mono {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 6) : gstar s ≤ gstar t := by
  unfold gstar
  have h1 := G_mono_s (LamS_ge s) (neg_log_LamS_le s) hst ht
  have h2 := G_anti_lam (LamS_ge t) (LamS_anti hst) (neg_log_LamS_le t) ht
  linarith

/-- **`γ` is non-decreasing** (proof of Theorem 6.23, Step 6), for a break point `s_H ≤ 6` with
`γ*(s_H) ≤ 7.5`. -/
theorem gam_monotone {sH : ℝ} (hsH : sH ≤ 6) (hg : gstar sH ≤ 7.5) : Monotone (gam sH) := by
  intro s t hst
  unfold gam
  by_cases hs : s ≤ sH
  · rw [if_pos hs]
    have hs' := gstar_mono hs hsH
    by_cases ht : t ≤ sH
    · rw [if_pos ht]; exact gstar_mono hst (ht.trans hsH)
    · rw [if_neg ht]
      push_neg at ht
      split_ifs with ht1
      · nlinarith
      · linarith
  · rw [if_neg hs]
    push_neg at hs
    have ht : ¬ t ≤ sH := by push_neg; linarith
    rw [if_neg ht]
    split_ifs with hs1 ht1 ht1
    · nlinarith
    · nlinarith
    · linarith
    · exact le_rfl

/-- `log c = max(4ℓ² - log 4, γ(s) Λ)` is non-decreasing in `s` on `ℓ ≥ 0`. -/
theorem logc_mono {sH Λ s t : ℝ} (hsH : sH ≤ 6) (hg : gstar sH ≤ 7.5) (hΛ : 0 ≤ Λ)
    (hl : 0 ≤ 2 * Real.log Λ + s) (hst : s ≤ t) : logc sH Λ s ≤ logc sH Λ t := by
  unfold logc
  apply max_le_max
  · have : (2 * Real.log Λ + s) ^ 2 ≤ (2 * Real.log Λ + t) ^ 2 := by nlinarith
    linarith
  · exact mul_le_mul_of_nonneg_right (gam_monotone hsH hg hst) hΛ

/-- `e^a/(3a) ≤ e^b/(3b)` for `1 ≤ a ≤ b`. -/
lemma exp_div_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.exp a / (3 * a) ≤ Real.exp b / (3 * b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (b - a)
  have hea := Real.exp_pos a
  rw [h1]
  have : b ≤ a * Real.exp (b - a) := by nlinarith
  nlinarith

/-- `r̄₀ = e^ℓ/(3ℓ) + 4` is non-decreasing in `s` on `ℓ ≥ 1`. -/
theorem rbar0_mono {Λ s t : ℝ} (hl : 1 ≤ 2 * Real.log Λ + s) (hst : s ≤ t) :
    rbar0 Λ s ≤ rbar0 Λ t := by
  unfold rbar0
  linarith [exp_div_mono hl (by linarith : 2 * Real.log Λ + s ≤ 2 * Real.log Λ + t)]

lemma rbar0_nonneg {Λ s : ℝ} (hl : 1 ≤ 2 * Real.log Λ + s) : 0 ≤ rbar0 Λ s := by
  unfold rbar0
  have : 0 < 2 * Real.log Λ + s := by linarith
  positivity

/-- **`M̄₁` is non-decreasing in `s`** (Theorem 6.23(c)) on `ℓ = 2 log Λ + s ≥ 1`, `Λ ≥ 0`, for a
break point `s_H ≤ 6` with `γ*(s_H) ≤ 7.5`. -/
theorem Mbar1_mono {sH Λ s t : ℝ} (hsH : sH ≤ 6) (hg : gstar sH ≤ 7.5) (hΛ : 0 ≤ Λ)
    (hl : 1 ≤ 2 * Real.log Λ + s) (hst : s ≤ t) : Mbar1 sH Λ s ≤ Mbar1 sH Λ t := by
  unfold Mbar1
  simp only
  have hc : Real.exp (logc sH Λ s) ≤ Real.exp (logc sH Λ t) :=
    Real.exp_le_exp.mpr (logc_mono hsH hg hΛ (by linarith) hst)
  have hr := rbar0_mono hl hst
  have hr0 := rbar0_nonneg hl
  have hsq := Real.sqrt_le_sqrt hc
  have hc0 := Real.exp_pos (logc sH Λ s)
  have hq0 := Real.sqrt_nonneg (Real.exp (logc sH Λ s))
  have h1 : rbar0 Λ s * Real.sqrt (Real.exp (logc sH Λ s)) ≤
      rbar0 Λ t * Real.sqrt (Real.exp (logc sH Λ t)) := mul_le_mul hr hsq hq0 (by linarith)
  have h2 : rbar0 Λ s * (rbar0 Λ s + 1) ≤ rbar0 Λ t * (rbar0 Λ t + 1) := by nlinarith
  linarith

end BSCert.Capl

end
