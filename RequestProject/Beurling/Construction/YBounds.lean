module

public import RequestProject.Beurling.AbsorbEmpty

/-!
# Bounds on the absorption threshold `y` (Theorem 6.23(b), Step 5)

For a height `x ≥ X₀` (`Λ = log X₀ ≥ 10⁸`) write `L = log x`, `ℓ = log L`, `s = ℓ - 2 log Λ` and
`K = log c = max(4ℓ² - log 4, γ(s) Λ)`. The threshold is `y(x) = H L₀ L⁶` (`absorbYAt`), with
`H = max(H_std, M̄₁²)` and `L₀ = max(L⁵, 48 M̄₁ L³/c'²)`, `c' = 0.15`.

* `log_two_absorbYAt_le`: `log 2y ≤ max(8ℓ², 2K + 1.39) + K + 9ℓ + 9.07`
  (from `M̄₁ ≤ 2c`). Hence `log 2y ≤ 3K + 9ℓ + 11.85` always, and `log 2y ≤ 12ℓ² + 9ℓ + 7.69` when
  `K = 4ℓ² - log 4` (the paper: `log y ≤ 3 log c + 9ℓ + 11.14`; `log 2y ≤ 12ℓ² + 9ℓ + 8`).
* `log_absorbYAt_ge`: `log y ≥ 8ℓ²`.
* `absorbYAt_mono`: `y` is non-decreasing on `[X₀, ∞)`.
* `two_absorbYAt_le_of_le_sH` (**Theorem 6.23(b), first case**): if `s ≤ s_H`, then `2y < X₀`.
-/

@[expose] public section

open Real Set BSCert.Capl CaplLink QueueMono InitialRange AbsorbEmpty

namespace Construction

/-- `log c` at the height `x`. -/
noncomputable def logcAt (X₀ x : ℝ) : ℝ := logc sHroot (Real.log X₀) (capS X₀ x)

lemma log4_bounds : 1.38 ≤ Real.log 4 ∧ Real.log 4 ≤ 1.39 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9]

lemma exp_837_ge : (4267 : ℝ) ≤ Real.exp 8.37 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  have h37 : (1.4384 : ℝ) ≤ Real.exp 0.37 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.37 by norm_num)
    nlinarith
  have e : Real.exp 8.37 = Real.exp 8 * Real.exp 0.37 := by rw [← Real.exp_add]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h1.le 8
  rw [e, h8]
  have : (2.7182818283 : ℝ) ^ 8 * 1.4384 ≥ 4267 := by norm_num
  have h0 : (0 : ℝ) ≤ 2.7182818283 ^ 8 := by positivity
  nlinarith

/-- The basic facts at a height `x ≥ X₀`. -/
lemma height_facts {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    0 < x ∧ 10 ^ 8 ≤ Real.log x ∧ 18 ≤ Real.log (Real.log x) ∧
      2 * Real.log (Real.log X₀) + capS X₀ x = Real.log (Real.log x) := by
  have hX1 := one_lt_of_logX hX0 hX
  obtain ⟨h1, h2, -⟩ := logs_of_ge hX0 hX hx
  refine ⟨by linarith, h1, ?_, ell_eq X₀ x⟩
  have := log_ge_18 (Λ := Real.log X₀) (by linarith)
  linarith

/-- `4ℓ² - log 4 ≤ K`. -/
lemma logcAt_ge {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    4 * Real.log (Real.log x) ^ 2 - Real.log 4 ≤ logcAt X₀ x := by
  obtain ⟨-, -, -, hell⟩ := height_facts hX0 hX hx
  unfold logcAt logc
  rw [hell]
  exact le_max_left _ _

/-- `M̄₁ ≤ 2c` at a height `x ≥ X₀`. -/
lemma capM1_le_two_exp {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capM1 X₀ x ≤ 2 * Real.exp (logcAt X₀ x) := by
  obtain ⟨-, -, h3, hell⟩ := height_facts hX0 hX hx
  unfold capM1 logcAt
  exact Mbar1_le (by rw [hell]; exact h3)

/-- **The upper bound for `log 2y`**: `log 2y ≤ max(8ℓ², 2K + 1.39) + K + 9ℓ + 9.07`. -/
theorem log_two_absorbYAt_le {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) :
    Real.log (2 * absorbYAt X₀ x) ≤ max (8 * Real.log (Real.log x) ^ 2)
      (2 * logcAt X₀ x + 1.39) + logcAt X₀ x + 9 * Real.log (Real.log x) + 9.07 := by
  obtain ⟨hx0, hL, hl, -⟩ := height_facts hX0 hX hx
  set L := Real.log x with hLdef
  set l := Real.log L with hldef
  set K := logcAt X₀ x with hK
  have hLpos : 0 < L := by linarith
  have hLl : L = Real.exp l := (Real.exp_log hLpos).symm
  have hM0 := capM1_pos hX0 hX hx
  have hM2 := capM1_le_two_exp hX0 hX hx
  have hKge := logcAt_ge hX0 hX hx
  rw [← hK] at hM2 hKge
  obtain ⟨hl4, hl4'⟩ := log4_bounds
  -- `H ≤ exp(max(8ℓ², 2K + 1.39))`
  have hH : capH X₀ x ≤ Real.exp (max (8 * l ^ 2) (2 * K + 1.39)) := by
    unfold capH
    rw [← hLdef, ← hldef]
    apply max_le
    · exact Real.exp_le_exp.mpr (le_max_left _ _)
    · calc capM1 X₀ x ^ 2 ≤ (2 * Real.exp K) ^ 2 := pow_le_pow_left₀ hM0.le hM2 2
        _ = Real.exp (2 * K + Real.log 4) := by
          rw [Real.exp_add, Real.exp_log (by norm_num), mul_pow, ← Real.exp_nat_mul]
          push_cast; ring
        _ ≤ _ := Real.exp_le_exp.mpr (le_trans (by linarith) (le_max_right _ _))
  -- `L₀ ≤ exp(K + 3ℓ + 8.37)`
  have hL0 : absorbL0 X₀ x ≤ Real.exp (K + 3 * l + 8.37) := by
    unfold absorbL0
    rw [← hLdef]
    have e3 : Real.exp (K + 3 * l + 8.37) = Real.exp K * L ^ 3 * Real.exp 8.37 := by
      rw [Real.exp_add, Real.exp_add, hLl, ← Real.exp_nat_mul]; push_cast; ring
    rw [e3]
    have hE := exp_837_ge
    have hK0 : 0 < Real.exp K := Real.exp_pos K
    have hL3 : 0 < L ^ 3 := by positivity
    apply max_le
    · -- `L² = e^{2ℓ} ≤ e^{4ℓ²}/4 ≤ e^K`
      have h2 : L ^ 2 ≤ Real.exp K := by
        rw [hLl, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        push_cast; nlinarith
      have : L ^ 5 = L ^ 2 * L ^ 3 := by ring
      rw [this]
      calc L ^ 2 * L ^ 3 ≤ Real.exp K * L ^ 3 := mul_le_mul_of_nonneg_right h2 hL3.le
        _ ≤ Real.exp K * L ^ 3 * Real.exp 8.37 :=
          le_mul_of_one_le_right (by positivity) (by linarith)
    · rw [div_le_iff₀ (by norm_num)]
      have hKL : 0 < Real.exp K * L ^ 3 := by positivity
      calc 48 * capM1 X₀ x * L ^ 3 ≤ 48 * (2 * Real.exp K) * L ^ 3 := by gcongr
        _ = (Real.exp K * L ^ 3) * 96 := by ring
        _ ≤ (Real.exp K * L ^ 3) * (Real.exp 8.37 * 0.15 ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hKL.le; nlinarith
        _ = Real.exp K * L ^ 3 * Real.exp 8.37 * 0.15 ^ 2 := by ring
  have hy : absorbYAt X₀ x ≤ Real.exp (max (8 * l ^ 2) (2 * K + 1.39) + K + 9 * l + 8.37) := by
    unfold absorbYAt
    rw [← hLdef]
    have e : Real.exp (max (8 * l ^ 2) (2 * K + 1.39) + K + 9 * l + 8.37) =
        Real.exp (max (8 * l ^ 2) (2 * K + 1.39)) * Real.exp (K + 3 * l + 8.37) * L ^ 6 := by
      rw [← Real.exp_add, hLl, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    rw [e]
    have hH0 : 0 ≤ capH X₀ x := le_trans (Real.exp_pos _).le (le_max_left _ _)
    have hL00 : 0 ≤ absorbL0 X₀ x := le_trans (by positivity) (le_max_left _ _)
    have := mul_le_mul hH hL0 hL00 (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hy0 : 0 < absorbYAt X₀ x := by
    unfold absorbYAt absorbL0 capH
    have : 0 < max (Real.exp (8 * Real.log (Real.log x) ^ 2)) (capM1 X₀ x ^ 2) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
    have : 0 < max (Real.log x ^ 5) (48 * capM1 X₀ x * Real.log x ^ 3 / 0.15 ^ 2) :=
      lt_of_lt_of_le (by positivity) (le_max_left _ _)
    positivity
  rw [Real.log_mul (by norm_num) hy0.ne']
  have h1 := Real.log_le_log hy0 hy
  rw [Real.log_exp] at h1
  have h2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  linarith

/-- `y ≥ H_std = e^{8ℓ²}` (from `H ≥ H_std`, `L₀ ≥ L⁵ ≥ 1`, `L⁶ ≥ 1`). -/
lemma exp_le_absorbYAt {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ absorbYAt X₀ x := by
  obtain ⟨hx0, hL, -, -⟩ := height_facts hX0 hX hx
  have hH : Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ capH X₀ x := le_max_left _ _
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hL0 : 1 ≤ absorbL0 X₀ x := le_trans (one_le_pow₀ hL1) (le_max_left _ _)
  have hL6 : 1 ≤ Real.log x ^ 6 := one_le_pow₀ hL1
  unfold absorbYAt
  have h0 : 0 ≤ capH X₀ x := le_trans (Real.exp_pos _).le hH
  calc Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ capH X₀ x := hH
    _ = capH X₀ x * 1 * 1 := by ring
    _ ≤ capH X₀ x * absorbL0 X₀ x * Real.log x ^ 6 := by gcongr

/-- **The lower bound** `log y ≥ 8ℓ²`. -/
theorem log_absorbYAt_ge {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    8 * Real.log (Real.log x) ^ 2 ≤ Real.log (absorbYAt X₀ x) := by
  have := Real.log_le_log (Real.exp_pos _) (exp_le_absorbYAt hX0 hX hx)
  rwa [Real.log_exp] at this

/-- `y ≥ 1` at heights `x ≥ X₀`. -/
lemma one_le_absorbYAt {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    1 ≤ absorbYAt X₀ x :=
  le_trans (Real.one_le_exp (by positivity)) (exp_le_absorbYAt hX0 hX hx)

/-! ## The conditions on `H` for the paper's `H = max(H_std, M̄₁²)` -/

/-- `H` is non-decreasing on `[X₀, ∞)` (Theorem 6.23(c)). -/
theorem capH_monotoneOn {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    MonotoneOn (capH X₀) (Ici X₀) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  obtain ⟨h1, -, h3⟩ := logs_of_ge hX0 hX hx
  unfold capH
  apply max_le_max
  · apply Real.exp_le_exp.mpr
    have hlx : 0 < Real.log x := by linarith
    have hx1 := one_lt_of_logX hX0 hX
    have := Real.log_le_log hlx (Real.log_le_log (by linarith) hxy)
    nlinarith
  · have hm := capM1_mono hX0 hX hx hxy
    have hp := capM1_pos hX0 hX hx
    nlinarith

/-- `4 H(v) ≤ v` for `v ≥ X₀` (from `H(v) ≤ v^{1/8}`). -/
theorem four_capH_le {X₀ v : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hv : X₀ ≤ v) :
    4 * capH X₀ v ≤ v := by
  have hH := InitialRange.capH_le_rpow hX0 hX hv
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hv
  have hv0 : 0 < v := by linarith [one_lt_of_logX hX0 hX]
  set w := v ^ (1 / 8 : ℝ) with hw
  have hw8 : w ^ 8 = v := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; norm_num
  have hw0 : 0 ≤ w := Real.rpow_nonneg hv0.le _
  have hw2 : 2 ≤ w := by
    by_contra hc; push_neg at hc
    have : v < 256 := by
      rw [← hw8]
      calc w ^ 8 < 2 ^ 8 := by gcongr
        _ = 256 := by norm_num
    have := Real.log_lt_log hv0 this
    have h256 : Real.log 256 < 10 ^ 8 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256); linarith
    linarith
  have : 4 * w ≤ w ^ 8 := by
    have h7 : 4 ≤ w ^ 7 := by
      calc (4 : ℝ) ≤ 2 ^ 7 := by norm_num
        _ ≤ w ^ 7 := by gcongr
    nlinarith
  linarith

/-- `L₀` is non-decreasing on `[X₀, ∞)`. -/
lemma absorbL0_mono {X₀ x z : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxz : x ≤ z) : absorbL0 X₀ x ≤ absorbL0 X₀ z := by
  obtain ⟨hx0, hL, -, -⟩ := height_facts hX0 hX hx
  have hLL : Real.log x ≤ Real.log z := Real.log_le_log hx0 hxz
  have hM := capM1_mono hX0 hX hx hxz
  have hM0 := capM1_pos hX0 hX hx
  unfold absorbL0
  apply max_le_max
  · exact pow_le_pow_left₀ (by linarith) hLL 5
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log x) hLL 3
    have h3 : 0 ≤ Real.log x ^ 3 := by positivity
    calc 48 * capM1 X₀ x * Real.log x ^ 3 ≤ 48 * capM1 X₀ z * Real.log x ^ 3 := by gcongr
      _ ≤ 48 * capM1 X₀ z * Real.log z ^ 3 := by
        apply mul_le_mul_of_nonneg_left this; linarith

/-- **`y` is non-decreasing** on `[X₀, ∞)` (Theorem 6.23(c)). -/
theorem absorbYAt_mono {X₀ x z : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxz : x ≤ z) : absorbYAt X₀ x ≤ absorbYAt X₀ z := by
  obtain ⟨hx0, hL, -, -⟩ := height_facts hX0 hX hx
  have hLL : Real.log x ≤ Real.log z := Real.log_le_log hx0 hxz
  unfold absorbYAt
  have hH := capH_monotoneOn hX0 hX (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxz)) hxz
  have hL0 := absorbL0_mono hX0 hX hx hxz
  have hH0 : 0 ≤ capH X₀ x := le_trans (Real.exp_pos _).le (le_max_left _ _)
  have hL00 : 0 ≤ absorbL0 X₀ x := le_trans (by positivity) (le_max_left _ _)
  have h6 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log x) hLL 6
  have := mul_le_mul hH hL0 hL00 (le_trans hH0 hH)
  have hz0 : 0 ≤ capH X₀ z * absorbL0 X₀ z :=
    le_trans (mul_nonneg hH0 hL00) this
  exact mul_le_mul this h6 (by positivity) hz0

/-- `log 2y ≤ 3K + 9ℓ + 11.85` (always). -/
theorem log_two_absorbYAt_le_three {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) :
    Real.log (2 * absorbYAt X₀ x) ≤ 3 * logcAt X₀ x + 9 * Real.log (Real.log x) + 11.85 := by
  have h := log_two_absorbYAt_le hX0 hX hx
  have hK := logcAt_ge hX0 hX hx
  obtain ⟨-, h4⟩ := log4_bounds
  have : max (8 * Real.log (Real.log x) ^ 2) (2 * logcAt X₀ x + 1.39) ≤
      2 * logcAt X₀ x + 2.78 := max_le (by linarith) (by linarith)
  linarith

/-- `log 2y ≤ 12ℓ² + 9ℓ + 7.69` when `K = 4ℓ² - log 4` (the standard regime). -/
theorem log_two_absorbYAt_le_std {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) (hK : logcAt X₀ x = 4 * Real.log (Real.log x) ^ 2 - Real.log 4) :
    Real.log (2 * absorbYAt X₀ x) ≤
      12 * Real.log (Real.log x) ^ 2 + 9 * Real.log (Real.log x) + 7.69 := by
  have h := log_two_absorbYAt_le hX0 hX hx
  obtain ⟨h4, -⟩ := log4_bounds
  rw [hK] at h
  have : max (8 * Real.log (Real.log x) ^ 2)
      (2 * (4 * Real.log (Real.log x) ^ 2 - Real.log 4) + 1.39) =
      8 * Real.log (Real.log x) ^ 2 := max_eq_left (by linarith)
  rw [this] at h
  linarith

/-- `K = max(4ℓ² - log 4, γ(s) Λ)`. -/
lemma logcAt_eq {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    logcAt X₀ x = max (4 * Real.log (Real.log x) ^ 2 - Real.log 4)
      (gam sHroot (capS X₀ x) * Real.log X₀) := by
  obtain ⟨-, -, -, hell⟩ := height_facts hX0 hX hx
  unfold logcAt logc
  rw [hell]

/-- **Theorem 6.23(b), first case**: if `s ≤ s_H`, then `2y(x) < X₀` (so `A` has no element at
height `x`, since its elements have a prime `r` with `X₀⁻ ≤ r < y`). -/
theorem two_absorbYAt_lt_of_le_sH {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) (hs : capS X₀ x ≤ sHroot) : 2 * absorbYAt X₀ x < X₀ := by
  obtain ⟨hx0, hL, hl, hell⟩ := height_facts hX0 hX hx
  set Λ := Real.log X₀ with hΛ
  set l := Real.log (Real.log x) with hl'
  have hX1 := one_lt_of_logX hX0 hX
  obtain ⟨hest1, hest2⟩ := log_estimates hX
  have hsH := sHroot_mem
  have hlogΛ : 18 ≤ Real.log Λ := log_ge_18 (by linarith)
  have hgam : gam sHroot (capS X₀ x) ≤ gTarget := by
    unfold gam
    rw [if_pos hs, ← gstar_sHroot]
    exact gstar_mono hs sHroot_le_six
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  have hl6 : l ≤ 2 * Real.log Λ + 6 := by rw [← hell]; linarith [hsH.2]
  have hl2 : 4 * l ^ 2 ≤ Λ / 400 + 288 := by
    have : l ^ 2 ≤ (2 * Real.log Λ + 6) ^ 2 := pow_le_pow_left₀ (by linarith) hl6 2
    nlinarith
  have hK : logcAt X₀ x ≤ gTarget * Λ := by
    rw [logcAt_eq hX0 hX hx]
    apply max_le
    · rw [hg]; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
    · exact mul_le_mul_of_nonneg_right hgam (by linarith)
  have h3 := log_two_absorbYAt_le_three hX0 hX hx
  rw [← hl'] at h3
  have hlt : Real.log (2 * absorbYAt X₀ x) < Real.log X₀ := by
    rw [← hΛ]; rw [hg] at hK; nlinarith
  have hy1 := one_le_absorbYAt hX0 hX hx
  exact (Real.log_lt_log_iff (by positivity) (by linarith)).mp hlt

end Construction

end
