module

public import RequestProject.Beurling.LocalPNT.ZeroFree

/-!
# Step 10 of the proof of Theorem 5.24(iii): the numerics

Throughout (`Num10.Hyp`): `Λ ≥ 10⁸`, `v > 1`, `Λ_p := log v ≥ 76 Λ³` and `e^{-2Λ} ≤ η ≤ 1/2`.
With `k = lpK v η`, `L₁ = lpL1 v η`, `T₁ = e^{L₁}`, `ω = lpW v η/4`, `c = 1 + 17 log Λ_p/Λ_p`,
`δ = η_{T₁}/3.79`, `c' = 1 - 0.9 δ`, `G = GLam Λ L₁` and `M = η v/(1.0001 Λ_p)`:

* the elementary facts on `k`, `L₁` and `T₁ ω = e^{3.08} k/4 ≥ 2ek`;
* (Range) `log y ≥ 10⁴ Λ² log log y` and `L_{T₁+1} ≤ log T_y + 1` for `log y ≥ Λ_p`;
* `190 Y(e^L) ≤ G(L)` for `L ≥ 5`, `1000 G(L₁) ≤ T₁`, and `log G(L₁) ≤ Λ` if `L₁ ≤ e^{Λ/2}`;
* (finite height width) `c_zf/(L + 442 + 2 log Λ + log L) ≤ δ_zf(e^L)` for `L ≥ 5`;
* `e^{σ(b + 2ω)} ≤ 1.51 v^σ` for `0 ≤ σ ≤ c`, `b = log(v(1 + η))`; so `e^{c'(b + 2ω)} ≤ 1.51 v^{c'}`
  and `e^{c(b + 2ω)} ≤ 1.6 v^c`;
* (A) + (B) + (C) `≤ Rel · M` (`contour_le_relBound_mul`).
-/

@[expose] public section

open Real

namespace LocalPNT

namespace Num10

/-- The standing hypotheses of Step 10. -/
structure Hyp (Λ v η : ℝ) : Prop where
  hΛ : 10 ^ 8 ≤ Λ
  hv : 1 < v
  hP : 76 * Λ ^ 3 ≤ Real.log v
  hη0 : Real.exp (-(2 * Λ)) ≤ η
  hη1 : η ≤ 1 / 2

/-- `log x ≤ x/N + log N - 1`. -/
lemma log_le_div_add {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    Real.log x ≤ x / N + Real.log N - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hN)
  rw [Real.log_div hx.ne' hN.ne'] at h
  linarith

lemma log_two_pow_le (n : ℕ) : Real.log (2 ^ n) ≤ 0.6931471808 * n := by
  rw [Real.log_pow]
  have := Real.log_two_lt_d9
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

/-- `log x ≤ x/10⁵` for `x ≥ 10⁸`. -/
lemma log_le_div_1e5 {x : ℝ} (hx : 10 ^ 8 ≤ x) : Real.log x ≤ x / 10 ^ 5 := by
  have h := log_le_div_add (x := x) (N := 2 ^ 20) (by linarith) (by norm_num)
  have h2 := log_two_pow_le 20
  push_cast at h2
  rw [div_eq_mul_one_div x (2 ^ 20)] at h
  rw [div_eq_mul_one_div]
  norm_num at h ⊢
  linarith

lemma eighteen_le_log {x : ℝ} (hx : 10 ^ 8 ≤ x) : 18 ≤ Real.log x := by
  have h18 : Real.exp 18 ≤ 10 ^ 8 := by
    have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc Real.exp 1 ^ 18 ≤ 2.7182818286 ^ 18 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 18
      _ ≤ 10 ^ 8 := by norm_num
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

namespace Hyp

variable {Λ v η : ℝ} (h : Hyp Λ v η)
include h

lemma Λ_pos : 0 < Λ := by linarith [h.hΛ]

lemma η_pos : 0 < η := lt_of_lt_of_le (Real.exp_pos _) h.hη0

lemma Λ_le_cube : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith [h.hΛ]) (by norm_num)

lemma P_ge : 10 ^ 8 ≤ Real.log v := by
  have := h.Λ_le_cube
  have : 0 ≤ Λ ^ 3 := by linarith [h.Λ_pos]
  linarith [h.hP, h.hΛ]

lemma P_pos : 0 < Real.log v := by linarith [h.P_ge]

lemma Λ_le_P : Λ ≤ Real.log v := by
  have := h.Λ_le_cube
  have : 0 ≤ Λ ^ 3 := by linarith [h.Λ_pos]
  linarith [h.hP]

lemma logΛ_nonneg : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith [h.hΛ])

/-- `log Λ_p ≥ 3 log Λ`. -/
lemma three_logΛ_le : 3 * Real.log Λ ≤ Real.log (Real.log v) := by
  have hΛ0 := h.Λ_pos
  rw [show 3 * Real.log Λ = Real.log (Λ ^ 3) by rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (by positivity)
  have : 0 ≤ Λ ^ 3 := by positivity
  linarith [h.hP]

lemma p_ge : 54 ≤ Real.log (Real.log v) := by
  have := eighteen_le_log h.hΛ
  linarith [h.three_logΛ_le]

lemma p_le : Real.log (Real.log v) ≤ Real.log v := by
  have := Real.log_le_sub_one_of_pos h.P_pos
  linarith

lemma logη_ge : Real.log 2 ≤ Real.log (1 / η) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ h.η_pos]
  linarith [h.hη1]

lemma logη_pos : 0 < Real.log (1 / η) :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) h.logη_ge

lemma logη_le : Real.log (1 / η) ≤ 2 * Λ := by
  rw [one_div, Real.log_inv, neg_le]
  have := Real.log_le_log (Real.exp_pos _) h.hη0
  rwa [Real.log_exp] at this

omit h in
lemma k_ge : Real.log (1 / η) + 20 * Real.log (Real.log v) ≤ (lpK v η : ℝ) := Nat.le_ceil _

lemma k_lt : (lpK v η : ℝ) < Real.log (1 / η) + 20 * Real.log (Real.log v) + 1 :=
  Nat.ceil_lt_add_one (by linarith [h.logη_pos, h.p_ge])

lemma k_pos : (0 : ℝ) < lpK v η := by linarith [(k_ge (v := v) (η := η)), h.logη_pos, h.p_ge]

/-- `k ≤ 2Λ + 20 log Λ_p + 1`. -/
lemma k_le : (lpK v η : ℝ) ≤ 2 * Λ + 20 * Real.log (Real.log v) + 1 := by
  linarith [h.k_lt, h.logη_le]

lemma logk_nonneg : 0 ≤ Real.log (lpK v η : ℝ) := by
  apply Real.log_nonneg
  have h1 : 0 < lpK v η := by exact_mod_cast h.k_pos
  exact_mod_cast h1

lemma two_p_le_L1 : 2 * Real.log (Real.log v) ≤ lpL1 v η := by
  unfold lpL1; linarith [h.logη_pos, h.logk_nonneg]

lemma L1_ge : 108 ≤ lpL1 v η := by linarith [h.two_p_le_L1, h.p_ge]

/-- `L₁ ≤ 2.016 Λ + 2.16 log Λ_p + 7`. -/
lemma L1_le : lpL1 v η ≤ 2.016 * Λ + 2.16 * Real.log (Real.log v) + 7 := by
  have hk := h.k_le
  have hlk := log_le_div_add (x := lpK v η) (N := 2 ^ 7) h.k_pos (by norm_num)
  have h7 := log_two_pow_le 7
  push_cast at h7
  rw [div_eq_mul_one_div] at hlk
  norm_num at hlk
  unfold lpL1
  nlinarith [h.logη_le]

/-- `T₁ = e^{L₁} = Λ_p² η^{-1} k e^{3.08}`. -/
lemma T1_eq : Real.exp (lpL1 v η) = Real.log v ^ 2 * (1 / η) * lpK v η * Real.exp 3.08 := by
  unfold lpL1
  have hη := h.η_pos
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log h.k_pos,
    Real.exp_log (by positivity), two_mul, Real.exp_add, Real.exp_log h.P_pos]
  ring

/-- `T₁ ω = e^{3.08} k/4`. -/
lemma T1ω_eq : Real.exp (lpL1 v η) * (lpW v η / 4) = lpK v η * Real.exp 3.08 / 4 := by
  rw [h.T1_eq]
  unfold lpW
  have := h.η_pos
  have := h.P_pos
  field_simp

lemma T1_ge : 4 ≤ Real.exp (lpL1 v η) := by
  linarith [Real.add_one_le_exp (lpL1 v η), h.L1_ge]

/-- `L_{T₁} ≤ L₁ + log 2`, indeed `log(T₁ + 4) ≤ L₁ + log 2`. -/
lemma log_T1_add_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 4) :
    Real.log (Real.exp (lpL1 v η) + a) ≤ lpL1 v η + Real.log 2 := by
  have hT := h.T1_ge
  rw [← Real.log_exp (lpL1 v η), ← Real.log_mul (Real.exp_pos _).ne' (by norm_num),
    Real.log_exp]
  exact Real.log_le_log (by linarith) (by linarith)

lemma logΛ_le_L1 : 2 * Real.log Λ ≤ lpL1 v η / 3 := by
  linarith [h.three_logΛ_le, h.two_p_le_L1]

lemma p_le_div : Real.log (Real.log v) ≤ Real.log v / 10 ^ 5 := log_le_div_1e5 h.P_ge

end Hyp

variable {Λ v η : ℝ}

/-! ### The elementary facts on `k`, `L₁` and `T₁` -/

theorem five_le_L1 (h : Hyp Λ v η) : 5 ≤ lpL1 v η := by linarith [h.L1_ge]

theorem forty_le_L1 (h : Hyp Λ v η) : 40 ≤ lpL1 v η := by linarith [h.L1_ge]

/-- `L₁ ≥ 2 log Λ_p ≥ 40`. -/
theorem forty_le_two_logP_le_L1 (h : Hyp Λ v η) :
    40 ≤ 2 * Real.log (Real.log v) ∧ 2 * Real.log (Real.log v) ≤ lpL1 v η :=
  ⟨by linarith [h.p_ge], h.two_p_le_L1⟩

theorem one_le_k (h : Hyp Λ v η) : 1 ≤ lpK v η :=
  Nat.ceil_pos.mpr (by linarith [h.logη_pos, h.p_ge])

theorem logP_le_k (h : Hyp Λ v η) : Real.log (Real.log v) ≤ (lpK v η : ℝ) / 20 := by
  linarith [Hyp.k_ge (v := v) (η := η), h.logη_pos]

/-- `e^{-k} ≤ η Λ_p^{-20}`. -/
theorem exp_neg_k_le (h : Hyp Λ v η) :
    Real.exp (-(lpK v η : ℝ)) ≤ η / Real.log v ^ 20 := by
  have hη := h.η_pos
  calc Real.exp (-(lpK v η : ℝ))
      ≤ Real.exp (-(Real.log (1 / η) + ((20 : ℕ) : ℝ) * Real.log (Real.log v))) := by
        push_cast; exact Real.exp_le_exp.mpr (by linarith [Hyp.k_ge (v := v) (η := η)])
    _ = η / Real.log v ^ 20 := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
          Real.exp_log h.P_pos]
        field_simp

lemma log_eight_le : Real.log 8 ≤ 2.08 := by
  have := log_two_pow_le 3
  norm_num at this
  linarith

/-- `T₁ ω = e^{3.08} k/4 ≥ 2ek`. -/
theorem two_e_k_le_T1ω (h : Hyp Λ v η) :
    2 * Real.exp 1 * lpK v η ≤ Real.exp (lpL1 v η) * (lpW v η / 4) := by
  rw [h.T1ω_eq]
  have h8 : 8 ≤ Real.exp 2.08 := by
    rw [← Real.exp_log (show (0 : ℝ) < 8 by norm_num)]
    exact Real.exp_le_exp.mpr log_eight_le
  have e : Real.exp 3.08 = Real.exp 1 * Real.exp 2.08 := by rw [← Real.exp_add]; norm_num
  rw [e]
  have := h.k_pos
  have := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_left h8 (mul_pos this h.k_pos).le]

/-- `(k/(T₁ω))^k ≤ (2e)^{-k} ≤ e^{-k} ≤ η Λ_p^{-20}`. -/
theorem pow_k_le (h : Hyp Λ v η) :
    ((lpK v η : ℝ) / (Real.exp (lpL1 v η) * (lpW v η / 4))) ^ lpK v η ≤
      η / Real.log v ^ 20 := by
  have hk := h.k_pos
  have hT := two_e_k_le_T1ω h
  have hTω : 0 < Real.exp (lpL1 v η) * (lpW v η / 4) := by
    have := Real.exp_pos 1; nlinarith
  have hq : (lpK v η : ℝ) / (Real.exp (lpL1 v η) * (lpW v η / 4)) ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hTω, Real.exp_neg]
    have h1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h2 : Real.exp 1 * (Real.exp 1)⁻¹ = 1 := mul_inv_cancel₀ (Real.exp_pos 1).ne'
    have h3 : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
    nlinarith [mul_le_mul_of_nonneg_left hT h3.le]
  calc ((lpK v η : ℝ) / (Real.exp (lpL1 v η) * (lpW v η / 4))) ^ lpK v η
      ≤ Real.exp (-1) ^ lpK v η := pow_le_pow_left₀ (by positivity) hq _
    _ = Real.exp (-(lpK v η : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ η / Real.log v ^ 20 := exp_neg_k_le h

/-! ### Range -/

/-- `u² ≤ 2 e^u` for `u ≥ 0`. -/
lemma sq_log_le {m : ℝ} (hm : 1 ≤ m) : Real.log m ^ 2 ≤ 2 * m := by
  have hu := Real.log_nonneg hm
  have := Real.quadratic_le_exp_of_nonneg hu
  rw [Real.exp_log (by linarith)] at this
  nlinarith

/-- (eq. lp-yrange) `10⁴ Λ² log ℓ ≤ ℓ` for `ℓ ≥ 76 Λ³`. -/
lemma yrange_of {Λ ℓ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hℓ : 76 * Λ ^ 3 ≤ ℓ) :
    10 ^ 4 * Λ ^ 2 * Real.log ℓ ≤ ℓ := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛ3 : 0 < Λ ^ 3 := by positivity
  set m := ℓ / Λ ^ 3 with hm
  have hm76 : 76 ≤ m := by rw [hm, le_div_iff₀ hΛ3]; linarith
  have hℓm : ℓ = m * Λ ^ 3 := by rw [hm]; field_simp
  have hlog : Real.log ℓ = Real.log m + 3 * Real.log Λ := by
    rw [hℓm, Real.log_mul (by positivity) hΛ3.ne', Real.log_pow]; norm_num
  have hu := Real.log_le_sub_one_of_pos (show 0 < m by linarith)
  have hlam := log_le_div_1e5 hΛ
  rw [div_eq_mul_one_div] at hlam
  have hlam0 := Real.log_nonneg (show (1 : ℝ) ≤ Λ by linarith)
  have hu0 := Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)
  rw [hlog, hℓm]
  have hΛ2 : 0 ≤ Λ ^ 2 := by positivity
  have e3 : Λ ^ 3 = Λ ^ 2 * Λ := by ring
  have h1 : 10 ^ 4 * Λ ^ 2 * Real.log m ≤ m * Λ ^ 3 / 2 := by
    have : 10 ^ 4 * Real.log m ≤ m * Λ / 2 := by nlinarith
    rw [e3]; nlinarith [mul_le_mul_of_nonneg_left this hΛ2]
  have h2 : 10 ^ 4 * Λ ^ 2 * (3 * Real.log Λ) ≤ m * Λ ^ 3 / 2 := by
    have : 3 * 10 ^ 4 * Real.log Λ ≤ m * Λ / 2 := by norm_num at hlam ⊢; nlinarith
    rw [e3]; nlinarith [mul_le_mul_of_nonneg_left this hΛ2]
  nlinarith

/-- (Range) `log y ≥ 10⁴ Λ² log log y` whenever `log y ≥ Λ_p`. -/
theorem yrange (h : Hyp Λ v η) {y : ℝ} (hy : Real.log v ≤ Real.log y) :
    10 ^ 4 * Λ ^ 2 * Real.log (Real.log y) ≤ Real.log y :=
  yrange_of h.hΛ (h.hP.trans hy)

/-- The comparison `51 Λ log Λ_p (L₁ + 500) ≤ Λ_p` for `Λ_p ≥ 76 Λ³`. -/
lemma height_aux (h : Hyp Λ v η) :
    51 * Λ * Real.log (Real.log v) * (lpL1 v η + Real.log 2 + 499) ≤ Real.log v := by
  have hΛ := h.hΛ
  have hΛ0 := h.Λ_pos
  have hΛ3 : 0 < Λ ^ 3 := by positivity
  set P := Real.log v with hP
  set m := P / Λ ^ 3 with hm
  have hm76 : 76 ≤ m := by rw [hm, le_div_iff₀ hΛ3]; linarith [h.hP]
  have hPm : P = m * Λ ^ 3 := by rw [hm]; field_simp
  set u := Real.log m
  set q := Real.log P
  have hq : q = u + 3 * Real.log Λ := by
    simp only [q, u]
    rw [hPm, Real.log_mul (by positivity) hΛ3.ne', Real.log_pow]; norm_num
  have hu := Real.log_le_sub_one_of_pos (show 0 < m by linarith)
  have hu2 := sq_log_le (show (1 : ℝ) ≤ m by linarith)
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith)
  have hlam := log_le_div_1e5 hΛ
  rw [div_eq_mul_one_div] at hlam
  norm_num at hlam
  have hlam0 := h.logΛ_nonneg
  have hL := h.L1_le
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hq0 : 0 ≤ q := by linarith [h.p_ge]
  -- `B := L₁ + log 2 + 499 ≤ 2.017 Λ + 2.16 u`, `q ≤ u + 3·10⁻⁵ Λ`
  have hB : lpL1 v η + Real.log 2 + 499 ≤ 2.017 * Λ + 2.16 * u := by nlinarith
  have hq1 : q ≤ u + 3 / 10 ^ 5 * Λ := by norm_num; linarith
  have hB0 : 0 ≤ lpL1 v η + Real.log 2 + 499 := by linarith [h.L1_ge, Real.log_two_gt_d9]
  have hqB : q * (lpL1 v η + Real.log 2 + 499) ≤ (u + 3 / 10 ^ 5 * Λ) * (2.017 * Λ + 2.16 * u) :=
    mul_le_mul hq1 hB hB0 (by positivity)
  have hexp : (u + 3 / 10 ^ 5 * Λ) * (2.017 * Λ + 2.16 * u) ≤
      2.02 * m * Λ + 4.32 * m + 6.1 / 10 ^ 5 * Λ ^ 2 := by
    have : u * Λ ≤ m * Λ := mul_le_mul_of_nonneg_right (by linarith) hΛ0.le
    norm_num; nlinarith
  have hfin : 51 * Λ * (2.02 * m * Λ + 4.32 * m + 6.1 / 10 ^ 5 * Λ ^ 2) ≤ m * Λ ^ 3 := by
    have h1 : 51 * 2.02 * m * Λ ^ 2 ≤ m * Λ ^ 3 / 3 := by
      have : 0 ≤ m * Λ ^ 2 := by positivity
      have e : m * Λ ^ 3 = (m * Λ ^ 2) * Λ := by ring
      rw [e]; nlinarith
    have h2 : 51 * 4.32 * m * Λ ≤ m * Λ ^ 3 / 3 := by
      have : 0 ≤ m * Λ := by positivity
      have : 10 ^ 16 ≤ Λ ^ 2 := by nlinarith
      have e : m * Λ ^ 3 = (m * Λ) * Λ ^ 2 := by ring
      rw [e]; nlinarith
    have h3 : 51 * (6.1 / 10 ^ 5) * Λ ^ 3 ≤ m * Λ ^ 3 / 3 := by nlinarith
    nlinarith
  calc 51 * Λ * q * (lpL1 v η + Real.log 2 + 499)
      = 51 * Λ * (q * (lpL1 v η + Real.log 2 + 499)) := by ring
    _ ≤ 51 * Λ * (2.02 * m * Λ + 4.32 * m + 6.1 / 10 ^ 5 * Λ ^ 2) := by
        gcongr; exact hqB.trans hexp
    _ ≤ m * Λ ^ 3 := hfin
    _ = P := hPm.symm

/-- (Range) `L_{T₁+1} ≤ log T_y + 1` whenever `log y ≥ Λ_p`: so the Step 7 width is available up to
height `T₁ + 1`. -/
theorem Lt_le_logTy (h : Hyp Λ v η) {y : ℝ} (hy : Real.log v ≤ Real.log y) :
    Lt (Real.exp (lpL1 v η) + 1) ≤ logTy Λ (Real.log y) + 1 := by
  have hΛ0 := h.Λ_pos
  have hP := h.P_pos
  have hT := h.T1_ge
  have hLt : Lt (Real.exp (lpL1 v η) + 1) ≤ lpL1 v η + Real.log 2 := by
    unfold Lt
    rw [abs_of_pos (by linarith), add_assoc]
    exact h.log_T1_add_le (by norm_num) (by norm_num)
  have he : Real.exp 1 ≤ Real.log v := by
    linarith [h.P_ge, Real.exp_one_lt_d9]
  have hmono : Real.log (Real.log y) / Real.log y ≤ Real.log (Real.log v) / Real.log v :=
    Real.log_div_self_antitoneOn he (he.trans hy) hy
  have hp := h.p_ge
  have hy0 : 0 < Real.log y := by linarith
  have hly : 0 < Real.log (Real.log y) := by
    apply Real.log_pos; linarith [h.P_ge]
  -- `ℓ/(51 Λ log ℓ) ≥ Λ_p/(51 Λ log Λ_p)`
  have hcmp : Real.log v / (51 * Λ * Real.log (Real.log v)) ≤
      Real.log y / (51 * Λ * Real.log (Real.log y)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_div_iff₀ hy0 hP] at hmono
    nlinarith [mul_le_mul_of_nonneg_left hmono (show 0 ≤ 51 * Λ by linarith)]
  have haux := height_aux h
  have hB : lpL1 v η + Real.log 2 + 499 ≤ Real.log v / (51 * Λ * Real.log (Real.log v)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  unfold logTy
  linarith

/-! ### `G(L₁)` -/

theorem Gb_pos (h : Hyp Λ v η) : 0 < GLam Λ (lpL1 v η) := by
  unfold GLam; linarith [h.L1_ge, h.logΛ_nonneg]

/-- `L_{e^L} ≤ L + 0.0203` for `L ≥ 5`. -/
lemma Lt_exp_le {L : ℝ} (hL : 5 ≤ L) : Lt (Real.exp L) ≤ L + 0.0203 := by
  have h5 : 148 ≤ Real.exp L := by
    have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have : (148 : ℝ) ≤ Real.exp 5 := by
      rw [e]
      calc (148 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
        _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 5
    exact this.trans (Real.exp_le_exp.mpr hL)
  have hE := Real.exp_pos L
  unfold Lt
  rw [abs_of_pos hE]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (Real.exp L + 3) / Real.exp L by positivity)
  rw [Real.log_div (by positivity) hE.ne', Real.log_exp] at h1
  have h2 : (Real.exp L + 3) / Real.exp L - 1 = 3 / Real.exp L := by field_simp; ring
  have h3 : 3 / Real.exp L ≤ 0.0203 := by rw [div_le_iff₀ hE]; linarith
  linarith

/-- `|𝔊₁| ≤ 190 Y(e^L) ≤ G(L)` on the discs of Step 8, for every `L ≥ 5`. -/
theorem Yt_le_GLam {Λ L : ℝ} (hΛ : 1 ≤ Λ) (hL : 5 ≤ L) :
    190 * Yt Λ (Real.exp L) ≤ GLam Λ L := by
  have hLt := Lt_exp_le hL
  have hl := Real.log_nonneg hΛ
  have hX : 1 ≤ Lt (Real.exp L) + 442 + 2 * Real.log Λ := by
    linarith [Lt_nonneg (Real.exp L)]
  have hlX := Real.log_le_sub_one_of_pos (show 0 < Lt (Real.exp L) + 442 +
    2 * Real.log Λ by linarith)
  unfold Yt GLam
  linarith

/-- `|𝔊₁| ≤ 190 Y(T₁) ≤ G(L₁)`. -/
theorem Yt_le_Gb (h : Hyp Λ v η) : 190 * Yt Λ (Real.exp (lpL1 v η)) ≤ GLam Λ (lpL1 v η) :=
  Yt_le_GLam (by linarith [h.hΛ]) (five_le_L1 h)

/-- (Size) `log G(L₁) ≤ Λ` if `L₁ ≤ e^{Λ/2}`. -/
theorem log_Gb_le (h : Hyp Λ v η) (hL : lpL1 v η ≤ Real.exp (Λ / 2)) :
    Real.log (GLam Λ (lpL1 v η)) ≤ Λ := by
  have hΛ := h.hΛ
  have hG := Gb_pos h
  rw [Real.log_le_iff_le_exp hG]
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Λ / 2 by linarith)
  have hlΛ : Real.log Λ ≤ Λ := by linarith [Real.log_le_sub_one_of_pos h.Λ_pos]
  have he : Real.exp Λ = Real.exp (Λ / 2) * Real.exp (Λ / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : 450 + 2 * Real.log Λ ≤ Real.exp (Λ / 2) := by nlinarith
  have h2 : 800 ≤ Real.exp (Λ / 2) := by nlinarith
  unfold GLam
  rw [he]
  nlinarith

/-- `1000 G(L₁) ≤ T₁`. -/
theorem Gb_le_T1 (h : Hyp Λ v η) : 1000 * GLam Λ (lpL1 v η) ≤ Real.exp (lpL1 v η) := by
  have hL := h.L1_ge
  have h6 := Real.pow_div_factorial_le_exp (lpL1 v η) (by linarith) 6
  have hlam := h.logΛ_le_L1
  have h5 : (108 : ℝ) ^ 5 ≤ lpL1 v η ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have e6 : lpL1 v η ^ 6 = lpL1 v η * lpL1 v η ^ 5 := by ring
  norm_num [Nat.factorial] at h6
  unfold GLam
  rw [e6] at h6
  nlinarith [mul_le_mul_of_nonneg_left h5 (show 0 ≤ lpL1 v η by linarith)]

/-! ### The finite-height width (Step 7) -/

/-- (Finite height) `c_zf/(L + 442 + 2 log Λ + log L) ≤ δ_zf(e^L) = η_{e^L}/3.79` for `L ≥ 5`. -/
theorem cZF_div_le_etat {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 5 ≤ L) :
    cZF Λ / (L + 442 + 2 * Real.log Λ + Real.log L) ≤ etat Λ (Real.exp L) / 3.79 := by
  have hΛ0 : 0 < Λ := by linarith
  have hlam := eighteen_le_log hΛ
  have hlL := Real.log_nonneg (show (1 : ℝ) ≤ L by linarith)
  have hLt := Lt_exp_le hL
  set X := Lt (Real.exp L) + 442 + 2 * Real.log Λ with hXdef
  have hX0 : 0 < X := by have := Lt_nonneg (Real.exp L); linarith
  -- `log X ≤ log L + X/(128 L) + log 128 - 1`
  have hlX : Real.log X ≤ Real.log L + X * (1 / 640) + 7 * 0.6931471808 - 1 := by
    have h1 := log_le_div_add (x := X / L) (N := 2 ^ 7) (by positivity) (by norm_num)
    rw [Real.log_div hX0.ne' (by linarith)] at h1
    have h2 := log_two_pow_le 7
    push_cast at h2
    have h3 : X / L / 2 ^ 7 ≤ X * (1 / 640) := by
      rw [div_div, mul_one_div]
      exact div_le_div_of_nonneg_left hX0.le (by norm_num) (by linarith)
    linarith
  set D := L + 442 + 2 * Real.log Λ + Real.log L with hD
  have hY : Yt Λ (Real.exp L) ≤ X + Real.log X + 0.7 := by unfold Yt; rw [← hXdef]
  have hY0 : 0 < Yt Λ (Real.exp L) := lt_of_lt_of_le (by norm_num) (Yt_ge (by linarith) _)
  have key : 0.088 * 3.79 * Yt Λ (Real.exp L) ≤ 0.33769 * D := by linarith
  unfold etat cZF
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key hΛ0.le]

/-- (Finite height) `c_zf/(L₁ + 442 + 2 log Λ + log L₁) ≤ δ_zf(T₁) = η_{T₁}/3.79`. -/
theorem cZF_div_le_width (h : Hyp Λ v η) :
    cZF Λ / (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η)) ≤
      etat Λ (Real.exp (lpL1 v η)) / 3.79 :=
  cZF_div_le_etat h.hΛ (five_le_L1 h)

/-! ### The Mellin transform: `e^{σ(b + 2ω)} ≤ 1.51 v^σ` -/

lemma c_sub_one_le (h : Hyp Λ v η) : 17 * Real.log (Real.log v) / Real.log v ≤ 1 / 5000 := by
  rw [div_le_div_iff₀ h.P_pos (by norm_num)]
  have := h.p_le_div
  rw [div_eq_mul_one_div] at this
  norm_num at this
  linarith [h.P_pos]

lemma lpW_le (h : Hyp Λ v η) : lpW v η ≤ 1 / 10 ^ 4 := by
  have := h.P_ge
  have := h.η_pos
  unfold lpW
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [h.hη1]

/-- `e^{σ(b + 2ω)} ≤ 1.51 v^σ` for `0 ≤ σ ≤ c`, where `b = log(v(1 + η))` and `ω = w/4`. -/
theorem exp_sigma_le (h : Hyp Λ v η) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ 1 + 17 * Real.log (Real.log v) / Real.log v) :
    Real.exp (σ * (Real.log (v * (1 + η)) + 2 * (lpW v η / 4))) ≤ 1.51 * v ^ σ := by
  have hη := h.η_pos
  have hv0 : 0 < v := by linarith [h.hv]
  set a := Real.log (1 + η) + 2 * (lpW v η / 4) with ha
  have hω0 : 0 ≤ lpW v η := by have := h.P_pos; unfold lpW; positivity
  have hω := lpW_le h
  have hl1 : Real.log (1 + η) ≤ η := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + η by linarith)]
  have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith [h.hη1]
  have hc := c_sub_one_le h
  have hσa : σ * a ≤ a + a / 5000 := by
    have : σ ≤ 1 + 1 / 5000 := by linarith
    nlinarith
  set ε := 2 * (lpW v η / 4) + a / 5000 with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hε : ε ≤ 1 / 1000 := by rw [hεdef]; linarith
  have hexpε : Real.exp ε ≤ 1.0011 := by
    have h1 := Real.add_one_le_exp (-ε)
    have h2 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos ε
    nlinarith
  have hsplit : Real.log (v * (1 + η)) + 2 * (lpW v η / 4) = Real.log v + a := by
    rw [Real.log_mul hv0.ne' (by linarith), ha]; ring
  rw [hsplit, mul_add, Real.exp_add, Real.rpow_def_of_pos hv0, mul_comm (Real.log v) σ]
  have hexpa : Real.exp (σ * a) ≤ (1 + η) * Real.exp ε := by
    calc Real.exp (σ * a) ≤ Real.exp (Real.log (1 + η) + ε) := by
          apply Real.exp_le_exp.mpr; rw [hεdef]; linarith
      _ = (1 + η) * Real.exp ε := by rw [Real.exp_add, Real.exp_log (by linarith)]
  have h15 : (1 + η) * Real.exp ε ≤ 1.51 := by
    nlinarith [h.hη1, Real.exp_pos ε]
  have := Real.exp_pos (σ * Real.log v)
  nlinarith [mul_le_mul_of_nonneg_left (hexpa.trans h15) this.le]

/-- `e^{c'(b + 2ω)} ≤ 1.51 v^{c'}`, `c' = 1 - 0.9 δ_zf(T₁)`. -/
theorem exp_c'_le (h : Hyp Λ v η) :
    Real.exp ((1 - 0.9 * (etat Λ (Real.exp (lpL1 v η)) / 3.79)) *
        (Real.log (v * (1 + η)) + 2 * (lpW v η / 4))) ≤
      1.51 * v ^ (1 - 0.9 * (etat Λ (Real.exp (lpL1 v η)) / 3.79)) := by
  have hδ0 := (etat_pos (by linarith [h.hΛ]) (Real.exp (lpL1 v η))).le
  have hδ1 := etat_le h.hΛ (Real.exp (lpL1 v η))
  have hc : 0 ≤ 17 * Real.log (Real.log v) / Real.log v := by
    have := h.p_ge; have := h.P_pos; positivity
  have hδ : 0 ≤ etat Λ (Real.exp (lpL1 v η)) / 3.79 := by positivity
  apply exp_sigma_le h
  · norm_num at hδ1 ⊢; linarith
  · linarith

/-- `e^{c(b + 2ω)} ≤ 1.6 v^c`, `c = 1 + 17 log Λ_p/Λ_p`. -/
theorem exp_c_le (h : Hyp Λ v η) :
    Real.exp ((1 + 17 * Real.log (Real.log v) / Real.log v) *
        (Real.log (v * (1 + η)) + 2 * (lpW v η / 4))) ≤
      1.6 * v ^ (1 + 17 * Real.log (Real.log v) / Real.log v) := by
  have hc : 0 ≤ 17 * Real.log (Real.log v) / Real.log v := by
    have := h.p_ge; have := h.P_pos; positivity
  have hv : 0 ≤ v ^ (1 + 17 * Real.log (Real.log v) / Real.log v) :=
    Real.rpow_nonneg (by linarith [h.hv]) _
  have := exp_sigma_le h (by linarith) le_rfl
  linarith

/-! ### (A) + (B) + (C) -/

/-- `v^c = v Λ_p^{17}`. -/
lemma rpow_c_eq (h : Hyp Λ v η) :
    v ^ (1 + 17 * Real.log (Real.log v) / Real.log v) = v * Real.log v ^ 17 := by
  have hv0 : 0 < v := by linarith [h.hv]
  have hP := h.P_pos
  rw [Real.rpow_def_of_pos hv0, show Real.log v * (1 + 17 * Real.log (Real.log v) / Real.log v)
    = Real.log v + ((17 : ℕ) : ℝ) * Real.log (Real.log v) by push_cast; field_simp,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hv0, Real.exp_log hP]

/-- `v^{c'} = v e^{-0.9 δ Λ_p}`. -/
lemma rpow_c'_eq (h : Hyp Λ v η) (δ : ℝ) :
    v ^ (1 - 0.9 * δ) = v * Real.exp (-(0.9 * δ * Real.log v)) := by
  have hv0 : 0 < v := by linarith [h.hv]
  rw [Real.rpow_def_of_pos hv0, show Real.log v * (1 - 0.9 * δ) =
    Real.log v + -(0.9 * δ * Real.log v) by ring, Real.exp_add, Real.exp_log hv0]

/-- `0 ≤ 8 log(1 + 1.0001 η T₁/2) ≤ 201 Λ_p`. -/
lemma Q_bounds (h : Hyp Λ v η) :
    0 ≤ 8 * Real.log (1 + 1.0001 * η * Real.exp (lpL1 v η) / 2) ∧
      8 * Real.log (1 + 1.0001 * η * Real.exp (lpL1 v η) / 2) ≤ 201 * Real.log v := by
  have hη := h.η_pos
  have hk := h.k_pos
  have hT := Real.exp_pos (lpL1 v η)
  have hηT : η * Real.exp (lpL1 v η) = Real.log v ^ 2 * lpK v η * Real.exp 3.08 := by
    rw [h.T1_eq]; field_simp
  have hηT2 : 2 ≤ η * Real.exp (lpL1 v η) := by
    rw [hηT]
    have : (1 : ℝ) ≤ lpK v η := by exact_mod_cast one_le_k h
    have : 1 ≤ Real.exp 3.08 := by linarith [Real.add_one_le_exp 3.08]
    have := h.P_ge
    have : 10 ^ 16 ≤ Real.log v ^ 2 := by nlinarith
    have : 10 ^ 16 ≤ Real.log v ^ 2 * lpK v η := by nlinarith
    nlinarith
  have e : Real.log (1.0001 * η * Real.exp (lpL1 v η)) =
      Real.log 1.0001 + 2 * Real.log (Real.log v) + Real.log (lpK v η) + 3.08 := by
    rw [Real.log_mul (by positivity) hT.ne', Real.log_mul (by norm_num) hη.ne', Real.log_exp]
    unfold lpL1; rw [one_div, Real.log_inv]; ring
  have hle : Real.log (1 + 1.0001 * η * Real.exp (lpL1 v η) / 2) ≤
      Real.log (1.0001 * η * Real.exp (lpL1 v η)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h1 : Real.log 1.0001 ≤ 0.0001 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.0001 by norm_num); linarith
  have h3 : Real.log (lpK v η) ≤ lpK v η := by linarith [Real.log_le_sub_one_of_pos hk]
  have h4 := h.k_le
  have h5 := h.Λ_le_P
  have h6 := h.p_le
  have h7 := h.p_ge
  have h8 := h.P_ge
  constructor
  · have : 0 ≤ Real.log (1 + 1.0001 * η * Real.exp (lpL1 v η) / 2) :=
      Real.log_nonneg (by have : 0 ≤ 1.0001 * η * Real.exp (lpL1 v η) / 2 := by positivity
                          linarith)
    linarith
  · rw [e] at hle; linarith

/-- `0 ≤ log(1/(c - 1)) ≤ log Λ_p`. -/
lemma log_inv_c_bounds (h : Hyp Λ v η) :
    0 ≤ Real.log (1 / (1 + 17 * Real.log (Real.log v) / Real.log v - 1)) ∧
      Real.log (1 / (1 + 17 * Real.log (Real.log v) / Real.log v - 1)) ≤
        Real.log (Real.log v) := by
  have hP := h.P_pos
  have hp := h.p_ge
  have hc := c_sub_one_le h
  have e : 1 / (1 + 17 * Real.log (Real.log v) / Real.log v - 1) =
      Real.log v / (17 * Real.log (Real.log v)) := by
    rw [add_sub_cancel_left, one_div_div]
  rw [e]
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_div_iff₀ hP (by norm_num)] at hc
    linarith
  · rw [Real.log_div hP.ne' (by positivity)]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 17 * Real.log (Real.log v) by linarith)]

/-- The algebra of (A). -/
lemma termA_le {G w e E Q P : ℝ} (hG : 0 ≤ G) (hw : 0 ≤ w) (he0 : 0 ≤ e) (he : e ≤ E)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 201 * P) (hP : 3 ≤ P) :
    (1 / (2 * π)) * (G * (1.51 * (w * e)) * Q) ≤ 18 * G * P ^ 2 * E * w / 1.0001 := by
  have hpi := Real.pi_gt_three
  have hE0 : 0 ≤ E := he0.trans he
  have key : 1.51 * (201 * P) / (2 * π) ≤ 18 * P ^ 2 / 1.0001 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 108 * P ^ 2 ≤ 18 * P ^ 2 * (2 * π) := by nlinarith [sq_nonneg P]
    nlinarith
  calc (1 / (2 * π)) * (G * (1.51 * (w * e)) * Q)
      ≤ (1 / (2 * π)) * (G * (1.51 * (w * E)) * (201 * P)) := by gcongr
    _ = (G * w * E) * (1.51 * (201 * P) / (2 * π)) := by ring
    _ ≤ (G * w * E) * (18 * P ^ 2 / 1.0001) := by gcongr
    _ = 18 * G * P ^ 2 * E * w / 1.0001 := by ring

/-- The algebra of (B). -/
lemma termB_le {d G w P T R η : ℝ} (hd : d ≤ 1) (hG : 0 ≤ G)
    (hGT : 1000 * G ≤ T) (hT : 0 < T) (hw : 0 ≤ w) (hP : 0 < P) (hη : 0 ≤ η)
    (hR0 : 0 ≤ R) (hR : R ≤ η / P ^ 20) :
    (1 / (2 * π)) * (2 * d * G * (1.6 * (w * P ^ 17)) * (2 / T) * R) ≤
      1 / 100 * (η * w / (1.0001 * P ^ 3)) := by
  have hpi := Real.pi_gt_d2
  have key : 6.4 / (2 * π) * (G / T) ≤ 1 / 100 / 1.0001 := by
    have h1 : G / T ≤ 1 / 1000 := by rw [div_le_iff₀ hT]; linarith
    have h2 : 6.4 / (2 * π) ≤ 1.1 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h3 : 0 ≤ G / T := by positivity
    calc 6.4 / (2 * π) * (G / T) ≤ 1.1 * (1 / 1000) := by gcongr
      _ ≤ 1 / 100 / 1.0001 := by norm_num
  calc (1 / (2 * π)) * (2 * d * G * (1.6 * (w * P ^ 17)) * (2 / T) * R)
      ≤ (1 / (2 * π)) * (2 * 1 * G * (1.6 * (w * P ^ 17)) * (2 / T) * (η / P ^ 20)) := by
        gcongr
    _ = (6.4 / (2 * π) * (G / T)) * (η * w / P ^ 3) := by field_simp; ring
    _ ≤ (1 / 100 / 1.0001) * (η * w / P ^ 3) := by gcongr
    _ = 1 / 100 * (η * w / (1.0001 * P ^ 3)) := by field_simp

/-- The algebra of (C). -/
lemma termC_le {ℓ p w P R η k : ℝ} (hℓ : ℓ ≤ p) (hp : 54 ≤ p) (hk : 20 * p ≤ k)
    (hw : 0 ≤ w) (hP : 0 < P) (hη : 0 ≤ η) (hR0 : 0 ≤ R) (hR : R ≤ η / P ^ 20) :
    (1 / (2 * π)) * ((1.5 * ℓ + 8) * (1.6 * (w * P ^ 17)) * (4 / k) * R) ≤
      99 / 100 * (η * w / (1.0001 * P ^ 3)) := by
  have hpi := Real.pi_gt_d2
  have hk0 : 0 < k := by linarith
  have key : 6.4 / (2 * π) * ((1.5 * p + 8) / k) ≤ 99 / 100 / 1.0001 := by
    have h1 : (1.5 * p + 8) / k ≤ 1 / 10 := by rw [div_le_iff₀ hk0]; linarith
    have h2 : 6.4 / (2 * π) ≤ 1.1 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h3 : 0 ≤ (1.5 * p + 8) / k := by
      apply div_nonneg _ hk0.le; linarith
    calc 6.4 / (2 * π) * ((1.5 * p + 8) / k) ≤ 1.1 * (1 / 10) := by gcongr
      _ ≤ 99 / 100 / 1.0001 := by norm_num
  calc (1 / (2 * π)) * ((1.5 * ℓ + 8) * (1.6 * (w * P ^ 17)) * (4 / k) * R)
      ≤ (1 / (2 * π)) * ((1.5 * p + 8) * (1.6 * (w * P ^ 17)) * (4 / k) * (η / P ^ 20)) := by
        gcongr
    _ = (6.4 / (2 * π) * ((1.5 * p + 8) / k)) * (η * w / P ^ 3) := by field_simp; ring
    _ ≤ (99 / 100 / 1.0001) * (η * w / P ^ 3) := by gcongr
    _ = 99 / 100 * (η * w / (1.0001 * P ^ 3)) := by field_simp

/-- `exp(-0.9 δ Λ_p) ≤ exp(-0.9 c_zf Λ_p/(L₁ + 442 + 2 log Λ + log L₁))`. -/
lemma exp_width_le (h : Hyp Λ v η) :
    Real.exp (-(0.9 * (etat Λ (Real.exp (lpL1 v η)) / 3.79) * Real.log v)) ≤
      Real.exp (-(0.9 * cZF Λ * Real.log v /
        (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η)))) := by
  apply Real.exp_le_exp.mpr
  have hw := cZF_div_le_width h
  have hP := h.P_pos
  rw [neg_le_neg_iff,
    show 0.9 * cZF Λ * Real.log v / (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η)) =
      0.9 * Real.log v * (cZF Λ / (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η))) by
      ring,
    show 0.9 * (etat Λ (Real.exp (lpL1 v η)) / 3.79) * Real.log v =
      0.9 * Real.log v * (etat Λ (Real.exp (lpL1 v η)) / 3.79) by ring]
  gcongr

/-- **Step 10, (A) + (B) + (C)**: with `M = η v/(1.0001 Λ_p)` the main term, the three pieces of
the contour (with `1.51 v^{c'} ≥ e^{c'(b + 2ω)}` and `1.6 v^c ≥ e^{c(b + 2ω)}`, `exp_c'_le`,
`exp_c_le`) add up to at most `Rel · M`. -/
theorem contour_le_relBound_mul (h : Hyp Λ v η) :
    let k : ℝ := lpK v η
    let L₁ := lpL1 v η
    let T₁ := Real.exp L₁
    let ω := lpW v η / 4
    let c := 1 + 17 * Real.log (Real.log v) / Real.log v
    let δ := etat Λ T₁ / 3.79
    let c' := 1 - 0.9 * δ
    let Gb := GLam Λ L₁
    let M := η * v / (1.0001 * Real.log v)
    (1 / (2 * π)) * (Gb * (1.51 * v ^ c') * (8 * Real.log (1 + 1.0001 * η * T₁ / 2)))
      + (1 / (2 * π)) * (2 * (c - c') * Gb * (1.6 * v ^ c) * (2 / T₁) * (k / (T₁ * ω)) ^ lpK v η)
      + (1 / (2 * π)) * ((1.5 * Real.log (1 / (c - 1)) + 8) * (1.6 * v ^ c) * (4 / k) *
          (k / (T₁ * ω)) ^ lpK v η)
      ≤ relBound Λ v η * M := by
  intro k L₁ T₁ ω c δ c' Gb M
  simp only [k, L₁, T₁, ω, c, δ, c', Gb, M]
  have hv0 : 0 < v := by linarith [h.hv]
  have hη := h.η_pos
  have hP := h.P_pos
  have hP8 := h.P_ge
  have hδ : 0 < etat Λ (Real.exp (lpL1 v η)) / 3.79 :=
    div_pos (etat_pos (by linarith [h.hΛ]) _) (by norm_num)
  have hδ1 := etat_le h.hΛ (Real.exp (lpL1 v η))
  have hc := c_sub_one_le h
  have hp0 : 0 ≤ 17 * Real.log (Real.log v) / Real.log v := by
    have := h.p_ge; positivity
  have hTω : 0 < Real.exp (lpL1 v η) * (lpW v η / 4) := by
    have := two_e_k_le_T1ω h; have := Real.exp_pos 1; have := h.k_pos
    nlinarith
  have hR0 : 0 ≤ ((lpK v η : ℝ) / (Real.exp (lpL1 v η) * (lpW v η / 4))) ^ lpK v η := by
    have := h.k_pos; positivity
  have hQ := Q_bounds h
  have hl := log_inv_c_bounds h
  have hrel : relBound Λ v η * (η * v / (1.0001 * Real.log v)) =
      18 * GLam Λ (lpL1 v η) * Real.log v ^ 2 *
        Real.exp (-(0.9 * cZF Λ * Real.log v /
          (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η)))) * v / 1.0001 +
        (1 / 100 * (η * v / (1.0001 * Real.log v ^ 3)) +
          99 / 100 * (η * v / (1.0001 * Real.log v ^ 3))) := by
    unfold relBound
    field_simp
    ring
  rw [hrel, rpow_c_eq h, rpow_c'_eq h]
  have hA := termA_le (G := GLam Λ (lpL1 v η)) (w := v) (Gb_pos h).le hv0.le (Real.exp_pos _).le
    (exp_width_le h) hQ.1 hQ.2 (by linarith)
  have hB := termB_le (d := 1 + 17 * Real.log (Real.log v) / Real.log v -
      (1 - 0.9 * (etat Λ (Real.exp (lpL1 v η)) / 3.79))) (w := v)
    (by norm_num at hδ1 ⊢; linarith) (Gb_pos h).le (Gb_le_T1 h) (Real.exp_pos _)
    hv0.le hP hη.le hR0 (pow_k_le h)
  have hC := termC_le (w := v) (k := (lpK v η : ℝ)) hl.2 h.p_ge (by linarith [logP_le_k h])
    hv0.le hP hη.le hR0 (pow_k_le h)
  linarith

end Num10

end LocalPNT
