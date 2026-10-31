module

public import RequestProject.Beurling.Construction.YBounds

/-!
# Condition (81) and the hypothesis `(∗)` of Lemma 6.26 (Theorem 6.23(b), Step 5)

* `cond81_core`: the numerical core of Step 5 for a power window. With `u₀ = θ_b L / log 2y`, in
  the raised regime (`log 2y ≤ 3.01γΛ`, `log C_d + 4 log L ≤ 1.01γΛ`, `log x ≥ 393Λ²`,
  `0 < γ ≤ 7.5`) or the standard regime (`log 2y ≤ 12.1ℓ²`, `log C_d + 4 log L ≤ 4.1ℓ²`,
  `ℓ ≥ 2886`): `u₀ ≥ 2·10⁸` and `log 2y + log C_d + 4 log L ≤ 0.9 u₀ log u₀`.
* `cond81_core_win`: the same for the θ-free window `h = winH X₀` (`u₀ = log h / log 2y`): on the
  first piece `log h = L/8` it is `cond81_core` with `θ_b = 1/8`; beyond `L = 400Λ²` it uses
  `log h ≥ 50Λ²` in the raised regime (`cond81_raised_win`) and `log h ≥ 27Λℓ²`,
  `log h ≥ 120ℓ⁴/log ℓ` in the standard regime (`cond81_std_win`), as in the analytic proof of
  Step 5 in the paper.
* `regimes_of_gt_sH`: above `s_H`, `y(x)` is in one of the two regimes.
-/

@[expose] public section

open Real Set BSCert.Capl CaplLink QueueMono InitialRange AbsorbEmpty

namespace Construction

lemma log_217e6_le_log {t : ℝ} (ht : 217000000 ≤ t) : 19.19 ≤ Real.log t :=
  le_trans log_217e6_ge (Real.log_le_log (by norm_num) ht)

lemma log_2e8_ge : (19.1 : ℝ) ≤ Real.log (2 * 10 ^ 8) := by
  have h := BSCert.FX.logLoQF_le (a := 200000000) (by norm_num)
  have hc : (191 / 10 : ℚ) ≤ BSCert.FX.logLoQF 200000000 := by decide +kernel
  have hc' : ((191 / 10 : ℚ) : ℝ) ≤ ((BSCert.FX.logLoQF 200000000 : ℚ) : ℝ) := by
    exact_mod_cast hc
  push_cast at h hc'
  rw [show (2 * 10 ^ 8 : ℝ) = 200000000 by norm_num]
  linarith

/-- **The numerical core of Step 5 of Theorem 6.23**. Let `Λ ≥ 10⁸`, `θ_b ≥ 1/20`,
`L_x = e^ℓ`, `L ≥ L_x - 1`, `Ly > 0`, and suppose one of the two regimes. In the raised regime
(on and above the ramp) `L_x = Λ² e^s` with `122 γ ≤ e^s` and `15 γ² ≤ e^s` (`ramp_facts`).
Then `u₀ = θ_b L / Ly` satisfies `u₀ ≥ 2·10⁸` and `Ly + D ≤ 0.9 u₀ log u₀`. -/
theorem cond81_core {Λ θb L Lx ℓ Ly D γ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hθ : 1 / 20 ≤ θb)
    (hLx : Lx = Real.exp ℓ) (hLLx : Lx - 1 ≤ L) (hLy0 : 0 < Ly)
    (hreg : (0.3 ≤ γ ∧ γ ≤ 7.5 ∧ Ly ≤ 3.01 * γ * Λ ∧ D ≤ 1.01 * γ * Λ ∧
        122 * γ * Λ ^ 2 ≤ Lx ∧ 15 * γ ^ 2 * Λ ^ 2 ≤ Lx) ∨
      (Ly ≤ 12.1 * ℓ ^ 2 ∧ D ≤ 4.1 * ℓ ^ 2 ∧ 2886 ≤ ℓ)) :
    2 * 10 ^ 8 ≤ θb * L / Ly ∧ Ly + D ≤ 0.9 * (θb * L / Ly) * Real.log (θb * L / Ly) := by
  set u0 := θb * L / Ly with hu0
  rcases hreg with ⟨hγ0, hγ, hLy, hD, hLx1, hLx2⟩ | ⟨hLy, hD, hl⟩
  · -- the raised regime: `u₀ ≥ (L_x - 1)/(60.2 γΛ)`
    have hγΛ : 3 * 10 ^ 7 ≤ γ * Λ := by nlinarith
    have hΛ2 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have hL0 : 0 ≤ L := by nlinarith
    have hθL : L / 20 ≤ θb * L := by nlinarith
    have hu0big : 2 * 10 ^ 8 ≤ u0 := by
      rw [hu0, le_div_iff₀ hLy0]
      have h1 : 2 * 10 ^ 8 * Ly ≤ 2 * 10 ^ 8 * (3.01 * γ * Λ) := by linarith
      have h2 : γ * Λ * (6.02 * 10 ^ 8) + 1 ≤ γ * Λ * (6.1 * Λ) := by
        have : γ * Λ * (8 * 10 ^ 6) ≤ γ * Λ * (6.1 * Λ - 6.02 * 10 ^ 8) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith
      have e : γ * Λ * (6.1 * Λ) = 6.1 * (γ * Λ ^ 2) := by ring
      nlinarith
    have hlog : 19.1 ≤ Real.log u0 :=
      le_trans log_2e8_ge (Real.log_le_log (by norm_num) hu0big)
    refine ⟨hu0big, ?_⟩
    have h1 : 0.9 * u0 * 19.1 ≤ 0.9 * u0 * Real.log u0 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : 4.02 * γ * Λ ≤ 0.9 * u0 * 19.1 := by
      have hsq : (3 * 10 ^ 7 : ℝ) ^ 2 ≤ (γ * Λ) ^ 2 := pow_le_pow_left₀ (by norm_num) hγΛ 2
      have e1 : 4.02 * γ * Λ * Ly ≤ 4.02 * γ * Λ * (3.01 * γ * Λ) :=
        mul_le_mul_of_nonneg_left hLy (by nlinarith)
      have e2 : 4.02 * γ * Λ * (3.01 * γ * Λ) + 1 ≤ 0.8595 * (15 * γ ^ 2 * Λ ^ 2) := by
        nlinarith
      have hu0' : 4.02 * γ * Λ * Ly ≤ 17.19 * (θb * L) := by nlinarith
      have : 4.02 * γ * Λ ≤ 17.19 * u0 := by
        rw [hu0, ← mul_div_assoc, le_div_iff₀ hLy0]; linarith
      linarith
    linarith
  · -- the standard regime: `u₀ ≥ ℓ⁴/176000`
    have hexp : ℓ ^ 6 / 720 ≤ Lx := by
      rw [hLx]
      have := Real.pow_div_factorial_le_exp ℓ (by linarith : (0 : ℝ) ≤ ℓ) 6
      simpa [Nat.factorial] using this
    have hl2 : (2886 : ℝ) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hl 2
    have hl4 : ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 := by ring
    have hl6 : ℓ ^ 6 = ℓ ^ 4 * ℓ ^ 2 := by ring
    have hθL : ℓ ^ 6 / 14500 ≤ θb * L := by
      have h1 : 1 ≤ ℓ ^ 6 / 720 - ℓ ^ 6 / 721 := by
        have : ℓ ^ 6 / 720 - ℓ ^ 6 / 721 = ℓ ^ 6 / (720 * 721) := by ring
        rw [this, le_div_iff₀ (by norm_num)]
        have : (2886 : ℝ) ^ 6 ≤ ℓ ^ 6 := pow_le_pow_left₀ (by norm_num) hl 6
        nlinarith
      have hL : ℓ ^ 6 / 721 ≤ L := by linarith
      have h0 : 0 ≤ ℓ ^ 6 := by positivity
      nlinarith
    have hl20 : 0 < ℓ ^ 2 := by positivity
    have hu0ge : ℓ ^ 4 / 176000 ≤ u0 := by
      rw [hu0, div_le_div_iff₀ (by norm_num) hLy0]
      have : ℓ ^ 4 * Ly ≤ ℓ ^ 4 * (12.1 * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left hLy (by positivity)
      nlinarith
    have hl4big : (2886 : ℝ) ^ 4 ≤ ℓ ^ 4 := pow_le_pow_left₀ (by norm_num) hl 4
    have hu0big : 217000000 ≤ u0 := by
      have : (217000000 : ℝ) ≤ ℓ ^ 4 / 176000 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      linarith
    have hlog := log_217e6_le_log hu0big
    refine ⟨by linarith, ?_⟩
    have h1 : 0.9 * u0 * 19.19 ≤ 0.9 * u0 * Real.log u0 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : 16.2 * ℓ ^ 2 ≤ 0.9 * (ℓ ^ 4 / 176000) * 19.19 := by
      rw [hl4]; nlinarith
    have h3 : 0.9 * (ℓ ^ 4 / 176000) * 19.19 ≤ 0.9 * u0 * 19.19 := by nlinarith
    linarith

/-- **Step 5 beyond `L = 400Λ²`, raised regime**: `log h ≥ 50Λ²` gives `u₀ ≥ 16.6Λ/γ ≥ 2·10⁸`
and `log 2y + D ≤ 4.02γΛ ≤ 0.9 u₀ log u₀`. -/
theorem cond81_raised_win {Λ Ly D γ lh : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hLy0 : 0 < Ly)
    (hγ0 : 0.3 ≤ γ) (hγ : γ ≤ 7.5) (hLy : Ly ≤ 3.01 * γ * Λ) (hD : D ≤ 1.01 * γ * Λ)
    (hlh : 50 * Λ ^ 2 ≤ lh) :
    2 * 10 ^ 8 ≤ lh / Ly ∧ Ly + D ≤ 0.9 * (lh / Ly) * Real.log (lh / Ly) := by
  set u0 := lh / Ly with hu0
  have hγp : 0 < γ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hu0ge : 16.6 * Λ / γ ≤ u0 := by
    rw [hu0, div_le_div_iff₀ hγp hLy0]
    have : 16.6 * Λ * Ly ≤ 16.6 * Λ * (3.01 * γ * Λ) :=
      mul_le_mul_of_nonneg_left hLy (by positivity)
    nlinarith
  have hu0big : 2 * 10 ^ 8 ≤ u0 := by
    refine le_trans ?_ hu0ge
    rw [le_div_iff₀ hγp]; nlinarith
  have hlog : 19.1 ≤ Real.log u0 :=
    le_trans log_2e8_ge (Real.log_le_log (by norm_num) hu0big)
  refine ⟨hu0big, ?_⟩
  have h1 : 0.9 * u0 * 19.1 ≤ 0.9 * u0 * Real.log u0 :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 4.02 * γ * Λ ≤ 0.9 * u0 * 19.1 := by
    have h3 : 0.9 * (16.6 * Λ / γ) * 19.1 ≤ 0.9 * u0 * 19.1 := by nlinarith
    have h4 : 4.02 * γ * Λ ≤ 0.9 * (16.6 * Λ / γ) * 19.1 := by
      rw [show 0.9 * (16.6 * Λ / γ) * 19.1 = 285.354 * Λ / γ by ring, le_div_iff₀ hγp]
      nlinarith
    linarith
  linarith

/-- **Step 5 beyond `L = 400Λ²`, standard regime** (`ℓ ≥ 2886`, `log 2y ≤ 12.1ℓ²`, `D ≤ 4.1ℓ²`,
`ℓ_u = log L ∈ [ℓ - 10⁻³, ℓ]`): `log h ≥ 27Λℓ_u²` gives `u₀ ≥ 2.23Λ ≥ 2·10⁸`, and either
`ℓ² ≤ 2Λ` and `0.9 u₀ log u₀ ≥ 38Λ ≥ 16.2ℓ²`, or `log h ≥ 120ℓ_u⁴/log ℓ_u` gives
`u₀ ≥ 9.9ℓ²/log ℓ` and `0.9 u₀ log u₀ ≥ 0.9 · 9.9 · (11/6) ℓ² ≥ 16.2ℓ²`. -/
theorem cond81_std_win {Λ L ℓ Ly D lh : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hl : 2886 ≤ ℓ)
    (hℓu1 : ℓ - 1 / 1000 ≤ Real.log L) (hℓu2 : Real.log L ≤ ℓ)
    (hLy0 : 0 < Ly) (hLy : Ly ≤ 12.1 * ℓ ^ 2) (hD : D ≤ 4.1 * ℓ ^ 2)
    (h27 : 27 * Λ * Real.log L ^ 2 ≤ lh)
    (h120 : 120 * Real.log L ^ 4 / Real.log (Real.log L) ≤ lh) :
    2 * 10 ^ 8 ≤ lh / Ly ∧ Ly + D ≤ 0.9 * (lh / Ly) * Real.log (lh / Ly) := by
  set u0 := lh / Ly with hu0
  set ℓu := Real.log L with hℓu
  have hΛ0 : 0 < Λ := by linarith
  have hℓu0 : 2885 ≤ ℓu := by linarith
  have hsq : 0.9999 * ℓ ^ 2 ≤ ℓu ^ 2 := by nlinarith
  have hl2 : 0 < ℓ ^ 2 := by positivity
  -- `u₀ ≥ 2.23Λ`
  have hu0a : 2.23 * Λ ≤ u0 := by
    rw [hu0, le_div_iff₀ hLy0]
    have : 2.23 * Λ * Ly ≤ 2.23 * Λ * (12.1 * ℓ ^ 2) := mul_le_mul_of_nonneg_left hLy (by positivity)
    nlinarith
  have hu0big : 2 * 10 ^ 8 ≤ u0 := by nlinarith
  have hlog : 19.1 ≤ Real.log u0 :=
    le_trans log_2e8_ge (Real.log_le_log (by norm_num) hu0big)
  refine ⟨hu0big, ?_⟩
  have hu0p : 0 < u0 := by linarith
  rcases le_total (ℓ ^ 2) (2 * Λ) with hsmall | hbig
  · have h1 : 0.9 * u0 * 19.1 ≤ 0.9 * u0 * Real.log u0 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith
  · -- `t = log ℓ`
    set t := Real.log ℓ with ht
    have hℓ0 : 0 < ℓ := by linarith
    have ht0 : 2 ≤ t := by
      rw [ht, Real.le_log_iff_exp_le hℓ0]
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    have hlu0 : 0 < Real.log ℓu := Real.log_pos (by linarith)
    have hlu1 : Real.log ℓu ≤ t := Real.log_le_log (by linarith) hℓu2
    -- `u₀ ≥ v := 9.9ℓ²/t`
    have h4 : 0.9998 * ℓ ^ 4 ≤ ℓu ^ 4 := by
      have e1 : ℓu ^ 4 = (ℓu ^ 2) ^ 2 := by ring
      have e2 : ℓ ^ 4 = (ℓ ^ 2) ^ 2 := by ring
      rw [e1, e2]; nlinarith
    have hlh : 119.97 * ℓ ^ 4 / t ≤ lh := by
      refine le_trans ?_ h120
      rw [div_le_div_iff₀ (by linarith) hlu0]
      have : 119.97 * ℓ ^ 4 * Real.log ℓu ≤ 119.97 * ℓ ^ 4 * t :=
        mul_le_mul_of_nonneg_left hlu1 (by positivity)
      nlinarith [pow_pos hℓ0 4]
    set v := 9.9 * ℓ ^ 2 / t with hv
    have hv0 : 0 < v := by positivity
    have hu0v : v ≤ u0 := by
      rw [hv, hu0, div_le_div_iff₀ (by linarith) hLy0]
      have h5 : 119.97 * ℓ ^ 4 ≤ lh * t := by
        have := (div_le_iff₀ (by linarith : (0 : ℝ) < t)).mp hlh; linarith
      have : 9.9 * ℓ ^ 2 * Ly ≤ 9.9 * ℓ ^ 2 * (12.1 * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left hLy (by positivity)
      nlinarith
    -- `log v = log 9.9 + 2t - log t ≥ 1 + 11t/6`
    have hlog99 : 2 ≤ Real.log 9.9 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    have hlogt : Real.log t ≤ t / 6 + 1 := by
      have h6 : Real.log 6 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (2 : ℝ)
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have := Real.exp_one_gt_d9
        rw [e]; nlinarith [Real.exp_pos 1]
      have h1 : Real.log (t / 6) ≤ t / 6 - 1 := Real.log_le_sub_one_of_pos (by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h1
      linarith
    have hlogv : Real.log v = Real.log 9.9 + 2 * t - Real.log t := by
      rw [hv, Real.log_div (by positivity) (by linarith), Real.log_mul (by norm_num)
        (by positivity), Real.log_pow]
      push_cast; ring
    have hlogu0 : 1 + 11 / 6 * t ≤ Real.log u0 := by
      have := Real.log_le_log hv0 hu0v
      linarith
    have hmain : 0.9 * v * (1 + 11 / 6 * t) ≤ 0.9 * u0 * Real.log u0 := by
      have := mul_le_mul hu0v hlogu0 (by linarith) hu0p.le
      linarith
    have hv' : 0.9 * v * (1 + 11 / 6 * t) = 8.91 * ℓ ^ 2 / t + 16.335 * ℓ ^ 2 := by
      rw [hv]; field_simp; ring
    have : 0 ≤ 8.91 * ℓ ^ 2 / t := div_nonneg (by positivity) (by linarith)
    linarith

/-- **Step 5 for the θ-free window** `h = winH X₀`, `u₀ = log h / log 2y`: either the first piece
`log h = L/8` (`cond81_core` with `θ_b = 1/8`), or `L ≥ 400Λ²` and the three lower bounds
`log h ≥ 50Λ², 27Λℓ_u², 120ℓ_u⁴/log ℓ_u` (`ℓ_u = log L`). -/
theorem cond81_core_win {Λ L Lx ℓ Ly D γ lh : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hLx : Lx = Real.exp ℓ) (hLLx : Lx - 1 ≤ L) (hLLx2 : L ≤ Lx) (hLy0 : 0 < Ly)
    (hwin : lh = L / 8 ∨ (50 * Λ ^ 2 ≤ lh ∧ 27 * Λ * Real.log L ^ 2 ≤ lh ∧
      120 * Real.log L ^ 4 / Real.log (Real.log L) ≤ lh))
    (hreg : (0.3 ≤ γ ∧ γ ≤ 7.5 ∧ Ly ≤ 3.01 * γ * Λ ∧ D ≤ 1.01 * γ * Λ ∧
        122 * γ * Λ ^ 2 ≤ Lx ∧ 15 * γ ^ 2 * Λ ^ 2 ≤ Lx) ∨
      (Ly ≤ 12.1 * ℓ ^ 2 ∧ D ≤ 4.1 * ℓ ^ 2 ∧ 2886 ≤ ℓ)) :
    2 * 10 ^ 8 ≤ lh / Ly ∧ Ly + D ≤ 0.9 * (lh / Ly) * Real.log (lh / Ly) := by
  rcases hwin with heq | ⟨h50, h27, h120⟩
  · have := cond81_core (θb := 1 / 8) hΛ (by norm_num) hLx hLLx hLy0 hreg
    rw [show (1 / 8 : ℝ) * L = L / 8 by ring, ← heq] at this
    exact this
  · rcases hreg with ⟨hγ0, hγ, hLy, hD, -, -⟩ | ⟨hLy, hD, hl⟩
    · exact cond81_raised_win hΛ hLy0 hγ0 hγ hLy hD h50
    · -- `log L ∈ [ℓ - 10⁻³, ℓ]`
      have hLx0 : 0 < Lx := by rw [hLx]; exact Real.exp_pos _
      have hL0 : 0 < L := by
        have : (2 : ℝ) ≤ Lx := by
          rw [hLx]; have := Real.add_one_le_exp ℓ; linarith
        linarith
      have hu2 : Real.log L ≤ ℓ := by
        have := Real.log_le_log hL0 hLLx2; rwa [hLx, Real.log_exp] at this
      have hu1 : ℓ - 1 / 1000 ≤ Real.log L := by
        have he : Real.exp (-(1 / 1000 : ℝ)) ≤ 1 - 1 / 2000 := by
          rw [Real.exp_neg]
          have h1 := Real.add_one_le_exp (1 / 1000 : ℝ)
          rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
          nlinarith
        have hbig : 2000 ≤ Lx := by
          rw [hLx]
          have := Real.add_one_le_exp ℓ; linarith
        have h1 : Real.exp (ℓ - 1 / 1000) ≤ L := by
          rw [show ℓ - 1 / 1000 = ℓ + -(1 / 1000) by ring, Real.exp_add, ← hLx]
          nlinarith [Real.exp_pos (-(1 / 1000 : ℝ))]
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      exact cond81_std_win hΛ hl hu1 hu2 hLy0 hLy hD h27 h120

/-- `γ(s) ∈ [γ*(s_H), 7.5]` above `s_H`. -/
lemma gam_bounds_of_gt {s : ℝ} (hs : sHroot < s) : gTarget ≤ gam sHroot s ∧ gam sHroot s ≤ 7.5 := by
  refine ⟨?_, gam_le_of_gt gstar_sHroot_le hs⟩
  have := gam_monotone sHroot_le_six gstar_sHroot_le hs.le
  have e : gam sHroot sHroot = gTarget := by
    unfold gam; rw [if_pos le_rfl, gstar_sHroot]
  linarith

/-- **On and above the ramp** (`s > s_H`): `122 γ(s) ≤ e^s` and `15 γ(s)² ≤ e^s`. On the ramp
`γ(s) ≤ 0.33334 + 7.1667 t` with `t = s - 5.9745`, and `e^s ≥ 393 (1 + t + t²/2)`; above it
`γ = 7.5` and `t ≥ 1`. -/
lemma ramp_facts {s : ℝ} (hs : sHroot < s) :
    122 * gam sHroot s ≤ Real.exp s ∧ 15 * gam sHroot s ^ 2 ≤ Real.exp s := by
  obtain ⟨hlo, hhi⟩ := gam_bounds_of_gt hs
  have hsH := sHroot_mem
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  set t := s - 5.9745 with ht
  have ht0 : 0 ≤ t := by linarith [hsH.1]
  have hE : 393 * (1 + t + t ^ 2 / 2) ≤ Real.exp s := by
    have e : Real.exp s = Real.exp 5.9745 * Real.exp t := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul exp_sH_ge (Real.quadratic_le_exp_of_nonneg ht0) (by positivity)
      (by positivity)
  have hγt : gam sHroot s ≤ 0.33334 + 7.1667 * t := by
    unfold gam
    rw [if_neg (not_le.mpr hs), gstar_sHroot]
    split_ifs with h1
    · have hst : s - sHroot ≤ t := by linarith [hsH.1]
      have hst0 : 0 ≤ s - sHroot := by linarith
      have := mul_le_mul (show 7.5 - gTarget ≤ 7.1667 by rw [hg]; norm_num) hst hst0
        (by norm_num)
      rw [hg] at this ⊢; linarith
    · push_neg at h1; linarith [hsH.1]
  set γ := gam sHroot s
  have hγ0 : 0 ≤ γ := by rw [hg] at hlo; linarith
  rcases le_total t 1 with h | h
  · have htt : t ^ 2 ≤ t := by nlinarith
    have hγ2 : γ ^ 2 ≤ (0.33334 + 7.1667 * t) ^ 2 := pow_le_pow_left₀ hγ0 hγt 2
    constructor
    · nlinarith [sq_nonneg (t - 1.2248)]
    · nlinarith
  · have htt : 1 ≤ t ^ 2 := by nlinarith
    have hγ2 : γ ^ 2 ≤ 7.5 ^ 2 := pow_le_pow_left₀ hγ0 hhi 2
    constructor <;> nlinarith

/-- **The two regimes above `s_H`** (Theorem 6.23(b), Step 5). For `x ≥ X₀` with `s > s_H`, with
`K = log c`, `ℓ = log log x`, `γ = γ(s)`, `Λ = log X₀`, either
* (raised) `0 < γ ≤ 7.5`, `log 2y ≤ 3.01γΛ`, `K + 10ℓ ≤ 1.01γΛ`, `log x ≥ 393Λ²`; or
* (standard) `log 2y ≤ 12.1ℓ²`, `K + 10ℓ ≤ 4.1ℓ²`, `ℓ ≥ 2886`. -/
theorem regimes_of_gt_sH {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hs : sHroot < capS X₀ x) :
    (0 < gam sHroot (capS X₀ x) ∧ gam sHroot (capS X₀ x) ≤ 7.5 ∧
      Real.log (2 * absorbYAt X₀ x) ≤ 3.01 * gam sHroot (capS X₀ x) * Real.log X₀ ∧
      logcAt X₀ x + 10 * Real.log (Real.log x) ≤ 1.01 * gam sHroot (capS X₀ x) * Real.log X₀ ∧
      393 * Real.log X₀ ^ 2 ≤ Real.log x) ∨
    (Real.log (2 * absorbYAt X₀ x) ≤ 12.1 * Real.log (Real.log x) ^ 2 ∧
      logcAt X₀ x + 10 * Real.log (Real.log x) ≤ 4.1 * Real.log (Real.log x) ^ 2 ∧
      2886 ≤ Real.log (Real.log x)) := by
  obtain ⟨hx0, hL, hl18, hell⟩ := height_facts hX0 hX hx
  set Λ := Real.log X₀ with hΛ
  set l := Real.log (Real.log x) with hl
  set γ := gam sHroot (capS X₀ x) with hγ
  obtain ⟨hγlo, hγhi⟩ := gam_bounds_of_gt hs
  rw [← hγ] at hγlo hγhi
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  obtain ⟨h4lo, h4hi⟩ := log4_bounds
  have hKeq := logcAt_eq hX0 hX hx
  rw [← hγ, ← hl, ← hΛ] at hKeq
  have h3 := log_two_absorbYAt_le_three hX0 hX hx
  rw [← hl] at h3
  have hΛ0 : 0 < Λ := by linarith
  by_cases hreg : 4 * l ^ 2 - Real.log 4 ≤ γ * Λ
  · left
    have hK : logcAt X₀ x = γ * Λ := by rw [hKeq, max_eq_right hreg]
    have hl2 : l ^ 2 ≤ 2 * Λ := by nlinarith
    have hlin : l ≤ Λ / 10000 + 5000 := by nlinarith [sq_nonneg (l - 10000)]
    have hsmall : 10 * l + 12 ≤ 1 / 100 * γ * Λ := by rw [hg] at hγlo; nlinarith
    refine ⟨by rw [hg] at hγlo; linarith, hγhi, by rw [hK] at h3; nlinarith,
      by rw [hK]; nlinarith, ?_⟩
    -- `log x = Λ² e^s` with `e^s ≥ 393`
    have hLx : Real.log x = Λ ^ 2 * Real.exp (capS X₀ x) := by
      rw [← exp_two_log_add hΛ0, hell, hl, Real.exp_log (by linarith)]
    have hE : 393 ≤ Real.exp (capS X₀ x) :=
      le_trans exp_sH_ge (Real.exp_le_exp.mpr (by linarith [sHroot_mem.1]))
    rw [hLx]; nlinarith [sq_nonneg Λ]
  · right
    push_neg at hreg
    have hK : logcAt X₀ x = 4 * l ^ 2 - Real.log 4 := by rw [hKeq, max_eq_left hreg.le]
    have hl2 : 8330000 ≤ l ^ 2 := by rw [hg] at hγlo; nlinarith
    have hl2886 : 2886 ≤ l := by nlinarith
    have hstd := log_two_absorbYAt_le_std hX0 hX hx hK
    rw [← hl] at hstd
    refine ⟨by nlinarith, by rw [hK]; nlinarith, hl2886⟩

/-- The extra facts of the raised regime used by `cond81_core`: `γ ≥ 0.3`, and, with
`log x = Λ² e^s`, `122 γ Λ² ≤ log x` and `15 γ² Λ² ≤ log x` (`ramp_facts`). -/
lemma raised_extra {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hs : sHroot < capS X₀ x) :
    0.3 ≤ gam sHroot (capS X₀ x) ∧
    122 * gam sHroot (capS X₀ x) * Real.log X₀ ^ 2 ≤ Real.log x ∧
    15 * gam sHroot (capS X₀ x) ^ 2 * Real.log X₀ ^ 2 ≤ Real.log x := by
  obtain ⟨hx0, hL, -, hell⟩ := height_facts hX0 hX hx
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hLx : Real.log x = Real.log X₀ ^ 2 * Real.exp (capS X₀ x) := by
    rw [← exp_two_log_add hΛ0, hell, Real.exp_log (by linarith)]
  obtain ⟨hlo, -⟩ := gam_bounds_of_gt hs
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  obtain ⟨h1, h2⟩ := ramp_facts hs
  have hΛ2 : 0 ≤ Real.log X₀ ^ 2 := sq_nonneg _
  refine ⟨by rw [hg] at hlo; linarith, ?_, ?_⟩
  · rw [hLx]; nlinarith
  · rw [hLx]; nlinarith

/-- `log c` is non-decreasing in the height. -/
lemma logcAt_mono {X₀ u x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hu : X₀ ≤ u)
    (hux : u ≤ x) : logcAt X₀ u ≤ logcAt X₀ x := by
  obtain ⟨hu0, hL, hl, hell⟩ := height_facts hX0 hX hu
  have hX1 := one_lt_of_logX hX0 hX
  unfold logcAt
  refine logc_mono sHroot_le_six gstar_sHroot_le (by linarith) (by rw [hell]; linarith) ?_
  unfold capS
  have := Real.log_le_log (by linarith) (Real.log_le_log hu0 hux)
  linarith

/-- `M̄₁ ≥ 1`. -/
lemma one_le_capM1 {X₀ u : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hu : X₀ ≤ u) :
    1 ≤ capM1 X₀ u := by
  obtain ⟨-, -, hl, hell⟩ := height_facts hX0 hX hu
  unfold capM1 Mbar1
  have hr := rbar0_nonneg (Λ := Real.log X₀) (s := capS X₀ u) (by rw [hell]; linarith)
  have hc := Real.exp_pos (logc sHroot (Real.log X₀) (capS X₀ u))
  have := Real.sqrt_nonneg (Real.exp (logc sHroot (Real.log X₀) (capS X₀ u)))
  simp only
  nlinarith [mul_nonneg hr this, mul_nonneg hr (by linarith : (0 : ℝ) ≤ rbar0 (Real.log X₀) (capS X₀ u) + 1)]

/-- The constant of step (iv): `C_d = M̄₁(u) L⁶/2`, `L = log u`. -/
noncomputable def capCd (X₀ u : ℝ) : ℝ := capM1 X₀ u * Real.log u ^ 6 / 2

/-- `0 ≤ log C_d + 4 log L ≤ log c(x) + 10 log log x` for `X₀ ≤ u ≤ x ≤ 2u`. -/
lemma log_capCd_le {X₀ u x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hu : X₀ ≤ u)
    (hux : u ≤ x) :
    0 ≤ Real.log (capCd X₀ u) + 4 * Real.log (Real.log u) ∧
    Real.log (capCd X₀ u) + 4 * Real.log (Real.log u) ≤
      logcAt X₀ x + 10 * Real.log (Real.log x) := by
  obtain ⟨hu0, hL, hl, -⟩ := height_facts hX0 hX hu
  have hM1 := one_le_capM1 hX0 hX hu
  have hM2 := capM1_le_two_exp hX0 hX hu
  have hK := logcAt_mono hX0 hX hu hux
  have hLL : Real.log (Real.log u) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by linarith) (Real.log_le_log hu0 hux)
  set L := Real.log u
  have hL6 : (2 : ℝ) ≤ L ^ 6 := by
    have : (10 : ℝ) ^ 8 ≤ L := hL
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ L) 6]
  have hCd1 : 1 ≤ capCd X₀ u := by
    unfold capCd; rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  refine ⟨by have := Real.log_nonneg hCd1; linarith, ?_⟩
  have e : Real.log (capCd X₀ u) = Real.log (capM1 X₀ u) + 6 * Real.log L - Real.log 2 := by
    unfold capCd
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  have hlogM : Real.log (capM1 X₀ u) ≤ Real.log 2 + logcAt X₀ u := by
    have := Real.log_le_log (by linarith) hM2
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  rw [e]
  linarith

set_option maxHeartbeats 1600000 in
/-- **Condition (81) and the hypothesis `(∗)` of Lemma 6.26 at a window** (Theorem 6.23(b)). Let
`log X₀ ≥ 10⁸`, `X₀ ≤ u ≤ x ≤ 2u`, `L = log u`, `h = winH X₀ u` (the θ-free window), `y = y(x)`,
`C_d = M̄₁(u) L⁶/2` and `u₀ = log h / log 2y`, and suppose `2y > X₀` (which holds wherever `A`
meets the window). Then, with `u_* = log(2yh)/log 2y`:
`u_* ≥ 2·10⁸`, `log log 2y ≤ 1.79 u_*`, `log u_*/log 2y ≤ 0.31`, `1 ≤ u₀ ≤ u_*`, and (81):
`log 2y + log C_d + 4 log L ≤ 0.9 u₀ log u₀`. -/
theorem cond81_window {X₀ u x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hu : X₀ ≤ u) (hux : u ≤ x) (hx2 : x ≤ 2 * u)
    (hy : X₀ < 2 * absorbYAt X₀ x) :
    let y := absorbYAt X₀ x
    let h := Absorbed.winH X₀ u
    let us := Real.log (2 * y * h) / Real.log (2 * y)
    let u0 := Real.log h / Real.log (2 * y)
    2 * 10 ^ 8 ≤ us ∧ Real.log (Real.log (2 * y)) ≤ 1.79 * us ∧
      Real.log us / Real.log (2 * y) ≤ 0.31 ∧ 1 ≤ u0 ∧ u0 ≤ us ∧
      Real.log (2 * y) + Real.log (capCd X₀ u) + 4 * Real.log (Real.log u) ≤
        0.9 * u0 * Real.log u0 := by
  intro y h us u0
  obtain ⟨hu0, hL, hl, -⟩ := height_facts hX0 hX hu
  have hx : X₀ ≤ x := hu.trans hux
  obtain ⟨hx0, hLx, hlx, hellx⟩ := height_facts hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  set Λ := Real.log X₀ with hΛ
  set L := Real.log u with hLdef
  set ℓ := Real.log (Real.log x) with hℓ
  set Ly := Real.log (2 * y) with hLy
  set lh := Real.log h with hlhdef
  -- `s > s_H`
  have hs : sHroot < capS X₀ x := by
    by_contra hc; push_neg at hc
    have := two_absorbYAt_lt_of_le_sH hX0 hX hx hc
    linarith
  have hy1 : 1 ≤ y := one_le_absorbYAt hX0 hX hx
  have hLyΛ : Λ < Ly := Real.log_lt_log (by linarith) hy
  have hLy0 : 0 < Ly := by linarith
  -- `log(2yh) = Ly + log h`, so `u_* = 1 + u₀`
  have hh0 : 0 < h := Absorbed.winH_pos _ _
  have hlogh : lh = Absorbed.winLog Λ L := Absorbed.log_winH X₀ u
  have hus : us = 1 + u0 := by
    show Real.log (2 * y * h) / Ly = 1 + lh / Ly
    rw [Real.log_mul (by positivity) hh0.ne', add_div, div_self hLy0.ne']
  -- the window: the first piece, or the three lower bounds beyond `400Λ²`
  have hwin : lh = L / 8 ∨ (50 * Λ ^ 2 ≤ lh ∧ 27 * Λ * Real.log L ^ 2 ≤ lh ∧
      120 * Real.log L ^ 4 / Real.log (Real.log L) ≤ lh) := by
    rcases le_total L (400 * Λ ^ 2) with hle | hge
    · left; rw [hlogh, Absorbed.winLog_eq_left hX hle]
    · right; rw [hlogh]; exact Absorbed.winLog_ge hX hge
  have hlhL : lh ≤ L / 8 := by rw [hlogh]; exact Absorbed.winLog_le _ _
  -- the constants
  obtain ⟨hD0, hD⟩ := log_capCd_le hX0 hX hu hux
  set D := Real.log (capCd X₀ u) + 4 * Real.log L with hDdef
  have hLx_exp : Real.log x = Real.exp ℓ := (Real.exp_log (by linarith)).symm
  have hLLx : Real.log x - 1 ≤ L := by
    have h2 := Real.log_le_log hx0 hx2
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    have : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hLLx2 : L ≤ Real.log x := Real.log_le_log hu0 hux
  have hcore := cond81_core_win (Λ := Λ) (L := L) (Lx := Real.log x) (ℓ := ℓ) (Ly := Ly)
    (D := D) (γ := gam sHroot (capS X₀ x)) (lh := lh) hX hLx_exp hLLx hLLx2 hLy0 hwin (by
      rcases regimes_of_gt_sH hX0 hX hx hs with ⟨-, h2, h3, h4, -⟩ | ⟨h1, h2, h3⟩
      · obtain ⟨e1, e2, e3⟩ := raised_extra hX0 hX hx hs
        exact Or.inl ⟨e1, h2, h3, hD.trans h4, e2, e3⟩
      · exact Or.inr ⟨h1, hD.trans h2, h3⟩)
  obtain ⟨hu0big, h81⟩ := hcore
  have hu0e : u0 = lh / Ly := rfl
  rw [← hu0e] at hu0big h81
  have hu0pos : 0 < u0 := by linarith
  refine ⟨by rw [hus]; linarith, ?_, ?_, by linarith, by rw [hus]; linarith, by linarith⟩
  · -- `log log 2y ≤ 1.79 u_*`
    have hlogu0 : Real.log u0 ≤ u0 := by
      have := Real.log_le_sub_one_of_pos hu0pos; linarith
    have hlogu0' : 0 ≤ Real.log u0 := Real.log_nonneg (by linarith)
    have hLyu : Ly ≤ u0 ^ 2 := by nlinarith
    have h1 : Real.log Ly ≤ 2 * Real.log u0 := by
      have := Real.log_le_log hLy0 hLyu
      rwa [Real.log_pow] at this
    have h2 := log_le_eighth hu0pos
    rw [hus]; push_cast at h1; linarith
  · -- `log u_*/log 2y ≤ 0.31`
    have hθL : lh ≤ L := by linarith
    have hLΛ : Λ ≤ L := Real.log_le_log (by linarith) hu
    have hΛ0 : 0 < Λ := by linarith
    have hL0 : 0 ≤ L := by linarith
    have hA : u0 ≤ L / Λ :=
      calc u0 = lh / Ly := hu0e
        _ ≤ L / Ly := div_le_div_of_nonneg_right hθL hLy0.le
        _ ≤ L / Λ := div_le_div_of_nonneg_left hL0 hΛ0 hLyΛ.le
    have hB : L / Λ ≤ L / 2 := div_le_div_of_nonneg_left hL0 (by norm_num) (by linarith)
    have hus1 : us ≤ L := by rw [hus]; linarith
    have hus0 : 1 ≤ us := by rw [hus]; linarith
    have hlogus : Real.log us ≤ ℓ := by
      calc Real.log us ≤ Real.log L := Real.log_le_log (by linarith) hus1
        _ ≤ ℓ := Real.log_le_log (by linarith) (Real.log_le_log hu0 hux)
    have hlogus0 : 0 ≤ Real.log us := Real.log_nonneg hus0
    have hLy8 : 8 * ℓ ^ 2 ≤ Ly := by
      have h1 := log_absorbYAt_ge hX0 hX hx
      have h2 : Real.log y ≤ Ly := by
        rw [hLy, Real.log_mul (by norm_num) (by linarith)]
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
      linarith
    have hkey : ℓ ≤ 0.31 * Ly := by
      by_cases hc : ℓ ≤ 0.31 * Λ
      · linarith
      · have h18 : (18 : ℝ) ≤ ℓ := hlx
        have : ℓ ≤ 2.48 * ℓ ^ 2 := by nlinarith
        linarith
    exact (div_le_iff₀ hLy0).mpr (by linarith)

/-- `(log v)^{11} ≤ h(v)` for the window `h = winH X₀`, `log v ≥ 10⁸`, `log X₀ ≥ 10⁸`: on the
first piece `h = v^{1/8} ≥ v^{1/20}`, beyond it `log h ≥ 120ℓ⁴/log ℓ ≥ 11ℓ`. -/
lemma log_pow_le_winH {X₀ v : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) (hv0 : 0 < v)
    (hv : 10 ^ 8 ≤ Real.log v) : Real.log v ^ 11 ≤ Absorbed.winH X₀ v := by
  set L := Real.log v with hL
  have hL0 : 0 < L := by linarith
  have hv1 : 1 ≤ v := by
    by_contra hc; push_neg at hc
    have := Real.log_nonpos hv0.le hc.le; linarith
  rcases le_total L (400 * Real.log X₀ ^ 2) with hle | hge
  · rw [Absorbed.winH_eq_rpow hX hv0 hle]
    have h1 : v ^ (1 / 20 : ℝ) ≤ v ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
    have h2 : v ^ (1 / 20 : ℝ) = Real.exp (L / 220) ^ 11 := by
      rw [Real.rpow_def_of_pos hv0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : L ≤ Real.exp (L / 220) := by
      have := Real.pow_div_factorial_le_exp (L / 220) (by positivity) 2
      simp [Nat.factorial] at this
      nlinarith
    have h4 : L ^ 11 ≤ Real.exp (L / 220) ^ 11 := pow_le_pow_left₀ (by linarith) h3 11
    linarith
  · have hge' := (Absorbed.winLog_ge hX hge).2.2
    set ℓ := Real.log L with hℓ
    have hℓ1 : 1 ≤ ℓ := by
      rw [hℓ, Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
    have hlℓ0 : 0 < Real.log ℓ := by
      apply Real.log_pos
      rw [hℓ, Real.lt_log_iff_exp_lt hL0]; have := Real.exp_one_lt_d9
      have : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr (by linarith)
      have h3 : Real.exp 3 < 21 := by
        have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
              pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
          _ < 21 := by norm_num
      linarith
    have hlℓ : Real.log ℓ ≤ ℓ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ℓ); linarith
    have h11 : 11 * ℓ ≤ 120 * ℓ ^ 4 / Real.log ℓ := by
      rw [le_div_iff₀ hlℓ0]
      have : 11 * ℓ * Real.log ℓ ≤ 11 * ℓ * ℓ := mul_le_mul_of_nonneg_left hlℓ (by positivity)
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hℓ1 2]
    have hlogh := Absorbed.log_winH X₀ v
    rw [← hL] at hlogh
    have : Real.log (L ^ 11) ≤ Real.log (Absorbed.winH X₀ v) := by
      rw [Real.log_pow, hlogh]; push_cast; linarith
    exact (Real.log_le_log_iff (by positivity) (Absorbed.winH_pos _ _)).mp this

/-- `log 2y ≤ λ(log x) = max(22.6Λ, 12ℓ² + 9ℓ + 8)` above `s_H` (Section 2.2, proof of
Lemma 4.4). -/
theorem log_two_absorbYAt_le_lambda {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) (hs : sHroot < capS X₀ x) :
    Real.log (2 * absorbYAt X₀ x) ≤ RankinMinorant.rankinLambda (Real.log X₀) (Real.log x) := by
  obtain ⟨hx0, hL, hl18, hell⟩ := height_facts hX0 hX hx
  set Λ := Real.log X₀ with hΛ
  set l := Real.log (Real.log x) with hl
  obtain ⟨hγlo, hγhi⟩ := gam_bounds_of_gt hs
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  obtain ⟨h4lo, h4hi⟩ := log4_bounds
  have hKeq := logcAt_eq hX0 hX hx
  rw [← hl, ← hΛ] at hKeq
  unfold RankinMinorant.rankinLambda
  rw [← hl]
  by_cases hreg : 4 * l ^ 2 - Real.log 4 ≤ gam sHroot (capS X₀ x) * Λ
  · apply le_max_of_le_left
    have hK : logcAt X₀ x = gam sHroot (capS X₀ x) * Λ := by rw [hKeq, max_eq_right hreg]
    have h3 := log_two_absorbYAt_le_three hX0 hX hx
    rw [← hl, hK] at h3
    have hl2 : l ^ 2 ≤ 2 * Λ := by nlinarith
    have hlin : l ≤ Λ / 10000 + 5000 := by nlinarith [sq_nonneg (l - 10000)]
    nlinarith
  · apply le_max_of_le_right
    push_neg at hreg
    have hK : logcAt X₀ x = 4 * l ^ 2 - Real.log 4 := by rw [hKeq, max_eq_left hreg.le]
    have hstd := log_two_absorbYAt_le_std hX0 hX hx hK
    rw [← hl] at hstd
    linarith

set_option maxHeartbeats 1600000 in
/-- **The hypotheses `(∗)` of the Rankin bound for `A` (proof of Lemma 4.4)**, with `Y = x` and
`y = y(x)`, wherever `2y > X₀` (that is, wherever `A ∩ [1, x] ≠ ∅`): with `u = log x/log 2y`,
`u ≥ 2·10⁸`, `log log 2y ≤ 1.79u`, `log u/log 2y ≤ 0.31` and `log 2y ≤ λ(log x)`. -/
theorem rankin_conditions {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hy : X₀ < 2 * absorbYAt X₀ x) :
    2 * 10 ^ 8 ≤ Real.log x / Real.log (2 * absorbYAt X₀ x) ∧
    Real.log (Real.log (2 * absorbYAt X₀ x)) ≤
      1.79 * (Real.log x / Real.log (2 * absorbYAt X₀ x)) ∧
    Real.log (Real.log x / Real.log (2 * absorbYAt X₀ x)) / Real.log (2 * absorbYAt X₀ x) ≤ 0.31 ∧
    Real.log (2 * absorbYAt X₀ x) ≤ RankinMinorant.rankinLambda (Real.log X₀) (Real.log x) := by
  obtain ⟨hx0, hLx, hlx, hellx⟩ := height_facts hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  set Λ := Real.log X₀ with hΛ
  set L := Real.log x with hLdef
  set ℓ := Real.log L with hℓ
  set Ly := Real.log (2 * absorbYAt X₀ x) with hLy
  have hs : sHroot < capS X₀ x := by
    by_contra hc; push_neg at hc
    have := two_absorbYAt_lt_of_le_sH hX0 hX hx hc
    linarith
  have hy1 : 1 ≤ absorbYAt X₀ x := one_le_absorbYAt hX0 hX hx
  have hLyΛ : Λ < Ly := Real.log_lt_log (by linarith) hy
  have hLy0 : 0 < Ly := by linarith
  have hLx_exp : L = Real.exp ℓ := (Real.exp_log (by linarith)).symm
  have hcore := cond81_core (Λ := Λ) (θb := 1) (L := L) (Lx := L) (ℓ := ℓ) (Ly := Ly)
    (D := 0) (γ := gam sHroot (capS X₀ x)) hX (by norm_num) hLx_exp (by linarith) hLy0 (by
      rcases regimes_of_gt_sH hX0 hX hx hs with ⟨-, h2, h3, h4, -⟩ | ⟨h1, h2, h3⟩
      · obtain ⟨e1, e2, e3⟩ := raised_extra hX0 hX hx hs
        exact Or.inl ⟨e1, h2, h3, by positivity, e2, e3⟩
      · exact Or.inr ⟨h1, by positivity, h3⟩)
  rw [one_mul] at hcore
  obtain ⟨hubig, hR⟩ := hcore
  set u := L / Ly with hu
  have hupos : 0 < u := by linarith
  refine ⟨hubig, ?_, ?_, log_two_absorbYAt_le_lambda hX0 hX hx hs⟩
  · have hlogu : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hupos; linarith
    have hlogu' : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hLyu : Ly ≤ u ^ 2 := by nlinarith
    have h1 : Real.log Ly ≤ 2 * Real.log u := by
      have := Real.log_le_log hLy0 hLyu
      rwa [Real.log_pow] at this
    have h2 := log_le_eighth hupos
    push_cast at h1; linarith
  · have hΛ0 : 0 < Λ := by linarith
    have hL0 : 0 ≤ L := by linarith
    have hA : u ≤ L / Λ := div_le_div_of_nonneg_left hL0 hΛ0 hLyΛ.le
    have hB : L / Λ ≤ L / 2 := div_le_div_of_nonneg_left hL0 (by norm_num) (by linarith)
    have hu1 : u ≤ L := by linarith
    have hlogu : Real.log u ≤ ℓ := Real.log_le_log hupos hu1
    have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hLy8 : 8 * ℓ ^ 2 ≤ Ly := by
      have h1 := log_absorbYAt_ge hX0 hX hx
      have h2 : Real.log (absorbYAt X₀ x) ≤ Ly := by
        rw [hLy, Real.log_mul (by norm_num) (by linarith)]
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
      linarith
    have hkey : ℓ ≤ 0.31 * Ly := by
      by_cases hc : ℓ ≤ 0.31 * Λ
      · linarith
      · have h18 : (18 : ℝ) ≤ ℓ := hlx
        have : ℓ ≤ 2.48 * ℓ ^ 2 := by nlinarith
        linarith
    exact (div_le_iff₀ hLy0).mpr (by linarith)

end Construction

end
