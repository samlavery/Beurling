module

public import RequestProject.Beurling.Construction.JitterRegular
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# (R_H) for the jitter width: `H(y) ≤ (y/x)^{4·10⁻⁶} H(x)` for `X₀ ≤ x ≤ y`

Theorem 6.23(c) (05-queue.tex, Step 6 "Derivative"), in difference form. For
`X₀ ≤ x ≤ y` with `Δ = log y - log x ≤ 1`, `log H(y) ≤ log H(x) + 4·10⁻⁶ Δ` (`capH_local`):

* the standard part `H_std = e^{8ℓ²}`: `8(ℓ_y² - ℓ_x²) ≤ 8 (Δ/L)(2ℓ + 1) ≤ 4·10⁻⁶ Δ`
  (`std_step`; the paper's `16ℓ/L`);
* the raised part `M̄₁²`, when `M̄₁(y)² > H_std(y)`: then `log c(y) = γ(s_y) Λ` (as `M̄₁ ≤ 2c`),
  and by dominance `γ* Λ ≤ 1.5·10⁻⁷ L` (`gstar_ratio`, the paper's
  `γ*Λ/L ≤ 1.7 A_s(A_s+1)/(ℓ_s² Λ_s)`), so with `γ*(t) ≤ γ*(s)(1 + 4(t - s))` (`G_lip`) the
  increase of `log c` is `≤ 6.1·10⁻⁷ Δ`; on the ramp `γ` is `8`-Lipschitz (`gam_lip`) and
  `Λ/L ≤ e^{-s_H}/Λ` is negligible. The `r̄₀`-terms of `M̄₁` are `≤ 10⁻⁹ c` (as `c ≥ e^{4ℓ²}/4`).

Chaining over steps of length `≤ 1` in `log` gives `KR.WidthReal.CapHSlope X₀ (4·10⁻⁶)`
(`capHSlope`).
-/

@[expose] public section

open Real CaplLink BSCert.Capl

namespace CapHSlopeProof

/-! ### Numerics -/

lemma exp_one_pow_ge {n : ℕ} (c : ℝ) (hc : c ≤ 2.7182818283 ^ n) : c ≤ Real.exp n := by
  have he := Real.exp_one_gt_d9
  have : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact hc.trans (pow_le_pow_left₀ (by norm_num) he.le n)

lemma exp30_ge : (10 : ℝ) ^ 12 ≤ Real.exp 30 := by
  have := exp_one_pow_ge (n := 30) ((10 : ℝ) ^ 12) (by norm_num)
  simpa using this

lemma log_1e8_le : Real.log ((10 : ℝ) ^ 8) ≤ 37 / 2 := by
  have h := exp_one_pow_ge (n := 37) ((10 : ℝ) ^ 16) (by norm_num)
  have h' : (10 : ℝ) ^ 16 ≤ Real.exp 37 := by
    have e37 : ((37 : ℕ) : ℝ) = 37 := by norm_num
    rw [e37] at h; exact h
  have h2 : Real.log ((10 : ℝ) ^ 16) ≤ 37 := by
    rw [Real.log_le_iff_le_exp (by positivity)]; exact h'
  have e : Real.log ((10 : ℝ) ^ 16) = 2 * Real.log ((10 : ℝ) ^ 8) := by
    rw [show (10 : ℝ) ^ 16 = ((10 : ℝ) ^ 8) ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [e] at h2
  set t := Real.log ((10 : ℝ) ^ 8)
  linarith

/-- `log L ≤ 17.5 + L/10⁸` (tangent bound at `10⁸`). -/
lemma log_le_lin8 {L : ℝ} (hL : 0 < L) : Real.log L ≤ 17.5 + L / 10 ^ 8 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 10 ^ 8 by positivity)
  rw [Real.log_div hL.ne' (by norm_num)] at h
  have := log_1e8_le
  linarith

/-! ### The standard part -/

/-- **The standard part** (`H_std = e^{8ℓ²}`, `d log H_std/dL = 16ℓ/L`): for `10⁸ ≤ L_x ≤ L_y`,
`L_y - L_x ≤ 1`, `8 ℓ_y² ≤ 8 ℓ_x² + 4·10⁻⁶ (L_y - L_x)`. -/
lemma std_step {Lx Ly : ℝ} (hL : 10 ^ 8 ≤ Lx) (hxy : Lx ≤ Ly) (hΔ : Ly - Lx ≤ 1) :
    8 * Real.log Ly ^ 2 ≤ 8 * Real.log Lx ^ 2 + 4 / 1000000 * (Ly - Lx) := by
  have hLx0 : 0 < Lx := by linarith
  set Δ := Ly - Lx with hΔdef
  have hΔ0 : 0 ≤ Δ := by linarith
  set ℓx := Real.log Lx
  set ℓy := Real.log Ly
  have hδ : ℓy - ℓx ≤ Δ / Lx := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < Ly) hLx0)
    rw [Real.log_div (by linarith) hLx0.ne'] at h
    have : Ly / Lx - 1 = Δ / Lx := by rw [hΔdef]; field_simp
    linarith
  have hδ0 : 0 ≤ ℓy - ℓx := by have := Real.log_le_log hLx0 hxy; linarith
  have hℓx : ℓx ≤ 17.5 + Lx / 10 ^ 8 := log_le_lin8 hLx0
  have hℓx0 : 0 ≤ ℓx := Real.log_nonneg (by linarith)
  have hδ1 : ℓy - ℓx ≤ 1 := by
    refine hδ.trans ?_
    rw [div_le_one hLx0]; linarith
  have hkey : 8 * (2 * ℓx + 1) ≤ 4 / 1000000 * Lx := by nlinarith
  have e : 8 * ℓy ^ 2 - 8 * ℓx ^ 2 = 8 * (ℓy - ℓx) * (2 * ℓx + (ℓy - ℓx)) := by ring
  have h1 : 8 * (ℓy - ℓx) * (2 * ℓx + (ℓy - ℓx)) ≤ 8 * (Δ / Lx) * (2 * ℓx + 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hδ (by norm_num)) (by linarith) (by positivity)
      (by positivity)
  have h2 : 8 * (Δ / Lx) * (2 * ℓx + 1) = Δ * (8 * (2 * ℓx + 1)) / Lx := by ring
  have h3 : Δ * (8 * (2 * ℓx + 1)) / Lx ≤ 4 / 1000000 * Δ := by
    rw [div_le_iff₀ hLx0]; nlinarith
  linarith

/-! ### The dominance bound -/

set_option maxHeartbeats 1000000 in
/-- **`γ* Λ ≤ 1.5·10⁻⁷ L` where `γ*` dominates** (Theorem 6.23(c), Step 6, third item):
if `γ*(s) Λ ≥ 4ℓ² - log 2`, `ℓ = 2 log Λ + s`, `L = e^ℓ`, then
`γ*Λ/L ≤ γ*²/((4ℓ² - log 2) e^s) ≤ 6.76 A_s(A_s+1)/(3.9 ℓ² (Λ_s - A_s - 1)) ≤ 1.5·10⁻⁷`. -/
lemma gstar_ratio {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hsΛ : -Real.log Λ ≤ s) (hs6 : s ≤ 6)
    (hdom : 4 * (2 * Real.log Λ + s) ^ 2 - Real.log 2 ≤ gstar s * Λ) :
    gstar s * Λ ≤ 15 / 100000000 * Real.exp (2 * Real.log Λ + s) := by
  set Λs := LamS s with hΛsdef
  have hΛs : 100000000 ≤ Λs := LamS_ge s
  have hsΛs : -Real.log Λs ≤ s := neg_log_LamS_le s
  have hΛ0 : 0 < Λ := by linarith
  have hΛs0 : 0 < Λs := by linarith
  have hΛsΛ : Λs ≤ Λ := by
    rw [hΛsdef]; unfold LamS
    refine max_le hΛ ?_
    calc Real.exp (-s) ≤ Real.exp (Real.log Λ) := Real.exp_le_exp.mpr (by linarith)
      _ = Λ := Real.exp_log hΛ0
  have hLΛ := log_ge_18 hΛ
  have hLΛs := log_ge_18 hΛs
  set ℓ := 2 * Real.log Λ + s with hℓ
  set ℓs := 2 * Real.log Λs + s with hℓs
  have hℓ18 : 18 ≤ ℓ := by linarith
  have hℓs18 : 18 ≤ ℓs := by linarith
  have hℓsℓ : ℓs ≤ ℓ := by have := Real.log_le_log hΛs0 hΛsΛ; linarith
  set a := A Λs s with ha
  have hA6 : 6 ≤ a := A_ge_six hΛs hsΛs
  have hAup : a ≤ 3 * Real.log Λs + 13 := A_le_lin hΛs hsΛs hs6
  have hA2 : a ≤ 2 * ℓs := by
    rw [ha, A_eq hΛs0 (by linarith)]
    have : 0 ≤ Real.log ℓs := Real.log_nonneg (by linarith)
    have := Real.log_two_lt_d9
    linarith
  have hlog8 := log_le_eighth hΛs0
  set D := Λs - a - 1 with hD
  have hD2 : Λs / 2 ≤ D := by rw [hD]; linarith
  have hD0 : 0 < D := by linarith
  -- `γ*² = 6.76 a(a+1) e^s/D`
  have hG := G_eq_sqrt (Λ := Λs) (s := s) (by linarith) hD0
  set X := a * (a + 1) * Real.exp s / D with hX
  have hX0 : 0 ≤ X := by positivity
  have hγ : gstar s = 1.3 * (2 * Real.sqrt X) := by
    unfold gstar; rw [← hΛsdef, hG]
  have hγ0 : 0 ≤ gstar s := by rw [hγ]; positivity
  have hγ2 : gstar s ^ 2 = 6.76 * X := by
    rw [hγ, mul_pow, mul_pow, Real.sq_sqrt hX0]; ring
  -- `X ≤ 2.06 · 8 ℓ² e^s/Λs`
  have hes := Real.exp_pos s
  have hXb : X ≤ 8.24 * ℓ ^ 2 * Real.exp s / Λs := by
    rw [hX, div_le_div_iff₀ hD0 hΛs0]
    have h1 : a * (a + 1) ≤ 2 * ℓ * (2 * ℓ + 1) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : 2 * ℓ * (2 * ℓ + 1) ≤ 4.12 * ℓ ^ 2 := by nlinarith
    have hes0 := hes.le
    calc a * (a + 1) * Real.exp s * Λs ≤ (4.12 * ℓ ^ 2) * Real.exp s * Λs := by
          have := h1.trans h2
          have hp : 0 ≤ Real.exp s * Λs := by positivity
          nlinarith
      _ ≤ (4.12 * ℓ ^ 2) * Real.exp s * (2 * D) := by
          have hp : 0 ≤ 4.12 * ℓ ^ 2 * Real.exp s := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 8.24 * ℓ ^ 2 * Real.exp s * D := by ring
  -- dominance: `3.9 ℓ² ≤ γ* Λ`
  have hdom' : 3.9 * ℓ ^ 2 ≤ gstar s * Λ := by
    have := Real.log_two_lt_d9
    nlinarith
  have hγpos : 0 < gstar s := by
    rcases hγ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdom'; nlinarith
  -- `γ*² ≤ 6.76 · 8.24 ℓ² e^s/Λs ≤ 1.43·10⁻⁷ γ* Λ e^s`
  have hk : gstar s ^ 2 ≤ 15 / 100000000 * (gstar s * Λ * Real.exp s) := by
    rw [hγ2]
    set P := ℓ ^ 2 * Real.exp s with hP
    have hP0 : 0 ≤ P := by positivity
    have hXP : X ≤ 8.24 * P / Λs := by
      have e : 8.24 * ℓ ^ 2 * Real.exp s / Λs = 8.24 * P / Λs := by rw [hP]; ring
      rw [← e]; exact hXb
    have h2 : 6.76 * (8.24 * P / Λs) ≤ 15 / 100000000 * (3.9 * P) := by
      rw [show 6.76 * (8.24 * P / Λs) = (6.76 * 8.24 * P) / Λs by ring, div_le_iff₀ hΛs0]
      have := mul_le_mul_of_nonneg_left hΛs hP0
      linarith
    have h3 : 3.9 * P ≤ gstar s * Λ * Real.exp s := by
      have := mul_le_mul_of_nonneg_right hdom' hes.le
      rw [hP]; linarith
    nlinarith
  have hk2 : gstar s ≤ 15 / 100000000 * (Λ * Real.exp s) := by
    have : gstar s * gstar s ≤ gstar s * (15 / 100000000 * (Λ * Real.exp s)) := by nlinarith
    exact le_of_mul_le_mul_left this hγpos
  have he : Real.exp ℓ = Λ ^ 2 * Real.exp s := by
    rw [hℓ, Real.exp_add, show 2 * Real.log Λ = Real.log Λ * 2 by ring, Real.exp_mul,
      Real.exp_log hΛ0]
    norm_cast
  rw [he]
  nlinarith

/-! ### The local step -/

variable {X₀ : ℕ}

/-- `M̄₁` in its expanded form. -/
lemma capM1_eq (x : ℝ) : capM1 X₀ x =
    rbar0 (Real.log X₀) (capS X₀ x) + (Real.exp (logc sHroot (Real.log X₀) (capS X₀ x)) +
      rbar0 (Real.log X₀) (capS X₀ x) *
        Real.sqrt (Real.exp (logc sHroot (Real.log X₀) (capS X₀ x))) +
      rbar0 (Real.log X₀) (capS X₀ x) * (rbar0 (Real.log X₀) (capS X₀ x) + 1) / 2) + 1 := rfl

/-- `√c ≥ 8·10⁹ L²` when `log c ≥ 4ℓ² - log 4`, `L = e^ℓ`, `ℓ ≥ 18` (`c ≥ H_std^{1/2}/4`). -/
lemma sqrt_c_big {ℓ c : ℝ} (hℓ : 18 ≤ ℓ) (hc : Real.exp (4 * ℓ ^ 2 - Real.log 4) ≤ c) :
    8 * 10 ^ 9 * Real.exp ℓ ^ 2 ≤ Real.sqrt c := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e1 : Real.exp (4 * ℓ ^ 2 - Real.log 4) = Real.exp (2 * ℓ ^ 2 - Real.log 2) ^ 2 := by
    rw [← Real.exp_nat_mul, hlog4]; push_cast; ring_nf
  have h1 : Real.exp (2 * ℓ ^ 2 - Real.log 2) ≤ Real.sqrt c := by
    have := Real.sqrt_le_sqrt hc
    rwa [e1, Real.sqrt_sq (Real.exp_pos _).le] at this
  have e2 : Real.exp (2 * ℓ ^ 2 - Real.log 2) =
      Real.exp ℓ ^ 2 * Real.exp (2 * ℓ ^ 2 - 2 * ℓ - Real.log 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hl2 := Real.log_two_lt_d9
  have h3 : (10 : ℝ) ^ 12 ≤ Real.exp (2 * ℓ ^ 2 - 2 * ℓ - Real.log 2) :=
    exp30_ge.trans (Real.exp_le_exp.mpr (by nlinarith))
  have h4 : 0 ≤ Real.exp ℓ ^ 2 := by positivity
  have h5 : Real.exp ℓ ^ 2 * 10 ^ 12 ≤ Real.exp ℓ ^ 2 *
      Real.exp (2 * ℓ ^ 2 - 2 * ℓ - Real.log 2) := mul_le_mul_of_nonneg_left h3 h4
  linarith

/-- **On the raised range `log c = γ(s) Λ`** (Theorem 6.23(c), Step 6, "Derivative"): if
`M̄₁² > H_std`, then `log c > 4ℓ² - log 2` (as `M̄₁ ≤ 2c`), so the `γ`-term is the maximum. -/
lemma logc_raised {Λ s : ℝ} (hℓ : 18 ≤ 2 * Real.log Λ + s)
    (hraise : Real.exp (8 * (2 * Real.log Λ + s) ^ 2) < Mbar1 sHroot Λ s ^ 2) :
    4 * (2 * Real.log Λ + s) ^ 2 - Real.log 2 < logc sHroot Λ s ∧
      logc sHroot Λ s = gam sHroot s * Λ := by
  set ℓ := 2 * Real.log Λ + s with hℓdef
  have hM := Mbar1_le (sH := sHroot) hℓ
  have hM0 : 0 ≤ Mbar1 sHroot Λ s := by
    have := rbar0_nonneg (Λ := Λ) (s := s) (by linarith)
    unfold Mbar1; simp only; positivity
  have h1 : Real.exp (8 * ℓ ^ 2) < Real.exp (2 * Real.log 2 + 2 * logc sHroot Λ s) := by
    calc Real.exp (8 * ℓ ^ 2) < Mbar1 sHroot Λ s ^ 2 := hraise
      _ ≤ (2 * Real.exp (logc sHroot Λ s)) ^ 2 := pow_le_pow_left₀ hM0 hM 2
      _ = Real.exp (2 * Real.log 2 + 2 * logc sHroot Λ s) := by
        rw [show 2 * Real.log 2 + 2 * logc sHroot Λ s = (Real.log 2 + logc sHroot Λ s) +
          (Real.log 2 + logc sHroot Λ s) by ring, Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num)]
        ring
  have h2 := Real.exp_lt_exp.mp h1
  have hlt : 4 * ℓ ^ 2 - Real.log 2 < logc sHroot Λ s := by linarith
  refine ⟨hlt, ?_⟩
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  unfold logc at hlt ⊢
  rw [← hℓdef] at hlt ⊢
  rcases le_total (4 * ℓ ^ 2 - Real.log 4) (gam sHroot s * Λ) with h | h
  · exact max_eq_right h
  · rw [max_eq_left h] at hlt; linarith

set_option maxHeartbeats 1000000 in
/-- **The increase of `log c` over a step** (Theorem 6.23(c), Step 6): on the raised range at
`s_y`, `log c(s_y) - log c(s_x) ≤ 6.1·10⁻⁷ Δ` for `s_y - s_x ≤ Δ/L_x`. Below `s_H` from
`γ*(t) ≤ γ*(s)(1 + 4(t - s))` and dominance (`gstar_ratio`); on the ramp from `gam_lip` and
`Λ/L ≤ e^{-5}/Λ`. -/
lemma logc_incr {Λ sx sy Δ : ℝ} (hΛ : 100000000 ≤ Λ) (hsx : -Real.log Λ ≤ sx)
    (hsxy : sx ≤ sy) (hΔ0 : 0 ≤ Δ) (hδ : sy - sx ≤ Δ / Real.exp (2 * Real.log Λ + sx))
    (hδ' : sy - sx ≤ 1 / 1000)
    (hLy : Real.exp (2 * Real.log Λ + sy) ≤ Real.exp (2 * Real.log Λ + sx) + 1)
    (hraise : 4 * (2 * Real.log Λ + sy) ^ 2 - Real.log 2 < logc sHroot Λ sy)
    (heq : logc sHroot Λ sy = gam sHroot sy * Λ) :
    logc sHroot Λ sy - logc sHroot Λ sx ≤ 61 / 10 ^ 8 * Δ := by
  set Lx := Real.exp (2 * Real.log Λ + sx) with hLxdef
  set Ly := Real.exp (2 * Real.log Λ + sy) with hLydef
  have hΛ0 : 0 < Λ := by linarith
  have hLΛ := log_ge_18 hΛ
  have hLx0 : 0 < Lx := Real.exp_pos _
  have hLxΛ : Λ ≤ Lx := by
    rw [hLxdef, ← Real.exp_log hΛ0]
    exact Real.exp_le_exp.mpr (by rw [Real.exp_log hΛ0]; linarith)
  have hsH := sHroot_mem
  have hgH : gstar sHroot = 1 / 3 - 1 / 100000 := by rw [gstar_sHroot]; rfl
  have hcxge : gam sHroot sx * Λ ≤ logc sHroot Λ sx := le_max_right _ _
  rw [heq]
  refine (sub_le_sub_left hcxge _).trans ?_
  rw [← sub_mul]
  rcases le_or_gt sy sHroot with hyH | hyH
  · have hxH : sx ≤ sHroot := hsxy.trans hyH
    have egy : gam sHroot sy = gstar sy := by unfold gam; rw [if_pos hyH]
    have egx : gam sHroot sx = gstar sx := by unfold gam; rw [if_pos hxH]
    rw [egy, egx]
    have hlip := G_lip hsxy (by linarith [hsH.2]) hδ'
    have hlip' : gstar sy ≤ gstar sx * (1 + 4 * (sy - sx)) := by
      unfold gstar
      have : G (LamS sy) sy * 1.3 ≤ G (LamS sx) sx * (1 + 4 * (sy - sx)) * 1.3 :=
        mul_le_mul_of_nonneg_right hlip (by norm_num)
      linarith
    have hmo : gstar sx ≤ gstar sy := gstar_mono hsxy (by linarith [hsH.2])
    have hdom : 4 * (2 * Real.log Λ + sy) ^ 2 - Real.log 2 ≤ gstar sy * Λ := by
      rw [← egy, ← heq]; exact hraise.le
    have hrat := gstar_ratio hΛ (by linarith) (by linarith [hsH.2]) hdom
    rw [← hLydef] at hrat
    have hgx0 : 0 ≤ gstar sx := by unfold gstar G; positivity
    have hd0 : 0 ≤ sy - sx := by linarith
    have h0 : gstar sy - gstar sx ≤ 4 * (sy - sx) * gstar sy := by nlinarith
    have h1 : (gstar sy - gstar sx) * Λ ≤ 4 * (sy - sx) * (gstar sy * Λ) := by
      have := mul_le_mul_of_nonneg_right h0 hΛ0.le
      linarith
    have h2 : 4 * (sy - sx) * (gstar sy * Λ) ≤ 4 * (Δ / Lx) * (15 / 100000000 * Ly) := by
      have hgy0 : 0 ≤ gstar sy * Λ := by nlinarith
      exact mul_le_mul (by linarith) hrat hgy0 (by positivity)
    have h3 : 4 * (Δ / Lx) * (15 / 100000000 * Ly) ≤ 61 / 10 ^ 8 * Δ := by
      rw [show 4 * (Δ / Lx) * (15 / 100000000 * Ly) = Δ * (60 / 100000000 * Ly) / Lx by ring,
        div_le_iff₀ hLx0]
      have : Δ * Ly ≤ Δ * (Lx + 1) := mul_le_mul_of_nonneg_left hLy hΔ0
      have : Δ * 1 ≤ Δ * Lx / 100000000 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      nlinarith
    linarith
  · have hlip := gam_lip (sH := sHroot) (s := sx) (t := sy) (by linarith [hsH.2])
      (by rw [hgH]; norm_num) (by rw [hgH]; norm_num) hsxy hδ'
    have hsx5 : 5 ≤ sx := by linarith [hsH.1]
    have hLxe : Λ ^ 2 * Real.exp 5 ≤ Lx := by
      rw [hLxdef, Real.exp_add, show 2 * Real.log Λ = Real.log Λ * 2 by ring,
        Real.exp_mul, Real.exp_log hΛ0]
      norm_cast
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsx5) (by positivity)
    have he5 : (100 : ℝ) ≤ Real.exp 5 := by
      have := exp_one_pow_ge (n := 5) (100 : ℝ) (by norm_num); simpa using this
    have h1 : (gam sHroot sy - gam sHroot sx) * Λ ≤ 8 * (Δ / Lx) * Λ :=
      mul_le_mul_of_nonneg_right (hlip.trans (by linarith)) hΛ0.le
    have h3 : 100 * Λ ^ 2 ≤ Lx := le_trans (by nlinarith) hLxe
    have h4 : 8 * Λ ≤ 61 / 10 ^ 8 * Lx := by nlinarith
    have h2 : 8 * (Δ / Lx) * Λ ≤ 61 / 10 ^ 8 * Δ := by
      rw [show 8 * (Δ / Lx) * Λ = Δ * (8 * Λ) / Lx by ring, div_le_iff₀ hLx0]
      have := mul_le_mul_of_nonneg_left h4 hΔ0
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- **The `M̄₁` step** (Theorem 6.23(c), Step 6: the `r̄₀`-terms are `≤ 10⁻⁹ c`): with
`c_y ≤ e^ā c_x`, `r_y ≤ r_x + Δ`, `4 ≤ r_x ≤ L`, `√c_x ≥ 8·10⁹ L²`,
`M̄₁(y) ≤ M̄₁(x) e^{2ā + 3Δ/10⁸}`. -/
lemma Mbar_step {rx ry cx cy Lx Δ ā : ℝ} (hcx0 : 0 < cx) (hcxy : cy ≤ Real.exp ā * cx)
    (hā0 : 0 ≤ ā) (hā1 : ā ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hrx4 : 4 ≤ rx) (hrxL : rx ≤ Lx)
    (hrxy : ry ≤ rx + Δ) (hry0 : 0 ≤ ry) (hqx : 8 * 10 ^ 9 * Lx ^ 2 ≤ Real.sqrt cx) :
    ry + (cy + ry * Real.sqrt cy + ry * (ry + 1) / 2) + 1 ≤
      (rx + (cx + rx * Real.sqrt cx + rx * (rx + 1) / 2) + 1) *
        Real.exp (2 * ā + 3 * Δ / 10 ^ 8) := by
  set qx := Real.sqrt cx with hqxdef
  have hqx2 : qx ^ 2 = cx := Real.sq_sqrt hcx0.le
  have hqx0 : 0 < qx := Real.sqrt_pos.mpr hcx0
  have heā1 : 1 ≤ Real.exp ā := Real.one_le_exp hā0
  have hqxy : Real.sqrt cy ≤ Real.exp ā * qx := by
    have h := Real.sqrt_le_sqrt hcxy
    rw [Real.sqrt_mul (Real.exp_pos _).le] at h
    have : Real.sqrt (Real.exp ā) ≤ Real.exp ā := by
      rw [Real.sqrt_le_left (Real.exp_pos _).le]; nlinarith
    exact h.trans (mul_le_mul_of_nonneg_right this hqx0.le)
  set Ex := rx + rx * qx + rx * (rx + 1) / 2 + 1 with hEx
  have hL1 : 4 ≤ Lx := le_trans hrx4 hrxL
  have hq1 : 1 ≤ qx := by nlinarith
  have hExc : Ex ≤ cx / 10 ^ 9 := by
    have h1 : Ex ≤ 4 * Lx ^ 2 * qx := by
      rw [hEx]
      have e1 : rx * (rx + 1) / 2 ≤ Lx ^ 2 := by nlinarith
      have e2 : rx * qx ≤ Lx ^ 2 * qx := by
        have : rx ≤ Lx ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hqx0.le
      have e3 : rx ≤ Lx ^ 2 * qx := by nlinarith
      have e4 : (1 : ℝ) ≤ Lx ^ 2 * qx := by nlinarith
      have e5 : Lx ^ 2 ≤ Lx ^ 2 * qx := by nlinarith
      linarith
    rw [← hqx2]
    have : 4 * Lx ^ 2 * qx ≤ qx ^ 2 / 10 ^ 9 := by
      rw [le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_left hqx hqx0.le
      nlinarith
    linarith
  have hrr : ry ≤ (1 + Δ) * rx := by nlinarith
  have e1 : ry * Real.sqrt cy ≤ (1 + Δ) * rx * (Real.exp ā * qx) :=
    mul_le_mul hrr hqxy (Real.sqrt_nonneg _) (by positivity)
  have e2 : ry * (ry + 1) ≤ (1 + Δ) ^ 2 * (rx * (rx + 1)) := by
    have : ry + 1 ≤ (1 + Δ) * (rx + 1) := by nlinarith
    calc ry * (ry + 1) ≤ ((1 + Δ) * rx) * ((1 + Δ) * (rx + 1)) :=
          mul_le_mul hrr this (by linarith) (by positivity)
      _ = (1 + Δ) ^ 2 * (rx * (rx + 1)) := by ring
  have hk : (1 + Δ) ^ 2 ≤ 1 + 3 * Δ := by nlinarith
  have hrq : 0 ≤ rx * qx := by positivity
  have hrr1 : 0 ≤ rx * (rx + 1) := by positivity
  set E := Real.exp ā with hE
  have g : 1 + Δ ≤ E * (1 + 3 * Δ) := by nlinarith
  have g2 : (1 + Δ) ^ 2 ≤ E * (1 + 3 * Δ) := by nlinarith
  have hrx0 : 0 ≤ rx := by linarith
  have f1 : (1 + Δ) * rx ≤ E * ((1 + 3 * Δ) * rx) := by
    have := mul_le_mul_of_nonneg_right g hrx0; linarith
  have f2 : (1 + Δ) * rx * (E * qx) ≤ E * ((1 + 3 * Δ) * (rx * qx)) := by
    have hErq : 0 ≤ E * (rx * qx) := by positivity
    have := mul_le_mul_of_nonneg_left (show 1 + Δ ≤ 1 + 3 * Δ by linarith) hErq
    nlinarith
  have f3 : (1 + Δ) ^ 2 * (rx * (rx + 1)) / 2 ≤ E * ((1 + 3 * Δ) * (rx * (rx + 1) / 2)) := by
    have := mul_le_mul_of_nonneg_right g2 hrr1; nlinarith
  have f4 : (1 : ℝ) ≤ E * ((1 + 3 * Δ) * 1) := by nlinarith
  have hMy : ry + (cy + ry * Real.sqrt cy + ry * (ry + 1) / 2) + 1 ≤
      E * (cx + Ex) + 3 * Δ * E * Ex := by
    rw [hEx]; nlinarith
  have heā : E ≤ 1 + 2 * ā := exp_le_one_add_two hā0 hā1
  have hM0 : 0 < cx + Ex := by positivity
  have hExM : Ex ≤ (cx + Ex) / 10 ^ 9 := by
    have : 0 ≤ Ex := by positivity
    linarith
  have h1 : E * (cx + Ex) + 3 * Δ * E * Ex ≤ (cx + Ex) * ((1 + 2 * ā) * (1 + 3 * Δ / 10 ^ 9)) := by
    have h2 : 3 * Δ * E * Ex ≤ 3 * Δ * E * ((cx + Ex) / 10 ^ 9) :=
      mul_le_mul_of_nonneg_left hExM (by positivity)
    have h3 : E * (cx + Ex) + 3 * Δ * E * ((cx + Ex) / 10 ^ 9) =
        (cx + Ex) * (E * (1 + 3 * Δ / 10 ^ 9)) := by ring
    have h4 : (cx + Ex) * (E * (1 + 3 * Δ / 10 ^ 9)) ≤
        (cx + Ex) * ((1 + 2 * ā) * (1 + 3 * Δ / 10 ^ 9)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heā (by positivity)) hM0.le
    linarith
  have h5 : (1 + 2 * ā) * (1 + 3 * Δ / 10 ^ 9) ≤ Real.exp (2 * ā + 3 * Δ / 10 ^ 8) := by
    have : (1 + 2 * ā) * (1 + 3 * Δ / 10 ^ 9) ≤ 2 * ā + 3 * Δ / 10 ^ 8 + 1 := by nlinarith
    exact this.trans (Real.add_one_le_exp _)
  have eM : rx + (cx + rx * qx + rx * (rx + 1) / 2) + 1 = cx + Ex := by rw [hEx]; ring
  rw [eM]
  calc _ ≤ E * (cx + Ex) + 3 * Δ * E * Ex := hMy
    _ ≤ (cx + Ex) * ((1 + 2 * ā) * (1 + 3 * Δ / 10 ^ 9)) := h1
    _ ≤ (cx + Ex) * Real.exp (2 * ā + 3 * Δ / 10 ^ 8) :=
        mul_le_mul_of_nonneg_left h5 hM0.le

variable (hX : 10 ^ 8 ≤ Real.log X₀)
include hX

set_option maxHeartbeats 1000000 in
/-- **The local step of (R_H)** (Theorem 6.23(c), Step 6): for `X₀ ≤ x ≤ y`,
`Δ = log y - log x ≤ 1`, `H(y) ≤ e^{4·10⁻⁶ Δ} H(x)`. -/
theorem capH_local {x y : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxy : x ≤ y)
    (hΔ : Real.log y - Real.log x ≤ 1) :
    capH X₀ y ≤ Real.exp (4 / 1000000 * (Real.log y - Real.log x)) * capH X₀ x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hx0 : 0 < x := by linarith
  obtain ⟨hLx, hℓΛx, hℓx0⟩ := logs_of_ge hX0 hX hx
  obtain ⟨hLy, hℓΛy, hℓy0⟩ := logs_of_ge hX0 hX (hx.trans hxy)
  have hLxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hstd := std_step hLx hLxy hΔ
  have hA1 : Real.exp (8 * Real.log (Real.log y) ^ 2) ≤
      Real.exp (4 / 1000000 * (Real.log y - Real.log x)) *
        max (Real.exp (8 * Real.log (Real.log x) ^ 2)) (capM1 X₀ x ^ 2) := by
    calc Real.exp (8 * Real.log (Real.log y) ^ 2)
        ≤ Real.exp (4 / 1000000 * (Real.log y - Real.log x) +
          8 * Real.log (Real.log x) ^ 2) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (4 / 1000000 * (Real.log y - Real.log x)) *
          Real.exp (8 * Real.log (Real.log x) ^ 2) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
  unfold capH
  refine max_le hA1 ?_
  by_cases hraise : capM1 X₀ y ^ 2 ≤ Real.exp (8 * Real.log (Real.log y) ^ 2)
  · exact hraise.trans hA1
  push_neg at hraise
  set Λ := Real.log X₀ with hΛdef
  have hX' : (100000000 : ℝ) ≤ Λ := by norm_num at hX; linarith
  have hLΛ := log_ge_18 hX'
  set Lx := Real.log x with hLxdef
  set Ly := Real.log y with hLydef
  set Δ := Ly - Lx with hΔdef
  have hΔ0 : 0 ≤ Δ := by linarith
  have hLx0 : 0 < Lx := by linarith
  set sx := capS X₀ x with hsx
  set sy := capS X₀ y with hsy
  have eℓx : 2 * Real.log Λ + sx = Real.log Lx := ell_eq X₀ x
  have eℓy : 2 * Real.log Λ + sy = Real.log Ly := ell_eq X₀ y
  have eLx : Real.exp (2 * Real.log Λ + sx) = Lx := by rw [eℓx]; exact Real.exp_log hLx0
  have eLy : Real.exp (2 * Real.log Λ + sy) = Ly := by
    rw [eℓy]; exact Real.exp_log (by linarith)
  have hδ : Real.log Ly - Real.log Lx ≤ Δ / Lx := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < Ly) hLx0)
    rw [Real.log_div (by linarith) hLx0.ne'] at h
    have : Ly / Lx - 1 = Δ / Lx := by rw [hΔdef]; field_simp
    linarith
  have hδ0 : 0 ≤ Real.log Ly - Real.log Lx := by
    have := Real.log_le_log hLx0 hLxy; linarith
  have hΔL : Δ / Lx ≤ 1 / 10 ^ 8 := by
    rw [div_le_div_iff₀ hLx0 (by norm_num)]; nlinarith
  have hssxy : sx ≤ sy := by linarith
  have hsxΛ : -Real.log Λ ≤ sx := by linarith
  -- the raised range
  have hraise' : Real.exp (8 * (2 * Real.log Λ + sy) ^ 2) < Mbar1 sHroot Λ sy ^ 2 := by
    rw [eℓy]; exact hraise
  obtain ⟨hdom, heq⟩ := logc_raised (by linarith) hraise'
  have hincr := logc_incr hX' hsxΛ hssxy hΔ0 (by rw [eLx]; linarith) (by linarith)
    (by rw [eLy, eLx]; linarith) hdom heq
  set ā := 61 / 10 ^ 8 * Δ with hā
  have hā0 : 0 ≤ ā := by positivity
  have hā1 : ā ≤ 1 := by rw [hā]; nlinarith
  -- the data of `M̄₁`
  set rx := rbar0 Λ sx with hrx
  set ry := rbar0 Λ sy with hry
  have hℓx18 : 18 ≤ Real.log Lx := by linarith
  have erx : rx = Lx / (3 * Real.log Lx) + 4 := by
    rw [hrx]; unfold rbar0; rw [eℓx, Real.exp_log hLx0]
  have ery : ry = Ly / (3 * Real.log Ly) + 4 := by
    rw [hry]; unfold rbar0; rw [eℓy, Real.exp_log (by linarith)]
  have hrxy : ry ≤ rx + Δ := by
    rw [ery, erx]
    have h1 : Ly / (3 * Real.log Ly) ≤ Ly / (3 * Real.log Lx) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    have h2 : Ly / (3 * Real.log Lx) = Lx / (3 * Real.log Lx) + Δ / (3 * Real.log Lx) := by
      rw [hΔdef]; ring
    have h3 : Δ / (3 * Real.log Lx) ≤ Δ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hrx4 : 4 ≤ rx := by
    rw [erx]; have : 0 ≤ Lx / (3 * Real.log Lx) := by positivity
    linarith
  have hry0 : 0 ≤ ry := by
    rw [ery]; have : 0 ≤ Ly / (3 * Real.log Ly) := by
      have : 0 < Real.log Ly := by linarith
      positivity
    linarith
  have hrxL : rx ≤ Lx := by
    rw [erx]
    have : Lx / (3 * Real.log Lx) ≤ Lx / 3 :=
      div_le_div_of_nonneg_left hLx0.le (by norm_num) (by linarith)
    linarith
  set cx := Real.exp (logc sHroot Λ sx) with hcx
  set cy := Real.exp (logc sHroot Λ sy) with hcy
  have hcx0 : 0 < cx := Real.exp_pos _
  have hcxy : cy ≤ Real.exp ā * cx := by
    rw [hcy, hcx, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hcxlow : Real.exp (4 * Real.log Lx ^ 2 - Real.log 4) ≤ cx := by
    rw [hcx]; apply Real.exp_le_exp.mpr; unfold logc; rw [eℓx]; exact le_max_left _ _
  have hqx := sqrt_c_big hℓx18 hcxlow
  rw [Real.exp_log hLx0] at hqx
  have hstep := Mbar_step hcx0 hcxy hā0 hā1 hΔ0 hΔ hrx4 hrxL hrxy hry0 hqx
  have hMx : capM1 X₀ x = rx + (cx + rx * Real.sqrt cx + rx * (rx + 1) / 2) + 1 := capM1_eq x
  have hMy : capM1 X₀ y = ry + (cy + ry * Real.sqrt cy + ry * (ry + 1) / 2) + 1 := capM1_eq y
  rw [← hMx, ← hMy] at hstep
  have hMy0 := capM1_pos hX0 hX (hx.trans hxy)
  calc capM1 X₀ y ^ 2 ≤ (capM1 X₀ x * Real.exp (2 * ā + 3 * Δ / 10 ^ 8)) ^ 2 :=
        pow_le_pow_left₀ hMy0.le hstep 2
    _ = Real.exp (2 * (2 * ā + 3 * Δ / 10 ^ 8)) * capM1 X₀ x ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring
    _ ≤ Real.exp (4 / 1000000 * Δ) * max (Real.exp (8 * Real.log Lx ^ 2))
          (capM1 X₀ x ^ 2) := by
        refine mul_le_mul (Real.exp_le_exp.mpr ?_) (le_max_right _ _) (by positivity)
          (Real.exp_pos _).le
        rw [hā]; nlinarith

/-! ### Chaining -/

/-- `H(y) ≤ e^{4·10⁻⁶ (log y - log x)} H(x)` for all `X₀ ≤ x ≤ y`. -/
theorem capH_chain : ∀ n : ℕ, ∀ x y : ℝ, (X₀ : ℝ) ≤ x → x ≤ y →
    Real.log y - Real.log x ≤ n →
    capH X₀ y ≤ Real.exp (4 / 1000000 * (Real.log y - Real.log x)) * capH X₀ x := by
  intro n
  induction n with
  | zero =>
    intro x y hx hxy h
    exact capH_local hX hx hxy (by push_cast at h; linarith)
  | succ n ih =>
    intro x y hx hxy h
    by_cases h1 : Real.log y - Real.log x ≤ 1
    · exact capH_local hX hx hxy h1
    push_neg at h1
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := QueueMono.one_lt_of_logX hX0 hX
    have hx0 : 0 < x := by linarith
    set m := Real.exp 1 * x with hm
    have hlm : Real.log m = Real.log x + 1 := by
      rw [hm, Real.log_mul (Real.exp_pos _).ne' hx0.ne', Real.log_exp]; ring
    have hxm : x ≤ m := by
      rw [hm]; nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hmy : m ≤ y := by
      have : Real.log m ≤ Real.log y := by linarith
      exact (Real.log_le_log_iff (by positivity) (by linarith)).mp this
    have hA := capH_local hX hx hxm (by linarith)
    have hB := ih m y (hx.trans hxm) hmy (by push_cast at h; linarith)
    have hH0 : 0 ≤ capH X₀ m := le_trans (Real.exp_pos _).le (le_max_left _ _)
    calc capH X₀ y ≤ Real.exp (4 / 1000000 * (Real.log y - Real.log m)) * capH X₀ m := hB
      _ ≤ Real.exp (4 / 1000000 * (Real.log y - Real.log m)) *
          (Real.exp (4 / 1000000 * (Real.log m - Real.log x)) * capH X₀ x) :=
          mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
      _ = Real.exp (4 / 1000000 * (Real.log y - Real.log x)) * capH X₀ x := by
          rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- **(R_H) for `capH`** (Theorem 6.23(c), integrated): `CapHSlope X₀ (4·10⁻⁶)`. -/
theorem capHSlope : KR.WidthReal.CapHSlope X₀ (4 / 1000000) := by
  intro x y hx hxy
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h := capH_chain hX ⌈Real.log y - Real.log x⌉₊ x y hx hxy (Nat.le_ceil _)
  rw [Real.rpow_def_of_pos (div_pos hy0 hx0), Real.log_div hy0.ne' hx0.ne']
  rw [show Real.log y - Real.log x = (Real.log y - Real.log x) by rfl] at h
  calc capH X₀ y ≤ _ := h
    _ = Real.exp ((Real.log y - Real.log x) * (4 / 1000000)) * capH X₀ x := by ring_nf

end CapHSlopeProof
