module

public import RequestProject.Beurling.Construction.YBounds

/-!
# Condition (81) and the hypothesis `(∗)` of Lemma 6.26 (Theorem 6.23(b), Step 5)

* `cond81_core`: the numerical core of Step 5. With `u₀ = θ_b L / log 2y`, in the raised regime
  (`log 2y ≤ 3.01γΛ`, `log C_d + 4 log L ≤ 1.01γΛ`, `log x ≥ 393Λ²`, `0 < γ ≤ 7.5`) or the standard
  regime (`log 2y ≤ 12.1ℓ²`, `log C_d + 4 log L ≤ 4.1ℓ²`, `ℓ ≥ 2886`):
  `u₀ ≥ 2·10⁸` and `log 2y + log C_d + 4 log L ≤ 0.9 u₀ log u₀`.
* `regimes_of_gt_sH`: above `s_H`, `y(x)` is in one of the two regimes.
-/

@[expose] public section

open Real Set BSCert.Capl CaplLink QueueMono InitialRange AbsorbEmpty

namespace Construction

lemma log_217e6_le_log {t : ℝ} (ht : 217000000 ≤ t) : 19.19 ≤ Real.log t :=
  le_trans log_217e6_ge (Real.log_le_log (by norm_num) ht)

/-- **The numerical core of Step 5 of Theorem 6.23**. Let `Λ ≥ 10⁸`, `θ_b ≥ 1/8`,
`L_x = e^ℓ`, `L ≥ L_x - 1`, `Ly > 0`, and suppose one of the two regimes. Then `u₀ = θ_b L / Ly`
satisfies `u₀ ≥ 2·10⁸` and `Ly + D ≤ 0.9 u₀ log u₀`. -/
theorem cond81_core {Λ θb L Lx ℓ Ly D γ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hθ : 1 / 8 ≤ θb)
    (hLx : Lx = Real.exp ℓ) (hLLx : Lx - 1 ≤ L) (hLy0 : 0 < Ly)
    (hreg : (0 < γ ∧ γ ≤ 7.5 ∧ Ly ≤ 3.01 * γ * Λ ∧ D ≤ 1.01 * γ * Λ ∧ 393 * Λ ^ 2 ≤ Lx) ∨
      (Ly ≤ 12.1 * ℓ ^ 2 ∧ D ≤ 4.1 * ℓ ^ 2 ∧ 2886 ≤ ℓ)) :
    2 * 10 ^ 8 ≤ θb * L / Ly ∧ Ly + D ≤ 0.9 * (θb * L / Ly) * Real.log (θb * L / Ly) := by
  set u0 := θb * L / Ly with hu0
  rcases hreg with ⟨hγ0, hγ, hLy, hD, hLx3⟩ | ⟨hLy, hD, hl⟩
  · -- the raised regime: `u₀ ≥ 16.3 Λ/γ`
    have hθL : 49.1 * Λ ^ 2 ≤ θb * L := by
      have hΛ2 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
      nlinarith
    have hu0ge : 16.3 * Λ / γ ≤ u0 := by
      rw [hu0, div_le_div_iff₀ hγ0 hLy0]
      have : 16.3 * Λ * Ly ≤ 16.3 * Λ * (3.01 * γ * Λ) :=
        mul_le_mul_of_nonneg_left hLy (by positivity)
      nlinarith
    have hΛγ : 16.3 * Λ / γ ≥ 217000000 := by
      rw [ge_iff_le, le_div_iff₀ hγ0]; nlinarith
    have hu0big : 217000000 ≤ u0 := le_trans hΛγ hu0ge
    have hlog := log_217e6_le_log hu0big
    refine ⟨by linarith, ?_⟩
    have h1 : 0.9 * u0 * 19.19 ≤ 0.9 * u0 * Real.log u0 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : 4.02 * γ * Λ ≤ 0.9 * (16.3 * Λ / γ) * 19.19 := by
      rw [show 0.9 * (16.3 * Λ / γ) * 19.19 = 0.9 * 16.3 * 19.19 * Λ / γ by ring,
        le_div_iff₀ hγ0]
      have : γ * γ ≤ 7.5 * 7.5 := by nlinarith
      nlinarith
    have h3 : 0.9 * (16.3 * Λ / γ) * 19.19 ≤ 0.9 * u0 * 19.19 := by nlinarith
    linarith
  · -- the standard regime: `u₀ ≥ ℓ⁴/70000`
    have hexp : ℓ ^ 6 / 720 ≤ Lx := by
      rw [hLx]
      have := Real.pow_div_factorial_le_exp ℓ (by linarith : (0 : ℝ) ≤ ℓ) 6
      simpa [Nat.factorial] using this
    have hl2 : (2886 : ℝ) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hl 2
    have hl4 : ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 := by ring
    have hl6 : ℓ ^ 6 = ℓ ^ 4 * ℓ ^ 2 := by ring
    have hθL : ℓ ^ 6 / 5770 ≤ θb * L := by
      have h1 : 1 ≤ ℓ ^ 6 / 720 - ℓ ^ 6 / 721 := by
        have : ℓ ^ 6 / 720 - ℓ ^ 6 / 721 = ℓ ^ 6 / (720 * 721) := by ring
        rw [this, le_div_iff₀ (by norm_num)]
        have : (2886 : ℝ) ^ 6 ≤ ℓ ^ 6 := pow_le_pow_left₀ (by norm_num) hl 6
        nlinarith
      have hL : ℓ ^ 6 / 721 ≤ L := by linarith
      have h0 : 0 ≤ ℓ ^ 6 := by positivity
      nlinarith
    have hl20 : 0 < ℓ ^ 2 := by positivity
    have hu0ge : ℓ ^ 4 / 70000 ≤ u0 := by
      rw [hu0, div_le_div_iff₀ (by norm_num) hLy0]
      have : ℓ ^ 4 * Ly ≤ ℓ ^ 4 * (12.1 * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left hLy (by positivity)
      nlinarith
    have hl4big : (2886 : ℝ) ^ 4 ≤ ℓ ^ 4 := pow_le_pow_left₀ (by norm_num) hl 4
    have hu0big : 217000000 ≤ u0 := by
      have : (217000000 : ℝ) ≤ ℓ ^ 4 / 70000 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      linarith
    have hlog := log_217e6_le_log hu0big
    refine ⟨by linarith, ?_⟩
    have h1 : 0.9 * u0 * 19.19 ≤ 0.9 * u0 * Real.log u0 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : 16.2 * ℓ ^ 2 ≤ 0.9 * (ℓ ^ 4 / 70000) * 19.19 := by
      rw [hl4]; nlinarith
    have h3 : 0.9 * (ℓ ^ 4 / 70000) * 19.19 ≤ 0.9 * u0 * 19.19 := by nlinarith
    linarith

/-- `γ(s) ∈ [γ*(s_H), 7.5]` above `s_H`. -/
lemma gam_bounds_of_gt {s : ℝ} (hs : sHroot < s) : gTarget ≤ gam sHroot s ∧ gam sHroot s ≤ 7.5 := by
  refine ⟨?_, gam_le_of_gt gstar_sHroot_le hs⟩
  have := gam_monotone sHroot_le_six gstar_sHroot_le hs.le
  have e : gam sHroot sHroot = gTarget := by
    unfold gam; rw [if_pos le_rfl, gstar_sHroot]
  linarith

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
`log X₀ ≥ 10⁸`, `θ ∈ [1/4, 1/2]`, `X₀ ≤ u ≤ x ≤ 2u`, `L = log u`, `h = u^{θ/2}`, `y = y(x)`,
`C_d = M̄₁(u) L⁶/2` and `u₀ = (θ/2) L / log 2y`, and suppose `2y > X₀` (which holds wherever `A`
meets the window). Then, with `u_* = log(2yh)/log 2y`:
`u_* ≥ 2·10⁸`, `log log 2y ≤ 1.79 u_*`, `log u_*/log 2y ≤ 0.31`, `1 ≤ u₀ ≤ u_*`, and (81):
`log 2y + log C_d + 4 log L ≤ 0.9 u₀ log u₀`. -/
theorem cond81_window {X₀ θ u x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2) (hu : X₀ ≤ u) (hux : u ≤ x) (hx2 : x ≤ 2 * u)
    (hy : X₀ < 2 * absorbYAt X₀ x) :
    let y := absorbYAt X₀ x
    let h := u ^ (θ / 2)
    let us := Real.log (2 * y * h) / Real.log (2 * y)
    let u0 := θ / 2 * Real.log u / Real.log (2 * y)
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
  -- `s > s_H`
  have hs : sHroot < capS X₀ x := by
    by_contra hc; push_neg at hc
    have := two_absorbYAt_lt_of_le_sH hX0 hX hx hc
    linarith
  have hy1 : 1 ≤ y := one_le_absorbYAt hX0 hX hx
  have hLyΛ : Λ < Ly := Real.log_lt_log (by linarith) hy
  have hLy0 : 0 < Ly := by linarith
  -- `log(2yh) = Ly + (θ/2) L`, so `u_* = 1 + u₀`
  have hh0 : 0 < h := Real.rpow_pos_of_pos hu0 _
  have hlogh : Real.log h = θ / 2 * L := Real.log_rpow hu0 _
  have hus : us = 1 + u0 := by
    show Real.log (2 * y * h) / Ly = 1 + θ / 2 * L / Ly
    rw [Real.log_mul (by positivity) hh0.ne', hlogh, add_div, div_self hLy0.ne']
  -- the constants
  obtain ⟨hD0, hD⟩ := log_capCd_le hX0 hX hu hux
  set D := Real.log (capCd X₀ u) + 4 * Real.log L with hDdef
  have hLx_exp : Real.log x = Real.exp ℓ := (Real.exp_log (by linarith)).symm
  have hLLx : Real.log x - 1 ≤ L := by
    have h2 := Real.log_le_log hx0 hx2
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    have : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hcore := cond81_core (Λ := Λ) (θb := θ / 2) (L := L) (Lx := Real.log x) (ℓ := ℓ) (Ly := Ly)
    (D := D) (γ := gam sHroot (capS X₀ x)) hX (by linarith) hLx_exp hLLx hLy0 (by
      rcases regimes_of_gt_sH hX0 hX hx hs with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, h3, hD.trans h4, h5⟩
      · exact Or.inr ⟨h1, hD.trans h2, h3⟩)
  obtain ⟨hu0big, h81⟩ := hcore
  have hu0e : u0 = θ / 2 * L / Ly := rfl
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
    have hθL : θ / 2 * L ≤ L := by nlinarith
    have hLΛ : Λ ≤ L := Real.log_le_log (by linarith) hu
    have hΛ0 : 0 < Λ := by linarith
    have hL0 : 0 ≤ L := by linarith
    have hA : u0 ≤ L / Λ :=
      calc u0 = θ / 2 * L / Ly := hu0e
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
      rcases regimes_of_gt_sH hX0 hX hx hs with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, h3, by positivity, h5⟩
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
