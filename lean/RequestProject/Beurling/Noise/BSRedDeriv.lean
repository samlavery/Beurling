module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Theorem 5.6, Step 5: the summand `f` in the variable `w`, and its derivative

In the variable `w = m/σ` the summand of (bs-rec-log) after the induction hypothesis is

  `Hf(w) = ν G(m, w) = ((1+w)/w) Φ(m) ρ(w-1) e^{Q(m,w)}`,  `m = ℓw/(1+w)`,

and `Hf = H₁ H₂` with `H₁ = ((1+w)/w) ρ(w-1)` (non-increasing: `f₁` of the paper) and
`H₂ = Φ(m) e^{Q(m,w)} = Φ_∞ e^{L(w)}`, `L(w) = -κ_Φ/m + Q(m, w)` (`f₂` of the paper).

* `hasDerivAt_H1`: `H₁' = -ρ(w-1)/w² + ((1+w)/w) ρ_D(w)` for `w > 0`, `w ≠ 2`, where
  `ρ_D(w) = -ρ(w-2)/(w-1)` for `w > 2` and `0` for `w < 2`; `H₁' ≤ 0`;
* `hasDerivAt_L`: `L' = Lp` (explicit), and `abs_Lp_le`: `|L'| ≤ η(w) := η_f(m, w) ℓ/(1+w)²`
  (`η_f = etaF`): this is `|∂_σ log f₂| ≤ η_f` of the paper, since `dσ/dw = -ℓ/(1+w)²`;
* `Hf_deriv_bound`: `|Hf'| ≤ -Hf' + 2 Hf η` (because `H₁' ≤ 0 ≤ H₁` and `|H₂'| ≤ η H₂`);
* continuity and integrability of all pieces on `[a, b] ⊂ (0, ∞)`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace BSaias

/-! ## The squared positive part -/

lemma hasDerivAt_sqpos (y : ℝ) : HasDerivAt (fun y : ℝ => max y 0 ^ 2) (2 * max y 0) y := by
  rcases lt_trichotomy y 0 with h | h | h
  · have hev : (fun y : ℝ => max y 0 ^ 2) =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [max_eq_right (le_of_lt hz)]; ring
    rw [max_eq_right h.le, mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    simp only [max_self, mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, smul_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    simp only [Real.norm_eq_abs]
    have h1 : |max h 0 ^ 2| ≤ |h| * |h| := by
      rw [abs_pow, sq]
      have : |max h 0| ≤ |h| := by
        rcases le_total h 0 with h0 | h0
        · rw [max_eq_right h0]; simp
        · rw [max_eq_left h0]
      exact mul_le_mul this this (abs_nonneg _) (abs_nonneg _)
    calc |max h 0 ^ 2| ≤ |h| * |h| := h1
      _ ≤ c * |h| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg _)
  · have hev : (fun y : ℝ => max y 0 ^ 2) =ᶠ[nhds y] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      rw [max_eq_left (le_of_lt hz)]
    rw [max_eq_left h.le]
    have := hasDerivAt_pow 2 y
    simp only [Nat.cast_ofNat] at this
    exact (this.congr_of_eventuallyEq hev).congr_deriv (by ring)

/-! ## `H₁ = ((1+w)/w) ρ(w-1)` -/

/-- The derivative of `w ↦ ρ(w-1)` off `w = 2`: `-ρ(w-2)/(w-1)` for `w > 2`, `0` for `w < 2`. -/
noncomputable def rhoD1 (w : ℝ) : ℝ := (Ioi 2).indicator (fun w => -(Dickman.rho (w - 2) /
  max (w - 1) 1)) w

lemma rhoD1_nonpos (w : ℝ) : rhoD1 w ≤ 0 := by
  unfold rhoD1
  by_cases h : w ∈ Ioi (2 : ℝ)
  · rw [indicator_of_mem h]
    have := Dickman.rho_pos (w - 2)
    have : 0 < max (w - 1) 1 := lt_max_of_lt_right one_pos
    simp only [neg_nonpos]; positivity
  · rw [indicator_of_notMem h]

lemma abs_rhoD1_le (w : ℝ) : |rhoD1 w| ≤ 1 := by
  unfold rhoD1
  by_cases h : w ∈ Ioi (2 : ℝ)
  · rw [indicator_of_mem h, abs_neg, abs_div, abs_of_pos (Dickman.rho_pos _),
      abs_of_pos (lt_max_of_lt_right one_pos)]
    rw [div_le_one (lt_max_of_lt_right one_pos)]
    exact (Dickman.rho_le_one _).trans (le_max_right _ _)
  · rw [indicator_of_notMem h]; simp

lemma hasDerivAt_rho_sub_one {w : ℝ} (hw : w ≠ 2) :
    HasDerivAt (fun w => Dickman.rho (w - 1)) (rhoD1 w) w := by
  rcases lt_or_gt_of_ne hw with h | h
  · have := (Dickman.hasDerivAt_rho_of_lt (u := w - 1) (by linarith)).comp w
      ((hasDerivAt_id w).sub_const 1)
    unfold rhoD1
    rw [indicator_of_notMem (show w ∉ Ioi (2 : ℝ) from fun h' => absurd (mem_Ioi.mp h') (by
      linarith))]
    simpa using this
  · have := (Dickman.hasDerivAt_rho (u := w - 1) (by linarith)).comp w
      ((hasDerivAt_id w).sub_const 1)
    unfold rhoD1
    rw [indicator_of_mem (show w ∈ Ioi (2 : ℝ) from h), max_eq_left (by linarith)]
    convert this using 1
    simp only [Function.comp, id, mul_one]
    ring_nf

/-- `H₁(w) = ((1+w)/w) ρ(w-1)`. -/
noncomputable def H1 (w : ℝ) : ℝ := (1 + w) / w * Dickman.rho (w - 1)

/-- `H₁'(w) = -ρ(w-1)/w² + ((1+w)/w) ρ_D(w)`. -/
noncomputable def H1' (w : ℝ) : ℝ := -(Dickman.rho (w - 1) / w ^ 2) + (1 + w) / w * rhoD1 w

lemma hasDerivAt_H1 {w : ℝ} (hw0 : 0 < w) (hw2 : w ≠ 2) : HasDerivAt H1 (H1' w) w := by
  have h1 : HasDerivAt (fun w : ℝ => (1 + w) / w) (-1 / w ^ 2) w := by
    have := ((hasDerivAt_id w).const_add 1).div (hasDerivAt_id w) hw0.ne'
    convert this using 1
    simp only [id]; field_simp; ring
  have := h1.mul (hasDerivAt_rho_sub_one hw2)
  unfold H1 H1'
  convert this using 1
  ring

lemma H1_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ H1 w := by
  unfold H1; have := Dickman.rho_pos (w - 1); positivity

lemma H1'_nonpos {w : ℝ} (hw : 0 < w) : H1' w ≤ 0 := by
  unfold H1'
  have h1 := Dickman.rho_pos (w - 1)
  have h2 := rhoD1_nonpos w
  have h3 : 0 ≤ (1 + w) / w := by positivity
  have : 0 ≤ Dickman.rho (w - 1) / w ^ 2 := by positivity
  nlinarith

lemma continuous_rho_sub_one : Continuous fun w : ℝ => Dickman.rho (w - 1) :=
  Dickman.continuous_rho.comp (continuous_sub_right 1)

lemma continuousOn_H1 {a b : ℝ} (ha : 0 < a) : ContinuousOn H1 (Icc a b) := by
  intro w hw
  have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
  apply ContinuousAt.continuousWithinAt
  unfold H1
  exact ((continuousAt_const.add continuousAt_id).div continuousAt_id hw0.ne').mul
    continuous_rho_sub_one.continuousAt

lemma intervalIntegrable_rhoD1 (a b : ℝ) : IntervalIntegrable rhoD1 volume a b := by
  have hc : Continuous fun w : ℝ => -(Dickman.rho (w - 2) / max (w - 1) 1) := by
    refine (Continuous.div (Dickman.continuous_rho.comp (continuous_sub_right 2))
      ((continuous_sub_right 1).max continuous_const) fun x => ?_).neg
    exact (lt_max_of_lt_right one_pos).ne'
  rw [intervalIntegrable_iff]
  exact (hc.integrableOn_uIoc).indicator measurableSet_Ioi

lemma intervalIntegrable_H1' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable H1' volume a b := by
  have hc1 : ContinuousOn (fun w => -(Dickman.rho (w - 1) / w ^ 2)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
    apply ContinuousAt.continuousWithinAt
    exact (continuous_rho_sub_one.continuousAt.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hw0.ne')).neg
  have hc2 : ContinuousOn (fun w : ℝ => (1 + w) / w) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
    exact ((continuousAt_const.add continuousAt_id).div continuousAt_id
      hw0.ne').continuousWithinAt
  exact (hc1.intervalIntegrable).add ((intervalIntegrable_rhoD1 a b).continuousOn_mul hc2)

/-! ## `H₂ = Φ_∞ e^{L(w)}`, `L(w) = -κ_Φ/m + Q(m, w)` -/

/-- `L(w) = -κ_Φ/m + Q(m, w)` with `m = ℓw/(1+w)`. -/
noncomputable def Lfun (τ ℓ w : ℝ) : ℝ := -(kappa τ / mOf ℓ w) + Qf (mOf ℓ w) w

/-- `H₂(w) = Φ(m) e^{Q(m, w)} = Φ_∞ e^{L(w)}`. -/
noncomputable def H2 (τ ℓ w : ℝ) : ℝ := PhiInf τ * Real.exp (Lfun τ ℓ w)

/-- `N(w) = B(1+w)³ log(2+w)`, so that `A(m, w) = N(w)/m`. -/
noncomputable def Nw (w : ℝ) : ℝ := 11 * (1 + w) ^ 3 * Real.log (2 + w)

/-- `N'(w) = B(3(1+w)² log(2+w) + (1+w)³/(2+w))`. -/
noncomputable def Nw' (w : ℝ) : ℝ :=
  11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w))

/-- `m'(w) = ℓ/(1+w)²`. -/
noncomputable def mOf' (ℓ w : ℝ) : ℝ := ℓ / (1 + w) ^ 2

/-- The explicit `L'(w)`. -/
noncomputable def Lp (τ ℓ w : ℝ) : ℝ :=
  let m := mOf ℓ w
  let d := dpos m w
  mOf' ℓ w * (kappa τ / m ^ 2 - Nw w / m ^ 2 - d / (4 * (m * u0 m)) - d ^ 2 / (4 * (m * √m)))
    + (Nw' w / m + d / √m)

/-- `η(w) = η_f(m, w) ℓ/(1+w)²`. -/
noncomputable def etaW (τ ℓ w : ℝ) : ℝ := etaF τ ℓ w * mOf' ℓ w

lemma red_mOf_pos {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) : 0 < mOf ℓ w := by
  unfold mOf; positivity

lemma hasDerivAt_mOf {ℓ w : ℝ} (hw : 0 < w) : HasDerivAt (mOf ℓ) (mOf' ℓ w) w := by
  have := ((hasDerivAt_id w).const_mul ℓ).div ((hasDerivAt_id w).const_add 1)
    (show (1 : ℝ) + id w ≠ 0 by simp only [id]; linarith)
  unfold mOf mOf'
  convert this using 1
  simp only [id]; field_simp; ring

lemma hasDerivAt_Nw {w : ℝ} (hw : 0 < w) : HasDerivAt Nw (Nw' w) w := by
  have h2 : (2 : ℝ) + w ≠ 0 := by linarith
  have := ((((hasDerivAt_id w).const_add 1).pow 3).const_mul 11).mul
    (((hasDerivAt_id w).const_add 2).log h2)
  unfold Nw Nw'
  convert this using 1
  simp only [id, Pi.pow_apply, Nat.cast_ofNat]; field_simp; ring

lemma hasDerivAt_L {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    HasDerivAt (Lfun τ ℓ) (Lp τ ℓ w) w := by
  have hm := hasDerivAt_mOf (ℓ := ℓ) hw
  have hm0 : 0 < mOf ℓ w := red_mOf_pos hℓ hw
  set m := mOf ℓ w with hmdef
  have hS : 0 < √m := Real.sqrt_pos.mpr hm0
  have hT : 0 < √√m := Real.sqrt_pos.mpr hS
  -- pieces
  have hk : HasDerivAt (fun w => -(kappa τ / mOf ℓ w))
      (-(-(kappa τ * mOf' ℓ w) / m ^ 2)) w := by
    have := (hm.inv hm0.ne').const_mul (kappa τ)
    convert this.neg using 1
    rw [hmdef]; field_simp
  have hA : HasDerivAt (fun w => BSCert.Z2.A (mOf ℓ w) w)
      ((Nw' w * m - Nw w * mOf' ℓ w) / m ^ 2) w := by
    have := (hasDerivAt_Nw hw).div hm hm0.ne'
    convert this using 1
  have hy : HasDerivAt (fun w => w - u0 (mOf ℓ w))
      (1 - mOf' ℓ w / (2 * √m) / (2 * √√m)) w := by
    have := ((hm.sqrt hm0.ne').sqrt hS.ne')
    exact (hasDerivAt_id w).sub this
  have hnum := (hasDerivAt_sqpos (w - u0 m)).comp w hy
  have hden : HasDerivAt (fun w => 2 * √(mOf ℓ w)) (2 * (mOf' ℓ w / (2 * √m))) w :=
    (hm.sqrt hm0.ne').const_mul 2
  have ha := hnum.div hden (mul_pos two_pos hS).ne'
  have hQ := hA.add ha
  have hL := hk.add hQ
  unfold Lfun Qf aQ
  convert hL using 1
  unfold Lp dpos
  simp only [Function.comp]
  have hSS : √m * √m = m := Real.mul_self_sqrt hm0.le
  have hTT : √√m * √√m = √m := Real.mul_self_sqrt hS.le
  have hu : u0 m = √√m := rfl
  rw [hu]
  clear_value m
  subst hmdef
  generalize mOf' ℓ w = m' at *
  generalize hTd : √√(mOf ℓ w) = T at *
  generalize hSd : √(mOf ℓ w) = S at *
  subst hTT
  generalize hmd : mOf ℓ w = M at *
  subst hSS
  generalize max (w - T) 0 = d
  have hT0 : T ≠ 0 := hT.ne'
  field_simp
  ring

lemma Nw_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ Nw w := by
  unfold Nw
  have : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  positivity

lemma Nw'_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ Nw' w := by
  unfold Nw'
  have : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have : 0 < 2 + w := by linarith
  positivity

lemma dpos_nonneg (m w : ℝ) : 0 ≤ dpos m w := le_max_right _ _

/-- `|L'(w)| ≤ η(w) = η_f(m, w) ℓ/(1+w)²` (the paper's `|∂_σ log f₂| ≤ η_f`). -/
lemma abs_Lp_le {τ ℓ w : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hw : 0 < w) :
    |Lp τ ℓ w| ≤ etaW τ ℓ w := by
  have hm0 : 0 < mOf ℓ w := red_mOf_pos hℓ hw
  have hm' : 0 < mOf' ℓ w := by unfold mOf'; positivity
  have hd := dpos_nonneg (mOf ℓ w) w
  have hS : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hm0
  have hu : 0 ≤ u0 (mOf ℓ w) := by unfold u0 BSCert.Z2.u0; positivity
  have hk : 0 ≤ kappa τ := by unfold kappa; linarith
  have hN := Nw_nonneg hw
  have hN' := Nw'_nonneg hw
  have hinv : mOf' ℓ w * ((1 + w) ^ 2 / ℓ) = 1 := by
    unfold mOf'; field_simp
  unfold etaW etaF Lp
  simp only
  set m := mOf ℓ w
  set d := dpos m w
  set m' := mOf' ℓ w
  have hAm : BSCert.Z2.A m w / m = Nw w / m ^ 2 := by unfold BSCert.Z2.A Nw; field_simp
  rw [hAm]
  have e1 : 0 ≤ kappa τ / m ^ 2 := by positivity
  have e2 : 0 ≤ Nw w / m ^ 2 := by positivity
  have e3 : 0 ≤ d / (4 * (m * u0 m)) := by positivity
  have e4 : 0 ≤ d ^ 2 / (4 * (m * √m)) := by positivity
  have e5 : 0 ≤ Nw' w / m + d / √m := by positivity
  have hrhs : (kappa τ / m ^ 2 + Nw w / m ^ 2 + (d / (4 * (m * u0 m)) + d ^ 2 / (4 * (m * √m))) +
      (1 + w) ^ 2 / ℓ * (Nw' w / m + d / √m)) * m' =
      m' * (kappa τ / m ^ 2 + Nw w / m ^ 2 + d / (4 * (m * u0 m)) + d ^ 2 / (4 * (m * √m)))
        + (Nw' w / m + d / √m) := by
    have : (1 + w) ^ 2 / ℓ * (Nw' w / m + d / √m) * m' = (Nw' w / m + d / √m) := by
      rw [mul_comm ((1 + w) ^ 2 / ℓ), mul_assoc, mul_comm _ m', hinv, mul_one]
    unfold Nw' at this ⊢
    linear_combination this
  unfold Nw' at hrhs e5 ⊢
  rw [hrhs]
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hm'.le e1, mul_nonneg hm'.le e2, mul_nonneg hm'.le e3,
      mul_nonneg hm'.le e4]
  · nlinarith [mul_nonneg hm'.le e1, mul_nonneg hm'.le e2, mul_nonneg hm'.le e3,
      mul_nonneg hm'.le e4]

lemma hasDerivAt_H2 {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    HasDerivAt (H2 τ ℓ) (H2 τ ℓ w * Lp τ ℓ w) w := by
  have := ((hasDerivAt_L (τ := τ) hℓ hw).exp).const_mul (PhiInf τ)
  unfold H2
  convert this using 1
  ring

lemma H2_pos (τ ℓ w : ℝ) : 0 < H2 τ ℓ w := by
  unfold H2
  have : 0 < PhiInf τ := by
    unfold PhiInf C0
    have := Real.exp_pos (kappa τ / τ)
    have : 0 < max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ))) :=
      lt_max_of_lt_left this
    positivity
  positivity

/-! ## `Hf = H₁ H₂ = ν G(m, w)` -/

/-- `Hf(w) = ((1+w)/w) G(m, w)`, `m = ℓw/(1+w)`. -/
noncomputable def Hf (τ ℓ w : ℝ) : ℝ := (1 + w) / w * Gf τ (mOf ℓ w) w

lemma Hf_eq (τ ℓ w : ℝ) : Hf τ ℓ w = H1 w * H2 τ ℓ w := by
  unfold Hf H1 H2 Gf Phi Lfun
  rw [Real.exp_add]; ring

/-- `Hf' = H₁' H₂ + H₁ H₂ L'`. -/
noncomputable def Hf' (τ ℓ w : ℝ) : ℝ := H1' w * H2 τ ℓ w + H1 w * (H2 τ ℓ w * Lp τ ℓ w)

lemma hasDerivAt_Hf {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) (hw2 : w ≠ 2) :
    HasDerivAt (Hf τ ℓ) (Hf' τ ℓ w) w := by
  have := (hasDerivAt_H1 hw hw2).mul (hasDerivAt_H2 (τ := τ) hℓ hw)
  rw [show Hf τ ℓ = fun w => H1 w * H2 τ ℓ w from funext (Hf_eq τ ℓ)]
  exact this

/-- `|Hf'| ≤ -Hf' + 2 Hf η`. -/
lemma Hf_deriv_bound {τ ℓ w : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hw : 0 < w) :
    |Hf' τ ℓ w| ≤ -Hf' τ ℓ w + 2 * Hf τ ℓ w * etaW τ ℓ w := by
  have h1 := H1_nonneg hw
  have h1' := H1'_nonpos hw
  have h2 := H2_pos τ ℓ w
  have hL := abs_le.mp (abs_Lp_le (τ := τ) hτ hℓ hw)
  rw [Hf_eq]
  unfold Hf'
  have hc : 0 ≤ H1 w * H2 τ ℓ w := mul_nonneg h1 h2.le
  have h3 : H1' w * H2 τ ℓ w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1' h2.le
  have h4 : 0 ≤ H1 w * H2 τ ℓ w * (etaW τ ℓ w - Lp τ ℓ w) := mul_nonneg hc (by linarith)
  have h5 : 0 ≤ H1 w * H2 τ ℓ w * (etaW τ ℓ w + Lp τ ℓ w) := mul_nonneg hc (by linarith)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ## Continuity -/

lemma continuousAt_mOf {ℓ w : ℝ} (hw : 0 < w) : ContinuousAt (mOf ℓ) w := by
  unfold mOf
  have h1w : (1 : ℝ) + id w ≠ 0 := ne_of_gt (by simp only [id]; linarith)
  exact (continuousAt_const.mul continuousAt_id).div (continuousAt_const.add continuousAt_id)
    h1w

lemma continuousAt_Lfun {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    ContinuousAt (Lfun τ ℓ) w := (hasDerivAt_L (τ := τ) hℓ hw).continuousAt

lemma continuousAt_H2 {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) : ContinuousAt (H2 τ ℓ) w :=
  (hasDerivAt_H2 (τ := τ) hℓ hw).continuousAt

lemma continuousOn_Hf {τ ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    ContinuousOn (Hf τ ℓ) (Icc a b) := by
  rw [show Hf τ ℓ = fun w => H1 w * H2 τ ℓ w from funext (Hf_eq τ ℓ)]
  refine (continuousOn_H1 ha).mul ?_
  intro w hw
  exact (continuousAt_H2 hℓ (lt_of_lt_of_le ha hw.1)).continuousWithinAt

lemma continuousAt_etaF {τ ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    ContinuousAt (etaF τ ℓ) w := by
  have hm0 : 0 < mOf ℓ w := red_mOf_pos hℓ hw
  have h2w : (2 : ℝ) + id w ≠ 0 := ne_of_gt (by simp only [id]; linarith)
  have hmc := continuousAt_mOf (ℓ := ℓ) hw
  have hS : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hm0
  have hT : 0 < u0 (mOf ℓ w) := by unfold u0 BSCert.Z2.u0; positivity
  have hT4 : (4 : ℝ) * (mOf ℓ w * u0 (mOf ℓ w)) ≠ 0 :=
    mul_ne_zero four_ne_zero (mul_pos hm0 hT).ne'
  have hS4 : (4 : ℝ) * (mOf ℓ w * √(mOf ℓ w)) ≠ 0 :=
    mul_ne_zero four_ne_zero (mul_pos hm0 hS).ne'
  have hu0c : ContinuousAt (fun w => u0 (mOf ℓ w)) w := by
    unfold u0 BSCert.Z2.u0; exact (hmc.sqrt).sqrt
  have hSc : ContinuousAt (fun w => √(mOf ℓ w)) w := hmc.sqrt
  have hdc : ContinuousAt (fun w => dpos (mOf ℓ w) w) w := by
    unfold dpos; exact (continuousAt_id.sub hu0c).max continuousAt_const
  have hAc : ContinuousAt (fun w => BSCert.Z2.A (mOf ℓ w) w) w := by
    unfold BSCert.Z2.A
    exact ((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 3)).mul
      ((continuousAt_const.add continuousAt_id).log h2w)).div hmc
        hm0.ne'
  unfold etaF
  simp only
  refine ((((continuousAt_const.div (hmc.pow 2) (pow_ne_zero 2 hm0.ne')).add
    (hAc.div hmc hm0.ne')).add ?_).add ?_)
  · exact (hdc.div (continuousAt_const.mul (hmc.mul hu0c)) hT4).add
      ((hdc.pow 2).div (continuousAt_const.mul (hmc.mul hSc)) hS4)
  · refine ((continuousAt_const.add continuousAt_id).pow 2 |>.div continuousAt_const
      hℓ.ne').mul ((ContinuousAt.div ?_ hmc hm0.ne').add (hdc.div hSc hS.ne'))
    refine continuousAt_const.mul (((continuousAt_const.mul
      ((continuousAt_const.add continuousAt_id).pow 2)).mul
      ((continuousAt_const.add continuousAt_id).log h2w)).add
      (((continuousAt_const.add continuousAt_id).pow 3).div
        (continuousAt_const.add continuousAt_id) h2w))

lemma continuousOn_etaW {τ ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    ContinuousOn (etaW τ ℓ) (Icc a b) := by
  intro w hw
  have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
  have h1w : (1 : ℝ) + id w ≠ 0 := ne_of_gt (by simp only [id]; linarith)
  apply ContinuousAt.continuousWithinAt
  unfold etaW mOf'
  exact (continuousAt_etaF hℓ hw0).mul (continuousAt_const.div
    ((continuousAt_const.add continuousAt_id).pow 2) (pow_ne_zero 2 h1w))

lemma intervalIntegrable_Hf' {τ ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (Hf' τ ℓ) volume a b := by
  have hH2c : ContinuousOn (H2 τ ℓ) (uIcc a b) := by
    rw [uIcc_of_le hab]; intro w hw
    exact (continuousAt_H2 hℓ (lt_of_lt_of_le ha hw.1)).continuousWithinAt
  have hLc : ContinuousOn (fun w => H1 w * (H2 τ ℓ w * Lp τ ℓ w)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine (continuousOn_H1 ha).mul (fun w hw => ?_)
    have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
    have h1w : (1 : ℝ) + id w ≠ 0 := ne_of_gt (by simp only [id]; linarith)
    have h2w : (2 : ℝ) + id w ≠ 0 := ne_of_gt (by simp only [id]; linarith)
    -- Lp is continuous: it is a combination of continuous functions
    have hm0 : 0 < mOf ℓ w := red_mOf_pos hℓ hw0
    have hmc := continuousAt_mOf (ℓ := ℓ) hw0
    have hS : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hm0
    have hT : 0 < u0 (mOf ℓ w) := by unfold u0 BSCert.Z2.u0; positivity
    have hT4 : (4 : ℝ) * (mOf ℓ w * u0 (mOf ℓ w)) ≠ 0 :=
      mul_ne_zero four_ne_zero (mul_pos hm0 hT).ne'
    have hS4 : (4 : ℝ) * (mOf ℓ w * √(mOf ℓ w)) ≠ 0 :=
      mul_ne_zero four_ne_zero (mul_pos hm0 hS).ne'
    have hu0c : ContinuousAt (fun w => u0 (mOf ℓ w)) w := by
      unfold u0 BSCert.Z2.u0; exact (hmc.sqrt).sqrt
    have hSc : ContinuousAt (fun w => √(mOf ℓ w)) w := hmc.sqrt
    have hdc : ContinuousAt (fun w => dpos (mOf ℓ w) w) w := by
      unfold dpos; exact (continuousAt_id.sub hu0c).max continuousAt_const
    have hm'c : ContinuousAt (mOf' ℓ) w := by
      unfold mOf'
      exact continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2)
        (pow_ne_zero 2 h1w)
    have hlog : ContinuousAt (fun w : ℝ => Real.log (2 + w)) w :=
      (continuousAt_const.add continuousAt_id).log h2w
    have hNc : ContinuousAt Nw w := by
      unfold Nw
      exact (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 3)).mul hlog
    have hN'c : ContinuousAt Nw' w := by
      unfold Nw'
      exact continuousAt_const.mul (((continuousAt_const.mul
        ((continuousAt_const.add continuousAt_id).pow 2)).mul hlog).add
        (((continuousAt_const.add continuousAt_id).pow 3).div
          (continuousAt_const.add continuousAt_id) h2w))
    have hLpc : ContinuousAt (Lp τ ℓ) w := by
      unfold Lp
      simp only
      refine (hm'c.mul ((((continuousAt_const.div (hmc.pow 2) (pow_ne_zero 2 hm0.ne')).sub
        (hNc.div (hmc.pow 2) (pow_ne_zero 2 hm0.ne'))).sub
        (hdc.div (continuousAt_const.mul (hmc.mul hu0c)) hT4)).sub
        ((hdc.pow 2).div (continuousAt_const.mul (hmc.mul hSc)) hS4))).add
        ((hN'c.div hmc hm0.ne').add (hdc.div hSc hS.ne'))
    exact ((continuousAt_H2 hℓ hw0).mul hLpc).continuousWithinAt
  exact ((intervalIntegrable_H1' ha hab).mul_continuousOn hH2c).add hLc.intervalIntegrable

end BSaias

end
