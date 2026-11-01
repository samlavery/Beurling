module

public import RequestProject.Beurling.Model.Slope
public import RequestProject.Beurling.OscMellin
public import RequestProject.BSCert.Consts.PhiCert

/-!
# The modulus of `R'` (§5, eq. (osc), the bullet on `o_R`)

The paper bounds the oscillation part `o_R` of `o_u` by
`o_R ≤ ∑_{k : x_k ≤ u} γ_k κ_k H(u) u⁻¹ (x_k/u)^{1-θ} ≤ H(u) u^{-θ}`, i.e. by a bound on `R''`
over a window. Here:

* `hasDerivAt_oscD` : the second derivative of one oscillation `R_k`, explicitly;
* `abs_oscD2_le` : `|R_k''(x)| ≤ |α| x^{θ-2} (γ² + 6γ + 15)`, from `0 ≤ ϕ' ≤ 2`, `|ϕ''| ≤ 10`
  (Appendix B.4, `phiCut_deriv_mem`, `phiCut_deriv2_le`), and `R_k'' = 0` on `(0, x⁺_k]`;
* `abs_oscD2_designed_le` : for the designed heights and amplitudes,
  `|R_k''(x)| ≤ 2⁻ᵏ x^{-θ} / 10¹⁴`;
* `deriv_osc_sub_le` : `|R'(t) - R'(s)| ≤ (t - s) max(s, x⁺_0)^{-θ}/10¹³` for `X₀ ≤ s ≤ t`, and
  `= 0` for `t ≤ x⁺_0` (`R' = 0` on `(0, x⁺_0]`). With the switch-on condition this gives the paper's
  `o_R ≤ H(u) u^{-θ}` for `u ≥ x₁/4`, `o_R = 0` below (04f, small `θ`).
-/

@[expose] public section

open Set Real Filter Topology

namespace BModel

/-- The explicit derivative `R_k'` of one oscillation (`Oscillation.hasDerivAt_oscTerm`). -/
noncomputable def oscD (θ α γ xk x : ℝ) : ℝ :=
  α * x ^ (θ - 1) * (θ * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
    - γ * Real.sin (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
    + Real.cos (γ * Real.log x) * deriv Real.smoothTransition (Real.log (x / xk)))

/-- The explicit second derivative `R_k''` of one oscillation. -/
noncomputable def oscD2 (θ α γ xk x : ℝ) : ℝ :=
  α * x ^ (θ - 2) *
    ((θ - 1) * (θ * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
      - γ * Real.sin (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
      + Real.cos (γ * Real.log x) * deriv Real.smoothTransition (Real.log (x / xk))) +
    (-(θ * γ) * Real.sin (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
      + θ * Real.cos (γ * Real.log x) * deriv Real.smoothTransition (Real.log (x / xk))
      - γ ^ 2 * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xk))
      - 2 * γ * Real.sin (γ * Real.log x) * deriv Real.smoothTransition (Real.log (x / xk))
      + Real.cos (γ * Real.log x) *
        deriv (deriv Real.smoothTransition) (Real.log (x / xk))))

lemma deriv_oscTerm_eq {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : 0 < xk) :
    deriv (Oscillation.oscTerm θ α γ xk) x = oscD θ α γ xk x :=
  (Oscillation.hasDerivAt_oscTerm hx hxk).deriv

/-- The explicit `R_k'` of the `k`-th oscillation of the design `θ`: `oscD` with the per-zero
exponent, minus (for the design `θ = 0`) the slope of the part switched on at the switch-off
point `x⁺ max(x⁺, 1)`. -/
noncomputable def RkD (θ α γ xk x : ℝ) : ℝ :=
  oscD (thK θ xk) α γ xk x - if θ = 0 then oscD (thK θ xk) α γ (xk * max xk 1) x else 0

lemma deriv_oscK_eq {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : 0 < xk) :
    deriv (Oscillation.oscK θ α γ xk) x = RkD θ α γ xk x := by
  have hy : 0 < xk * max xk 1 := mul_pos hxk (lt_of_lt_of_le one_pos (le_max_right _ _))
  unfold RkD
  by_cases hθ : θ = 0
  · subst hθ
    rw [Oscillation.deriv_oscK_zero hxk hx, deriv_oscTerm_eq hx hxk, deriv_oscTerm_eq hx hy,
      if_pos rfl]
  · have e : Oscillation.oscK θ α γ xk = Oscillation.oscTerm θ α γ xk := by
      funext z; exact Oscillation.oscK_of_ne hθ _ _ _ _
    rw [e, deriv_oscTerm_eq hx hxk, if_neg hθ, thK_of_ne hθ, sub_zero]

lemma RkD_of_ne {θ α γ xk x : ℝ} (hθ : θ ≠ 0) : RkD θ α γ xk x = oscD θ α γ xk x := by
  simp [RkD, hθ, thK_of_ne hθ]

lemma differentiable_deriv_smoothTransition : Differentiable ℝ (deriv Real.smoothTransition) :=
  ((Real.smoothTransition.contDiff (n := 2)).iterate_deriv' 1 1).differentiable (by norm_num)

/-- `ϕ''(t) = 0` for `t ≤ 0`: there `ϕ' = 0` is a minimum of `ϕ' ≥ 0`. -/
lemma deriv2_smoothTransition_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [deriv_smoothTransition_of_nonpos ht]
  exact SmoothStep.deriv_smoothTransition_nonneg s

/-- **`R_k''`** (for the `o_R` bullet of eq. (osc)). -/
theorem hasDerivAt_oscD {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : 0 < xk) :
    HasDerivAt (oscD θ α γ xk) (oscD2 θ α γ xk x) x := by
  have hr : HasDerivAt (fun y : ℝ => y ^ (θ - 1)) ((θ - 1) * x ^ (θ - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hc : HasDerivAt (fun y : ℝ => Real.cos (γ * Real.log y))
      (-Real.sin (γ * Real.log x) * (γ * x⁻¹)) x := (hlog.const_mul γ).cos
  have hs : HasDerivAt (fun y : ℝ => Real.sin (γ * Real.log y))
      (Real.cos (γ * Real.log x) * (γ * x⁻¹)) x := (hlog.const_mul γ).sin
  have hlog2 : HasDerivAt (fun y : ℝ => Real.log (y / xk)) x⁻¹ x := by
    have := ((hasDerivAt_id x).div_const xk).log (div_ne_zero hx.ne' hxk.ne')
    convert! this using 1
    simp only [id]
    field_simp
  have hϕ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (Real.log (x / xk))) (Real.log (x / xk)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hϕ' : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (Real.log (x / xk))) (Real.log (x / xk)) :=
    (differentiable_deriv_smoothTransition _).hasDerivAt
  have hp := hϕ.comp x hlog2
  have hd := hϕ'.comp x hlog2
  have hQ := (((hc.const_mul θ).mul hp).sub ((hs.const_mul γ).mul hp)).add (hc.mul hd)
  have h := (hr.const_mul α).mul hQ
  refine h.congr_deriv ?_
  have hx2 : x ^ (θ - 1) = x ^ (θ - 2) * x := by
    rw [← Real.rpow_add_one hx.ne']; ring_nf
  have hx3 : x ^ (θ - 1 - 1) = x ^ (θ - 2) := by ring_nf
  simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, hx2, hx3]
  unfold oscD2
  field_simp
  ring

/-- `R_k'' = 0` on `(0, x⁺_k]`. -/
lemma oscD2_eq_zero_of_le {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : x ≤ xk) :
    oscD2 θ α γ xk x = 0 := by
  have hxk0 : 0 < xk := lt_of_lt_of_le hx hxk
  have ht : Real.log (x / xk) ≤ 0 :=
    Real.log_nonpos (div_pos hx hxk0).le ((div_le_one hxk0).mpr hxk)
  unfold oscD2
  rw [Real.smoothTransition.zero_of_nonpos ht, deriv_smoothTransition_of_nonpos ht,
    deriv2_smoothTransition_of_nonpos ht]
  ring

/-- `ϕ'(t) = 0` for `t ≥ 1`: there `ϕ = 1` is a maximum of `ϕ ≤ 1`. -/
lemma deriv_smoothTransition_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.smoothTransition.one_of_one_le ht]
  exact Real.smoothTransition.le_one s

/-- `ϕ''(t) = 0` for `t ≥ 1`: there `ϕ' = 0` is a minimum of `ϕ' ≥ 0`. -/
lemma deriv2_smoothTransition_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [deriv_smoothTransition_of_one_le ht]
  exact SmoothStep.deriv_smoothTransition_nonneg s

/-- Beyond `e·max(x⁺, y)` both oscillations are fully switched on, so their `R''` agree (the
switched-off oscillation of the design `θ = 0` has `R'' = 0` beyond `e (x⁺)²`). -/
lemma oscD2_eq_of_one_le {θ α γ xk y x : ℝ} (h1 : 1 ≤ Real.log (x / xk))
    (h2 : 1 ≤ Real.log (x / y)) : oscD2 θ α γ xk x = oscD2 θ α γ y x := by
  unfold oscD2
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
    deriv_smoothTransition_of_one_le h1, deriv_smoothTransition_of_one_le h2,
    deriv2_smoothTransition_of_one_le h1, deriv2_smoothTransition_of_one_le h2]

/-- **`|R_k''(x)| ≤ |α| x^{θ-2} (γ² + 6γ + 15)`** for `0 ≤ θ ≤ 1`, `γ ≥ 0`, from `ϕ ∈ [0, 1]`,
`0 ≤ ϕ' ≤ 2`, `|ϕ''| ≤ 10` (Appendix B.4). -/
lemma abs_oscD2_le {θ α γ xk x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ) (hx : 0 < x) :
    |oscD2 θ α γ xk x| ≤ |α| * x ^ (θ - 2) * (γ ^ 2 + 6 * γ + 15) := by
  unfold oscD2
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set c := Real.cos (γ * Real.log x)
  set sn := Real.sin (γ * Real.log x)
  set p := Real.smoothTransition (Real.log (x / xk))
  set d := deriv Real.smoothTransition (Real.log (x / xk))
  set e := deriv (deriv Real.smoothTransition) (Real.log (x / xk))
  have hc := abs_le.mp (Real.abs_cos_le_one (γ * Real.log x))
  have hs := abs_le.mp (Real.abs_sin_le_one (γ * Real.log x))
  have hp0 : 0 ≤ p := Real.smoothTransition.nonneg _
  have hp1 : p ≤ 1 := Real.smoothTransition.le_one _
  have hd0 : 0 ≤ d := SmoothStep.deriv_smoothTransition_nonneg _
  have hd2 : d ≤ 2 := SmoothStep.deriv_smoothTransition_le_two _
  have he : |e| ≤ 10 := by
    have := BSCert.Consts.phiCut_deriv2_le (Real.log (x / xk))
    rwa [BSCert.Consts.phiCut_eq] at this
  have he' := abs_le.mp he
  -- termwise bounds
  have b1 : |θ * c * p - γ * sn * p + c * d| ≤ θ + γ + 2 := by
    have e1 : |θ * c * p| ≤ θ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hθ0, abs_of_nonneg hp0]
      have : |c| ≤ 1 := Real.abs_cos_le_one _
      have h1 : |c| * p ≤ 1 := mul_le_one₀ this hp0 hp1
      calc θ * |c| * p = θ * (|c| * p) := by ring
        _ ≤ θ := mul_le_of_le_one_right hθ0 h1
    have e2 : |γ * sn * p| ≤ γ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hγ, abs_of_nonneg hp0]
      have : |sn| ≤ 1 := Real.abs_sin_le_one _
      have h1 : |sn| * p ≤ 1 := mul_le_one₀ this hp0 hp1
      calc γ * |sn| * p = γ * (|sn| * p) := by ring
        _ ≤ γ := mul_le_of_le_one_right hγ h1
    have e3 : |c * d| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg hd0]
      have : |c| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [abs_nonneg c]
    calc _ ≤ |θ * c * p - γ * sn * p| + |c * d| := abs_add_le _ _
      _ ≤ |θ * c * p| + |γ * sn * p| + |c * d| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have b2 : |-(θ * γ) * sn * p + θ * c * d - γ ^ 2 * c * p - 2 * γ * sn * d + c * e| ≤
      γ + 2 + γ ^ 2 + 4 * γ + 10 := by
    have hc1 : |c| ≤ 1 := Real.abs_cos_le_one _
    have hs1 : |sn| ≤ 1 := Real.abs_sin_le_one _
    have f1 : |-(θ * γ) * sn * p| ≤ γ := by
      rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hθ0, abs_of_nonneg hγ,
        abs_of_nonneg hp0]
      have : θ * γ ≤ γ := by nlinarith
      have : |sn| * p ≤ 1 := by nlinarith [abs_nonneg sn]
      nlinarith [abs_nonneg sn, mul_nonneg hθ0 hγ]
    have f2 : |θ * c * d| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hθ0, abs_of_nonneg hd0]
      have : |c| * d ≤ 2 := by nlinarith [abs_nonneg c]
      nlinarith [abs_nonneg c, mul_nonneg (abs_nonneg c) hd0]
    have f3 : |γ ^ 2 * c * p| ≤ γ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg γ), abs_of_nonneg hp0]
      have : |c| * p ≤ 1 := by nlinarith [abs_nonneg c]
      nlinarith [abs_nonneg c, sq_nonneg γ, mul_nonneg (abs_nonneg c) hp0]
    have f4 : |2 * γ * sn * d| ≤ 4 * γ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ, abs_of_nonneg hd0]
      have : |sn| * d ≤ 2 := by nlinarith [abs_nonneg sn]
      norm_num
      nlinarith [abs_nonneg sn, mul_nonneg (abs_nonneg sn) hd0]
    have f5 : |c * e| ≤ 10 := by
      rw [abs_mul]; nlinarith [abs_nonneg c, abs_nonneg e]
    have t1 := abs_add_le (-(θ * γ) * sn * p + θ * c * d - γ ^ 2 * c * p - 2 * γ * sn * d)
      (c * e)
    have t2 := abs_sub (-(θ * γ) * sn * p + θ * c * d - γ ^ 2 * c * p) (2 * γ * sn * d)
    have t3 := abs_sub (-(θ * γ) * sn * p + θ * c * d) (γ ^ 2 * c * p)
    have t4 := abs_add_le (-(θ * γ) * sn * p) (θ * c * d)
    linarith
  have hθ1' : |θ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc _ ≤ |(θ - 1) * (θ * c * p - γ * sn * p + c * d)| +
        |-(θ * γ) * sn * p + θ * c * d - γ ^ 2 * c * p - 2 * γ * sn * d + c * e| :=
        abs_add_le _ _
    _ ≤ 1 * (θ + γ + 2) + (γ + 2 + γ ^ 2 + 4 * γ + 10) := by
        rw [abs_mul]; gcongr
    _ ≤ _ := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **The designed `R_k''`**: for `x⁺_k = switchOn S k` (seed `S ≥ X`), `γ_k ∈ [Γ_k, 2Γ_k]`,
`α_k = κ₀ (x⁺_k)^{1-θ}/(γ_k L)` (`κ₀ = X⁻¹`), `|R_k''(x)| ≤ 2⁻ᵏ x^{-θ}/10¹⁴` (the bound
`γ_k κ_k ≤ x_k^{1-θ}` of the `o_R` bullet of eq. (osc), with `log x⁺_k ≥ 2ᵏ X²`). -/
theorem abs_oscD2_designed_le {θ : ℝ} (hθ1 : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2) {X S : ℝ}
    (hX : 10 ^ 8 ≤ X) (hXS : X ≤ S) (k : ℕ) {γ : ℝ}
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ (Construction.kappa0Param X)
      (Construction.switchOn S k))
      (2 * DesignedZero.heightScale θ (Construction.kappa0Param X) (Construction.switchOn S k)))
    {y : ℝ} (hy : Construction.switchOn S k ≤ y) {x : ℝ} (hx : 0 < x) :
    |oscD2 θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn S k))
      γ y x| ≤ (1 / 2) ^ k * x ^ (-θ) / 10 ^ 14 := by
  set xk := Construction.switchOn S k with hxkdef
  have hxk : 0 < xk := Construction.switchOn_pos S k
  rcases le_or_gt x y with hle | hlt
  · rw [oscD2_eq_zero_of_le hx hle, abs_zero]; positivity
  replace hlt : xk < x := lt_of_le_of_lt hy hlt
  set L := Real.log xk with hLdef
  have hLk : 2 ^ k * X ^ 2 ≤ L := log_switchOn_ge_of (by linarith) hXS k
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hX2 : (10 : ℝ) ^ 16 ≤ X ^ 2 := by nlinarith
  have hL16 : 2 ^ k * 10 ^ 16 ≤ L := le_trans (by gcongr) hLk
  have hL1 : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  have hLxk : L ≤ xk := by
    have := Real.add_one_le_exp L; rw [hLdef, Real.exp_log hxk] at this; linarith
  set Γ := DesignedZero.heightScale θ (Construction.kappa0Param X) xk with hΓ
  have hX0 : 0 < X := by linarith
  have hΓ0 : 0 < Γ := by
    rw [hΓ]; unfold DesignedZero.heightScale Construction.kappa0Param; positivity
  have hγ0 : 0 < γ := lt_of_lt_of_le hΓ0 hγ.1
  set α := DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ xk with hα
  have hαγ : α * γ = 2 * Γ := by
    rw [hα, hΓ]; unfold DesignedZero.amplitudeOf DesignedZero.heightScale
    field_simp
  have hα0 : 0 < α := by
    rw [hα]; unfold DesignedZero.amplitudeOf Construction.kappa0Param; positivity
  have hα2 : α ≤ 2 := by
    have : α * γ ≤ 2 * γ := by rw [hαγ]; nlinarith [hγ.1]
    nlinarith
  set G := 2 * Γ with hG
  have hGe : G = xk ^ (1 - θ) / (X * L) := by
    rw [hG, hΓ]; unfold DesignedZero.heightScale Construction.kappa0Param; rw [← hLdef]
    field_simp
  have hγG : γ ≤ G := hγ.2
  have hb := abs_oscD2_le (θ := θ) (γ := γ) (α := α) (xk := y) (by linarith) (by linarith)
    hγ0.le hx
  rw [abs_of_pos hα0] at hb
  -- `α (γ² + 6γ + 15) ≤ G² + 6G + 30`
  have hcoef : α * (γ ^ 2 + 6 * γ + 15) ≤ G ^ 2 + 6 * G + 30 := by
    have : α * γ ^ 2 = G * γ := by rw [← hαγ]; ring
    nlinarith [mul_le_mul_of_nonneg_left hγG (show 0 ≤ G by positivity)]
  have hx2 : 0 ≤ x ^ (θ - 2) := Real.rpow_nonneg hx.le _
  have hb' : |oscD2 θ α γ y x| ≤ x ^ (θ - 2) * (G ^ 2 + 6 * G + 30) := by
    calc _ ≤ α * x ^ (θ - 2) * (γ ^ 2 + 6 * γ + 15) := hb
      _ = x ^ (θ - 2) * (α * (γ ^ 2 + 6 * γ + 15)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoef hx2
  -- rpow facts
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ xk := by linarith
    linarith
  have hpow : xk ^ (1 - θ) ≤ x ^ (1 - θ) :=
    Real.rpow_le_rpow hxk.le hlt.le (by linarith)
  have hq0 : 0 ≤ xk ^ (1 - θ) := Real.rpow_nonneg hxk.le _
  have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hG0 : 0 ≤ G := by positivity
  set m := x ^ (-θ) with hm
  have hm0 : 0 ≤ m := Real.rpow_nonneg hx.le _
  have hXL : L ≤ X * L := le_mul_of_one_le_left hL0.le (by linarith)
  -- `x^{θ-2} G² ≤ m / L`
  have e1 : x ^ (θ - 2) * G ^ 2 ≤ m / L := by
    rw [hGe]
    have : x ^ (θ - 2) * (x ^ (1 - θ)) ^ 2 = m := by
      rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]; ring_nf
    have hsq : (xk ^ (1 - θ)) ^ 2 ≤ (x ^ (1 - θ)) ^ 2 := pow_le_pow_left₀ hq0 hpow 2
    have hXL2 : L ≤ (X * L) ^ 2 := by nlinarith
    calc x ^ (θ - 2) * (xk ^ (1 - θ) / (X * L)) ^ 2 =
          x ^ (θ - 2) * (xk ^ (1 - θ)) ^ 2 / (X * L) ^ 2 := by ring
      _ ≤ x ^ (θ - 2) * (x ^ (1 - θ)) ^ 2 / (X * L) ^ 2 := by gcongr
      _ = m / (X * L) ^ 2 := by rw [this]
      _ ≤ m / L := div_le_div_of_nonneg_left hm0 hL0 hXL2
  -- `x^{θ-2} G ≤ m / L` (as `x^{θ-2} x^{1-θ} = x^{-1} ≤ x^{-θ}`)
  have hinv : x ^ (-(1 : ℝ)) ≤ m := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have e2 : x ^ (θ - 2) * G ≤ m / L := by
    rw [hGe]
    have : x ^ (θ - 2) * x ^ (1 - θ) = x ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hx]; ring_nf
    calc x ^ (θ - 2) * (xk ^ (1 - θ) / (X * L)) =
          x ^ (θ - 2) * xk ^ (1 - θ) / (X * L) := by ring
      _ ≤ x ^ (θ - 2) * x ^ (1 - θ) / (X * L) := by gcongr
      _ ≤ m / (X * L) := by rw [this]; gcongr
      _ ≤ m / L := div_le_div_of_nonneg_left hm0 hL0 hXL
  -- `x^{θ-2} ≤ m / L` (as `x^{2θ-2} ≤ x⁻¹ ≤ 1/x_k ≤ 1/L`)
  have e3 : x ^ (θ - 2) ≤ m / L := by
    have h1 : x ^ (θ - 2) = m * x ^ (2 * θ - 2) := by
      rw [hm, ← Real.rpow_add hx]; ring_nf
    have h2 : x ^ (2 * θ - 2) ≤ x ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h3 : x ^ (-(1 : ℝ)) ≤ 1 / L := by
      rw [Real.rpow_neg_one, one_div]
      exact inv_anti₀ hL0 (hLxk.trans hlt.le)
    rw [h1, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) hm0
  have hL6 : L ≤ L ^ 6 := le_self_pow₀ hL1 (by norm_num)
  have hL3' : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
  have hsum : x ^ (θ - 2) * (G ^ 2 + 6 * G + 30) ≤ 37 * m / L := by
    have : x ^ (θ - 2) * (G ^ 2 + 6 * G + 30) =
        x ^ (θ - 2) * G ^ 2 + 6 * (x ^ (θ - 2) * G) + 30 * x ^ (θ - 2) := by ring
    rw [this]
    have : 37 * m / L = m / L + 6 * (m / L) + 30 * (m / L) := by ring
    have : 0 ≤ m / L := by positivity
    linarith
  have hfin : 37 * m / L ≤ (1 / 2) ^ k * x ^ (-θ) / 10 ^ 14 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have hq : 0 ≤ x ^ (-θ) := Real.rpow_nonneg hx.le _
    have h2 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
      rw [← mul_pow]; norm_num
    have : (1 / 2 : ℝ) ^ k * x ^ (-θ) * L ≥
        (1 / 2) ^ k * x ^ (-θ) * (2 ^ k * 10 ^ 16) :=
      mul_le_mul_of_nonneg_left hL16 (by positivity)
    have e : (1 / 2 : ℝ) ^ k * x ^ (-θ) * (2 ^ k * 10 ^ 16) =
        x ^ (-θ) * 10 ^ 16 := by
      rw [show (1 / 2 : ℝ) ^ k * x ^ (-θ) * (2 ^ k * 10 ^ 16) =
        ((1 / 2) ^ k * 2 ^ k) * x ^ (-θ) * 10 ^ 16 by ring, h2, one_mul]
    rw [← hm] at e this ⊢
    nlinarith
  exact hb'.trans (hsum.trans hfin)

/-- **Mean value step for one oscillation**: `|R_k'(t) - R_k'(s)| ≤ (t - s) 2⁻ᵏ s^{-θ}/10¹⁴`
for `0 < s ≤ t`. -/
theorem oscD_sub_le {θ : ℝ} (hθ1 : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2) {X S : ℝ} (hX : 10 ^ 8 ≤ X)
    (hXS : X ≤ S) (k : ℕ) {γ : ℝ}
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ (Construction.kappa0Param X)
      (Construction.switchOn S k))
      (2 * DesignedZero.heightScale θ (Construction.kappa0Param X) (Construction.switchOn S k)))
    {y : ℝ} (hy : Construction.switchOn S k ≤ y) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    |oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn S k))
        γ y t -
      oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn S k))
        γ y s| ≤
      (t - s) * ((1 / 2) ^ k * s ^ (-θ) / 10 ^ 14) := by
  have hxk := Construction.switchOn_pos S k
  have hy0 : 0 < y := lt_of_lt_of_le hxk hy
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ
      (Construction.switchOn S k)) γ y)
    (f' := oscD2 θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ
      (Construction.switchOn S k)) γ y)
    (s := Icc s t) (C := (1 / 2) ^ k * s ^ (-θ) / 10 ^ 14)
    (fun x hx => (hasDerivAt_oscD (lt_of_lt_of_le hs hx.1) hy0).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      rw [Real.norm_eq_abs]
      refine (abs_oscD2_designed_le hθ1 hθ2 hX hXS k hγ hy hx0).trans ?_
      have : x ^ (-θ) ≤ s ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos hs hx.1 (by linarith)
      gcongr)
    (convex_Icc s t) (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h
  linarith

/-- `R'` as the finite sum `∑_{k<K} R_k'` on `(0, x⁺_K)`. -/
lemma deriv_osc_eq_sum {θ : ℝ} (α γ : ℕ → ℝ) (X : ℝ) (hX : 1 ≤ X) {K : ℕ} {y : ℝ}
    (hy : 0 < y) (hyK : y < Construction.switchOn X K) :
    deriv (Oscillation.osc θ α γ (Construction.switchOn X)) y =
      ∑ k ∈ Finset.range K, RkD θ (α k) (γ k) (Construction.switchOn X k) y := by
  have hsum : HasDerivAt (fun z => ∑ k ∈ Finset.range K,
      Oscillation.oscK θ (α k) (γ k) (Construction.switchOn X k) z)
      (∑ k ∈ Finset.range K, RkD θ (α k) (γ k) (Construction.switchOn X k) y) y :=
    HasDerivAt.fun_sum fun k _ => by
      rw [← deriv_oscK_eq hy (Construction.switchOn_pos X k)]
      exact Oscillation.hasDerivAt_oscK θ _ _ (Construction.switchOn_pos X k) hy
  refine (hsum.congr_of_eventuallyEq ?_).deriv
  filter_upwards [Ioo_mem_nhds hy hyK] with z hz
  exact osc_eq_finsum α γ X hz.1 hz.2.le

/-- The modulus density of the design `θ = 0` (Theorem A′):
`g(x) = exp(-9 (log log x - 1.1)²)`. On the active window `(x⁺_k, e (x⁺_k)²)` of the `k`-th
oscillation, `x^{-θ_k} ≤ g(x)` (`rpow_neg_thK_le_gS`). -/
noncomputable def gS (x : ℝ) : ℝ := Real.exp (-(9 * (Real.log (Real.log x) - 1.1) ^ 2))

/-- The modulus density of the design: `s^{-θ}` for `θ ≠ 0`, `gS s` for `θ = 0`. -/
noncomputable def mS (θ s : ℝ) : ℝ := if θ = 0 then gS s else s ^ (-θ)

lemma mS_nonneg (θ : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ mS θ s := by
  unfold mS gS; split_ifs
  · positivity
  · exact Real.rpow_nonneg hs _

/-- `gS` is non-increasing beyond `log log x = 1.1`. -/
lemma gS_anti {a b : ℝ} (ha1 : 1 < a) (ha : 1.1 ≤ Real.log (Real.log a)) (hab : a ≤ b) :
    gS b ≤ gS a := by
  unfold gS
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hLa : 0 < Real.log a := Real.log_pos ha1
  have hL : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hl : Real.log (Real.log a) ≤ Real.log (Real.log b) := Real.log_le_log hLa hL
  have h0 : 0 ≤ Real.log (Real.log a) - 1.1 := by linarith
  have := pow_le_pow_left₀ h0 (show Real.log (Real.log a) - 1.1 ≤ Real.log (Real.log b) - 1.1 by
    linarith) 2
  linarith

lemma mS_anti {θ : ℝ} (hθ : 0 ≤ θ) {a b : ℝ} (ha1 : 1 < a) (ha : 1.1 ≤ Real.log (Real.log a))
    (hab : a ≤ b) : mS θ b ≤ mS θ a := by
  unfold mS; split_ifs
  · exact gS_anti ha1 ha hab
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)

/-- `log 3 < 1.1`. -/
lemma log_three_lt : Real.log 3 < 1.1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.1 by norm_num)
  have e : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith

/-- **On the active window of the `k`-th oscillation** of the design `θ = 0`,
`x^{-θ_k} ≤ g(x)`: from `θ_k log x ≥ θ_k L_k = 9ℓ_k²` and `log log x ≤ ℓ_k + log 3`. -/
lemma rpow_neg_thK_le_gS {xk x : ℝ} (hxk0 : 0 < xk) (hL1 : 1 ≤ Real.log xk)
    (hℓ : 1.1 ≤ Real.log (Real.log xk)) (hx : xk < x) (hx2 : x < Real.exp 1 * xk ^ 2) :
    x ^ (-thK 0 xk) ≤ gS x := by
  set L := Real.log xk with hLdef
  set ℓ := Real.log L with hℓdef
  have hx0 : 0 < x := lt_trans hxk0 hx
  have hL0 : 0 < L := by linarith
  have hlx1 : L < Real.log x := Real.log_lt_log hxk0 hx
  have hlx2 : Real.log x < 1 + 2 * L := by
    have h := Real.log_lt_log hx0 hx2
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow] at h
    push_cast at h; linarith
  have hlx3 : Real.log x ≤ 3 * L := by linarith
  have hℓx1 : ℓ ≤ Real.log (Real.log x) := Real.log_le_log hL0 hlx1.le
  have hℓx2 : Real.log (Real.log x) ≤ ℓ + 1.1 := by
    have := Real.log_le_log (by linarith) hlx3
    rw [Real.log_mul (by norm_num) hL0.ne'] at this
    linarith [log_three_lt]
  rw [thK_zero, Real.rpow_def_of_pos hx0]
  unfold gS
  rw [Real.exp_le_exp]
  have h1 : 9 * ℓ ^ 2 / L * L ≤ 9 * ℓ ^ 2 / L * Real.log x :=
    mul_le_mul_of_nonneg_left hlx1.le (by positivity)
  rw [div_mul_cancel₀ _ hL0.ne'] at h1
  have h0 : 0 ≤ Real.log (Real.log x) - 1.1 := by linarith
  have h2 : (Real.log (Real.log x) - 1.1) ^ 2 ≤ ℓ ^ 2 :=
    pow_le_pow_left₀ h0 (by linarith) 2
  nlinarith

/-- The modulus of `R'` on `[s, t]` (§5, eq. (osc), the `o_R` bullet): `0` if `t ≤ x⁺_0`
(`R' = 0` on `(0, x⁺_0]`), else `m(max(s, x⁺_0))/10¹³` with the modulus density `m = mS θ`. -/
noncomputable def oscMod (θ : ℝ) (X₀ : ℕ) (s t : ℝ) : ℝ :=
  if t ≤ Construction.switchOn (swS θ X₀) 0 then 0
  else mS θ (max s (Construction.switchOn (swS θ X₀) 0)) / 10 ^ 13

lemma oscMod_nonneg (θ : ℝ) (X₀ : ℕ) {s t : ℝ} (hs : 0 ≤ s) : 0 ≤ oscMod θ X₀ s t := by
  unfold oscMod
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mS_nonneg θ (le_trans hs (le_max_left _ _))) (by norm_num)

/-- **The `R''` of a switched-off oscillation** (design `θ = 0`): for the designed heights and
amplitudes, `|R_k''(x)| ≤ 2·2⁻ᵏ g(x)/10¹⁴` (`R_k'' = 0` off the active window
`(x⁺_k, e (x⁺_k)²)`, and `x^{-θ_k} ≤ g(x)` on it). -/
theorem abs_oscD2_zero_le {X S : ℝ} (hX : 10 ^ 8 ≤ X) (hXS : X ≤ S) (k : ℕ) {γ : ℝ}
    (hγ : γ ∈ Icc (DesignedZero.heightScale (thK 0 (Construction.switchOn S k))
      (Construction.kappa0Param X) (Construction.switchOn S k))
      (2 * DesignedZero.heightScale (thK 0 (Construction.switchOn S k))
        (Construction.kappa0Param X) (Construction.switchOn S k)))
    {x : ℝ} (hx : 0 < x) :
    |oscD2 (thK 0 (Construction.switchOn S k)) (DesignedZero.amplitudeOf
        (thK 0 (Construction.switchOn S k)) (Construction.kappa0Param X) γ
        (Construction.switchOn S k)) γ (Construction.switchOn S k) x -
      oscD2 (thK 0 (Construction.switchOn S k)) (DesignedZero.amplitudeOf
        (thK 0 (Construction.switchOn S k)) (Construction.kappa0Param X) γ
        (Construction.switchOn S k)) γ
        (Construction.switchOn S k * max (Construction.switchOn S k) 1) x| ≤
      2 * ((1 / 2) ^ k * gS x / 10 ^ 14) := by
  set xk := Construction.switchOn S k with hxkdef
  set t := thK 0 xk with htdef
  have hxk : 0 < xk := Construction.switchOn_pos S k
  have hLk : 2 ^ k * X ^ 2 ≤ Real.log xk := log_switchOn_ge_of (by linarith) hXS k
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hL : X ^ 2 ≤ Real.log xk := le_trans (le_mul_of_one_le_left (by positivity) h2k) hLk
  have hL1 : 1 ≤ Real.log xk := by nlinarith
  have hxk1 : 1 ≤ xk := by
    have := Real.add_one_le_exp (Real.log xk); rw [Real.exp_log hxk] at this; linarith
  have hyk : xk * max xk 1 = xk ^ 2 := by rw [max_eq_left hxk1]; ring
  have hℓ : 1.1 ≤ Real.log (Real.log xk) := by
    have h1 : Real.log (X ^ 2) ≤ Real.log (Real.log xk) := Real.log_le_log (by positivity) hL
    rw [Real.log_pow] at h1
    have : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    push_cast at h1; linarith
  have ht0 : 0 ≤ t := by
    rw [htdef, thK_zero]
    have : 0 ≤ Real.log (Real.log xk) := by linarith
    positivity
  have ht2 : t ≤ 1 / 2 := by
    have := thK_zero_le (show 1 < xk by
      have := Real.add_one_le_exp (Real.log xk); rw [Real.exp_log hxk] at this; linarith)
      (by
        have h1 : Real.log (X ^ 2) ≤ Real.log (Real.log xk) := Real.log_le_log (by positivity) hL
        rw [Real.log_pow] at h1
        have : 10 ≤ Real.log X := by
          rw [Real.le_log_iff_exp_le (by linarith)]
          have h10 : Real.exp 10 ≤ 10 ^ 8 := by
            have := Real.exp_one_lt_d9
            calc Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
              _ ≤ 2.7182818286 ^ 10 := by gcongr
              _ ≤ 10 ^ 8 := by norm_num
          linarith
        push_cast at h1; linarith)
    linarith
  have hg0 : 0 ≤ gS x := by unfold gS; positivity
  have hxk2 : xk ≤ xk * max xk 1 := le_mul_of_one_le_right hxk.le (le_max_right _ _)
  rcases le_or_gt x xk with h1 | h1
  · rw [oscD2_eq_zero_of_le hx h1, oscD2_eq_zero_of_le hx (h1.trans hxk2), sub_zero, abs_zero]
    positivity
  rcases le_or_gt (Real.exp 1 * xk ^ 2) x with h2 | h2
  · have hl1 : 1 ≤ Real.log (x / xk) := by
      rw [Real.le_log_iff_exp_le (div_pos hx hxk), le_div_iff₀ hxk]
      nlinarith [Real.exp_pos 1]
    have hl2 : 1 ≤ Real.log (x / (xk * max xk 1)) := by
      rw [hyk, Real.le_log_iff_exp_le (div_pos hx (by positivity)), le_div_iff₀ (by positivity)]
      linarith
    rw [oscD2_eq_of_one_le hl1 hl2, sub_self, abs_zero]
    positivity
  have hA := abs_oscD2_designed_le ht0 ht2 hX hXS k hγ le_rfl hx
  have hB := abs_oscD2_designed_le ht0 ht2 hX hXS k hγ hxk2 hx
  have hr := rpow_neg_thK_le_gS hxk hL1 hℓ h1 h2
  have hq : (1 / 2 : ℝ) ^ k * x ^ (-t) / 10 ^ 14 ≤ (1 / 2) ^ k * gS x / 10 ^ 14 := by
    gcongr
  calc _ ≤ _ := abs_sub _ _
    _ ≤ (1 / 2) ^ k * x ^ (-t) / 10 ^ 14 + (1 / 2) ^ k * x ^ (-t) / 10 ^ 14 := add_le_add hA hB
    _ ≤ _ := by linarith

/-- `R' = 0` on `(0, x⁺_0]`. -/
lemma deriv_osc_eq_zero_of_le {θ : ℝ} (α γ : ℕ → ℝ) (S : ℝ) (hS : 1 ≤ S) {y : ℝ} (hy : 0 < y)
    (hyx : y ≤ Construction.switchOn S 0) :
    deriv (Oscillation.osc θ α γ (Construction.switchOn S)) y = 0 := by
  set K := ⌈y⌉₊ + 1 with hK
  have hyK : y < Construction.switchOn S K := by
    have := nat_lt_switchOn hS K
    have : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    push_cast [K] at *
    linarith
  rw [(hasDerivAt_osc α γ hS hy).deriv]
  refine Finset.sum_eq_zero fun k _ => ?_
  exact deriv_oscK_of_le hy (hyx.trans (Construction.switchOn_mono S (Nat.zero_le k)))

/-- **The `R'` modulus** (§5, eq. (osc), the `o_R` bullet): for `X₀ ≤ s ≤ t`,
`|R'(t) - R'(s)| ≤ (t - s) · oscMod θ X₀ s t`, from `|R''(x)| ≤ ∑_k 2⁻ᵏ x^{-θ}/10¹⁴` beyond
`x⁺_0` and `R' = 0` on `(0, x⁺_0]`. -/
theorem deriv_osc_sub_le {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) {s t : ℝ}
    (hs : (X₀ : ℝ) ≤ s) (hst : s ≤ t) :
    |deriv (Oscillation.osc θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
        (Construction.switchOn (swS θ X₀)) γ) γ (Construction.switchOn (swS θ X₀))) t -
      deriv (Oscillation.osc θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
        (Construction.switchOn (swS θ X₀)) γ) γ (Construction.switchOn (swS θ X₀))) s| ≤
      (t - s) * oscMod θ X₀ s t := by
  set X : ℝ := (X₀ : ℝ) with hXdef
  set S : ℝ := swS θ X with hSdef
  have hXS : X ≤ S := le_swS θ X
  have hX1 : 1 < X := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX2 : (10 : ℝ) ^ 8 ≤ X := by
    have := Real.add_one_le_exp (Real.log X); rw [Real.exp_log (by linarith)] at this; linarith
  have hS1 : 1 ≤ S := by linarith
  have hθ1 : 0 ≤ θ := hθ.1
  have hθ2 : θ ≤ 1 / 2 := by linarith [hθ.2]
  set α := Construction.amplitudes θ (Construction.kappa0Param X₀) (Construction.switchOn S) γ
  set R' := deriv (Oscillation.osc θ α γ (Construction.switchOn S)) with hR'
  set x0 := Construction.switchOn S 0 with hx0
  have hlogX : 10 ^ 8 ≤ Real.log X := hX
  -- `log log s ≥ 1.1` beyond `X₀`
  have hll : ∀ s, X ≤ s → 1.1 ≤ Real.log (Real.log s) := fun s hs => by
    have h1 : 10 ^ 8 ≤ Real.log s := hlogX.trans (Real.log_le_log (by linarith) hs)
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have e : Real.exp 1.1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have e3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr
    linarith [show (2.7182818286 : ℝ) ^ 2 ≤ 10 ^ 8 by norm_num]
  -- the step beyond the switch-on: `|R'(t) - R'(s)| ≤ (t - s) m(s)/10¹³` for `X₀ ≤ s ≤ t`
  have hbase : ∀ s t : ℝ, X ≤ s → s ≤ t → |R' t - R' s| ≤ (t - s) * (mS θ s / 10 ^ 13) := by
    intro s t hsX hst
    have hs0 : 0 < s := by linarith
    have ht0 : 0 < t := by linarith
    set K := ⌈t⌉₊ + 1 with hK
    have htK : t < Construction.switchOn S K := by
      have := nat_lt_switchOn hS1 K
      have : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      push_cast [K] at *
      linarith
    have hsK : s < Construction.switchOn S K := lt_of_le_of_lt hst htK
    rw [hR', deriv_osc_eq_sum _ _ S hS1 ht0 htK, deriv_osc_eq_sum _ _ S hS1 hs0 hsK,
      ← Finset.sum_sub_distrib]
    by_cases hθne : θ = 0
    · -- the design `θ = 0`: the switched-off oscillations, with the modulus density `g`
      subst hθne
      have hg : 0 ≤ gS s := by unfold gS; positivity
      have hstep : ∀ k, |RkD 0 (α k) (γ k) (Construction.switchOn S k) t -
          RkD 0 (α k) (γ k) (Construction.switchOn S k) s| ≤
          (t - s) * (2 * ((1 / 2) ^ k * gS s / 10 ^ 14)) := by
        intro k
        set xk := Construction.switchOn S k with hxk
        have hxk0 : 0 < xk := Construction.switchOn_pos S k
        have hy0 : 0 < xk * max xk 1 :=
          mul_pos hxk0 (lt_of_lt_of_le one_pos (le_max_right _ _))
        have hf : ∀ x, RkD 0 (α k) (γ k) xk x = oscD (thK 0 xk) (α k) (γ k) xk x -
            oscD (thK 0 xk) (α k) (γ k) (xk * max xk 1) x := fun x => by
          simp [RkD]
        have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun x => oscD (thK 0 xk) (α k) (γ k) xk x -
            oscD (thK 0 xk) (α k) (γ k) (xk * max xk 1) x)
          (f' := fun x => oscD2 (thK 0 xk) (α k) (γ k) xk x -
            oscD2 (thK 0 xk) (α k) (γ k) (xk * max xk 1) x)
          (s := Icc s t) (C := 2 * ((1 / 2) ^ k * gS s / 10 ^ 14))
          (fun x hx => ((hasDerivAt_oscD (lt_of_lt_of_le hs0 hx.1) hxk0).sub
            (hasDerivAt_oscD (lt_of_lt_of_le hs0 hx.1) hy0)).hasDerivWithinAt)
          (fun x hx => by
            have hx0 : 0 < x := lt_of_lt_of_le hs0 hx.1
            rw [Real.norm_eq_abs]
            refine (abs_oscD2_zero_le hX2 hXS k (hγ k) hx0).trans ?_
            have := gS_anti (by linarith) (hll s hsX) hx.1
            gcongr)
          (convex_Icc s t) (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h
        rw [hf, hf]
        linarith
      calc _ ≤ ∑ k ∈ Finset.range K, |RkD 0 (α k) (γ k) (Construction.switchOn S k) t -
            RkD 0 (α k) (γ k) (Construction.switchOn S k) s| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range K, (t - s) * (2 * ((1 / 2) ^ k * gS s / 10 ^ 14)) :=
            Finset.sum_le_sum fun k _ => hstep k
        _ = (t - s) * gS s / 10 ^ 14 * 2 * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
        _ ≤ (t - s) * gS s / 10 ^ 14 * 2 * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le K)
              (by have : 0 ≤ t - s := by linarith
                  positivity)
        _ ≤ (t - s) * (mS 0 s / 10 ^ 13) := by
            have : 0 ≤ (t - s) * gS s := mul_nonneg (by linarith) hg
            rw [show mS 0 s = gS s from if_pos rfl]
            have e : (t - s) * gS s / 10 ^ 14 * 2 * 2 = ((t - s) * gS s) * (4 / 10 ^ 14) := by
              ring
            have e' : (t - s) * (gS s / 10 ^ 13) = ((t - s) * gS s) * (1 / 10 ^ 13) := by ring
            rw [e, e']
            exact mul_le_mul_of_nonneg_left (by norm_num) this
    · simp only [RkD_of_ne hθne]
      have hq : 0 ≤ s ^ (-θ) := Real.rpow_nonneg hs0.le _
      calc _ ≤ ∑ k ∈ Finset.range K, |oscD θ (α k) (γ k) (Construction.switchOn S k) t -
            oscD θ (α k) (γ k) (Construction.switchOn S k) s| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range K, (t - s) * ((1 / 2) ^ k * s ^ (-θ) / 10 ^ 14) :=
            Finset.sum_le_sum fun k _ => by
              have hk := oscD_sub_le hθ1 hθ2 hX2 hXS k
                (by simpa [thK_of_ne hθne] using hγ k) le_rfl hs0 hst
              simpa [α, Construction.amplitudes, thK_of_ne hθne] using hk
        _ = (t - s) * s ^ (-θ) / 10 ^ 14 * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
        _ ≤ (t - s) * s ^ (-θ) / 10 ^ 14 * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le K)
              (by have : 0 ≤ t - s := by linarith
                  positivity)
        _ ≤ (t - s) * (mS θ s / 10 ^ 13) := by
            have : 0 ≤ (t - s) * s ^ (-θ) := mul_nonneg (by linarith) hq
            simp only [mS, if_neg hθne]
            nlinarith
  have hs0 : 0 < s := by linarith
  have hx00 : 0 < x0 := Construction.switchOn_pos S 0
  have hx0X : X ≤ x0 := switchOn_zero_ge_swS θ X
  have hzero : ∀ y, 0 < y → y ≤ x0 → R' y = 0 := fun y hy hyx =>
    deriv_osc_eq_zero_of_le α γ S hS1 hy hyx
  unfold oscMod
  rw [← hSdef, ← hx0]
  split_ifs with htx
  · rw [hzero t (by linarith) htx, hzero s hs0 (hst.trans htx)]; simp
  · push_neg at htx
    rcases le_total x0 s with hxs | hsx
    · rw [max_eq_left hxs]; exact hbase s t hs hst
    · rw [max_eq_right hsx, hzero s hs0 hsx]
      have h := hbase x0 t hx0X htx.le
      rw [hzero x0 hx00 le_rfl] at h
      have hq : 0 ≤ mS θ x0 / 10 ^ 13 := div_nonneg (mS_nonneg θ hx00.le) (by norm_num)
      calc |R' t - 0| ≤ (t - x0) * (mS θ x0 / 10 ^ 13) := h
        _ ≤ (t - s) * (mS θ x0 / 10 ^ 13) :=
            mul_le_mul_of_nonneg_right (by linarith) hq

end BModel

end
