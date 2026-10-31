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
  `|R_k''(x)| ≤ 2⁻ᵏ x^{-1/4} / 10¹⁴`;
* `deriv_osc_sub_le` : `|R'(t) - R'(s)| ≤ (t - s) s^{-1/4}` for `X₀ ≤ s ≤ t`.
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
/-- **The designed `R_k''`**: for `x⁺_k = switchOn X₀ k`, `γ_k ∈ [Γ_k, 2Γ_k]`,
`α_k = κ₀ (x⁺_k)^{1-θ}/(γ_k L)` (`κ₀ = X⁻¹`), `|R_k''(x)| ≤ 2⁻ᵏ x^{-1/4}/10¹⁴` (the bound
`γ_k κ_k ≤ x_k^{1-θ}` of the `o_R` bullet of eq. (osc), with `log x⁺_k ≥ 2ᵏ X₀²`). -/
theorem abs_oscD2_designed_le {θ : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2) {X : ℝ}
    (hX : 10 ^ 8 ≤ X) (k : ℕ) {γ : ℝ}
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ (Construction.kappa0Param X)
      (Construction.switchOn X k))
      (2 * DesignedZero.heightScale θ (Construction.kappa0Param X) (Construction.switchOn X k)))
    {x : ℝ} (hx : 0 < x) :
    |oscD2 θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn X k))
      γ (Construction.switchOn X k) x| ≤ (1 / 2) ^ k * x ^ (-(1 / 4 : ℝ)) / 10 ^ 14 := by
  set xk := Construction.switchOn X k with hxkdef
  have hxk : 0 < xk := Construction.switchOn_pos X k
  rcases le_or_gt x xk with hle | hlt
  · rw [oscD2_eq_zero_of_le hx hle, abs_zero]; positivity
  set L := Real.log xk with hLdef
  have hLk : 2 ^ k * X ^ 2 ≤ L := log_switchOn_ge X k
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
  have hb := abs_oscD2_le (θ := θ) (γ := γ) (α := α) (xk := xk) (by linarith) (by linarith)
    hγ0.le hx
  rw [abs_of_pos hα0] at hb
  -- `α (γ² + 6γ + 15) ≤ G² + 6G + 30`
  have hcoef : α * (γ ^ 2 + 6 * γ + 15) ≤ G ^ 2 + 6 * G + 30 := by
    have : α * γ ^ 2 = G * γ := by rw [← hαγ]; ring
    nlinarith [mul_le_mul_of_nonneg_left hγG (show 0 ≤ G by positivity)]
  have hx2 : 0 ≤ x ^ (θ - 2) := Real.rpow_nonneg hx.le _
  have hb' : |oscD2 θ α γ xk x| ≤ x ^ (θ - 2) * (G ^ 2 + 6 * G + 30) := by
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
  have hmq : m ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hfin : 37 * m / L ≤ (1 / 2) ^ k * x ^ (-(1 / 4 : ℝ)) / 10 ^ 14 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have hq : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
    have h2 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
      rw [← mul_pow]; norm_num
    have : (1 / 2 : ℝ) ^ k * x ^ (-(1 / 4 : ℝ)) * L ≥
        (1 / 2) ^ k * x ^ (-(1 / 4 : ℝ)) * (2 ^ k * 10 ^ 16) :=
      mul_le_mul_of_nonneg_left hL16 (by positivity)
    have e : (1 / 2 : ℝ) ^ k * x ^ (-(1 / 4 : ℝ)) * (2 ^ k * 10 ^ 16) =
        x ^ (-(1 / 4 : ℝ)) * 10 ^ 16 := by
      rw [show (1 / 2 : ℝ) ^ k * x ^ (-(1 / 4 : ℝ)) * (2 ^ k * 10 ^ 16) =
        ((1 / 2) ^ k * 2 ^ k) * x ^ (-(1 / 4 : ℝ)) * 10 ^ 16 by ring, h2, one_mul]
    nlinarith
  exact hb'.trans (hsum.trans hfin)

/-- **Mean value step for one oscillation**: `|R_k'(t) - R_k'(s)| ≤ (t - s) 2⁻ᵏ s^{-1/4}/10¹⁴`
for `0 < s ≤ t`. -/
theorem oscD_sub_le {θ : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2) {X : ℝ} (hX : 10 ^ 8 ≤ X)
    (k : ℕ) {γ : ℝ}
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ (Construction.kappa0Param X)
      (Construction.switchOn X k))
      (2 * DesignedZero.heightScale θ (Construction.kappa0Param X) (Construction.switchOn X k)))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    |oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn X k))
        γ (Construction.switchOn X k) t -
      oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ (Construction.switchOn X k))
        γ (Construction.switchOn X k) s| ≤
      (t - s) * ((1 / 2) ^ k * s ^ (-(1 / 4 : ℝ)) / 10 ^ 14) := by
  have hxk := Construction.switchOn_pos X k
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := oscD θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ
      (Construction.switchOn X k)) γ (Construction.switchOn X k))
    (f' := oscD2 θ (DesignedZero.amplitudeOf θ (Construction.kappa0Param X) γ
      (Construction.switchOn X k)) γ (Construction.switchOn X k))
    (s := Icc s t) (C := (1 / 2) ^ k * s ^ (-(1 / 4 : ℝ)) / 10 ^ 14)
    (fun x hx => (hasDerivAt_oscD (lt_of_lt_of_le hs hx.1) hxk).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      rw [Real.norm_eq_abs]
      refine (abs_oscD2_designed_le hθ1 hθ2 hX k hγ hx0).trans ?_
      have : x ^ (-(1 / 4 : ℝ)) ≤ s ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs hx.1 (by norm_num)
      gcongr)
    (convex_Icc s t) (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h
  linarith

/-- `R'` as the finite sum `∑_{k<K} R_k'` on `(0, x⁺_K)`. -/
lemma deriv_osc_eq_sum {θ : ℝ} (α γ : ℕ → ℝ) (X : ℝ) {K : ℕ} {y : ℝ} (hy : 0 < y)
    (hyK : y < Construction.switchOn X K) :
    deriv (Oscillation.osc θ α γ (Construction.switchOn X)) y =
      ∑ k ∈ Finset.range K, oscD θ (α k) (γ k) (Construction.switchOn X k) y := by
  have hsum : HasDerivAt (fun z => ∑ k ∈ Finset.range K,
      Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k) z)
      (∑ k ∈ Finset.range K, oscD θ (α k) (γ k) (Construction.switchOn X k) y) y :=
    HasDerivAt.fun_sum fun k _ =>
      Oscillation.hasDerivAt_oscTerm hy (Construction.switchOn_pos X k)
  refine (hsum.congr_of_eventuallyEq ?_).deriv
  filter_upwards [Ioo_mem_nhds hy hyK] with z hz
  exact osc_eq_finsum α γ X hz.1 hz.2.le

/-- **The `R'` modulus** (§5, eq. (osc), the `o_R` bullet): for `X₀ ≤ s ≤ t`,
`|R'(t) - R'(s)| ≤ (t - s) s^{-1/4}`, from `|R''(x)| ≤ ∑_k 2⁻ᵏ x^{-1/4}/10¹⁴`. -/
theorem deriv_osc_sub_le {θ : ℝ} (hθ : θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) {s t : ℝ}
    (hs : (X₀ : ℝ) ≤ s) (hst : s ≤ t) :
    |deriv (Oscillation.osc θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) t -
      deriv (Oscillation.osc θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) s| ≤
      (t - s) * s ^ (-(1 / 4 : ℝ)) := by
  set X : ℝ := (X₀ : ℝ) with hXdef
  have hX1 : 1 < X := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX2 : (10 : ℝ) ^ 8 ≤ X := by
    have := Real.add_one_le_exp (Real.log X); rw [Real.exp_log (by linarith)] at this; linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  set K := ⌈t⌉₊ + 1 with hK
  have htK : t < Construction.switchOn X K := by
    have := nat_lt_switchOn hX1.le K
    have : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    push_cast [K] at *
    linarith
  have hsK : s < Construction.switchOn X K := lt_of_le_of_lt hst htK
  rw [deriv_osc_eq_sum _ _ X ht0 htK, deriv_osc_eq_sum _ _ X hs0 hsK, ← Finset.sum_sub_distrib]
  have hθ1 : 1 / 4 ≤ θ := hθ.1
  have hθ2 : θ ≤ 1 / 2 := by linarith [hθ.2]
  have hq : 0 ≤ s ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hs0.le _
  calc _ ≤ ∑ k ∈ Finset.range K, |oscD θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
          (Construction.switchOn X) γ k) (γ k) (Construction.switchOn X k) t -
        oscD θ (Construction.amplitudes θ (Construction.kappa0Param X₀)
          (Construction.switchOn X) γ k) (γ k) (Construction.switchOn X k) s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, (t - s) * ((1 / 2) ^ k * s ^ (-(1 / 4 : ℝ)) / 10 ^ 14) :=
        Finset.sum_le_sum fun k _ => oscD_sub_le hθ1 hθ2 hX2 k (hγ k) hs0 hst
    _ = (t - s) * s ^ (-(1 / 4 : ℝ)) / 10 ^ 14 * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ (t - s) * s ^ (-(1 / 4 : ℝ)) / 10 ^ 14 * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le K)
          (by have : 0 ≤ t - s := by linarith
              positivity)
    _ ≤ (t - s) * s ^ (-(1 / 4 : ℝ)) := by
        have : 0 ≤ (t - s) * s ^ (-(1 / 4 : ℝ)) := mul_nonneg (by linarith) hq
        nlinarith

end BModel
