module

public import RequestProject.Beurling.Construction.JitterRegular

/-!
# The oscillation below `a_k`: slope bounds (proof of Lemma 4.8(ii))

On `(0, x⁺_k]` the oscillation is `R = ∑_{j<k} R_j` (`osc_eq_oscPart`). Each `R_j` vanishes on
`(0, x⁺_j]` and has slope `|R_j'| ≤ |α_j| (x⁺_j)^{θ-1} (|θ| + |γ_j| + 2)` (`oscLip`) beyond it. For
the designed heights (`γ_j ≤ 2Γ_j`) the slopes sum to at most `1/100` (`sum_oscLip_switchOn_le`);
this is the bound `|R'| ≤ 0.01` behind `T'_cont ≤ 1.01` in the proof of Lemma 4.8(ii).
-/

@[expose] public section

open Set Finset MeasureTheory Oscillation Construction

namespace Zeros48

/-- The slope bound `|α| (x⁺)^{θ-1} (|θ| + |γ| + 2)` of one oscillation `R_j`. -/
noncomputable def oscLip (θ α γ xp : ℝ) : ℝ := |α| * xp ^ (θ - 1) * (|θ| + |γ| + 2)

/-- The slope bound `2 |α| (x⁺)^{θ_k-1} (|θ_k| + |γ| + 2)` of the `k`-th oscillation of the
design `θ` (`θ_k = thK θ x⁺`; the factor `2` covers the switch-off of the design `θ = 0`). -/
noncomputable def oscLipK (θ α γ xp : ℝ) : ℝ := 2 * oscLip (thK θ xp) α γ xp

/-- The oscillation with only the terms `j < k`. -/
noncomputable def oscPart (θ : ℝ) (α γ xp : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range k, oscK θ (α j) (γ j) (xp j) x

/-- Its derivative, termwise. -/
noncomputable def oscDeriv (θ : ℝ) (α γ xp : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range k, deriv (oscK θ (α j) (γ j) (xp j)) x

/-- `|R_j'(x)| ≤ oscLip` for every `x > 0` (it is `0` below `x⁺_j`). -/
lemma abs_deriv_oscTerm_le_oscLip {θ α γ xp x : ℝ} (hθ : θ ≤ 1) (hxp : 0 < xp) (hx : 0 < x) :
    |deriv (oscTerm θ α γ xp) x| ≤ oscLip θ α γ xp := by
  have hL0 : 0 ≤ oscLip θ α γ xp := by
    unfold oscLip
    have := Real.rpow_nonneg hxp.le (θ - 1)
    positivity
  rcases lt_or_ge x xp with hlt | hle
  · have hev : oscTerm θ α γ xp =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hx hlt] with y hy
      exact oscTerm_eq_zero_of_le hy.1 hy.2.le
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact hL0
  · refine (abs_deriv_oscTerm_le hx hxp).trans ?_
    unfold oscLip
    have h1 : x ^ (θ - 1) ≤ xp ^ (θ - 1) := Real.rpow_le_rpow_of_nonpos hxp hle (by linarith)
    have h2 : 0 ≤ |θ| + |γ| + 2 := by positivity
    gcongr

/-- `|R_j'(x)| ≤ oscLipK` for every `x > 0` and every design. -/
lemma abs_deriv_oscK_le_oscLipK {θ α γ xp x : ℝ} (hθ : thK θ xp ≤ 1) (hxp : 0 < xp)
    (hx : 0 < x) : |deriv (oscK θ α γ xp) x| ≤ oscLipK θ α γ xp := by
  unfold oscLipK
  by_cases hθ0 : θ = 0
  · subst hθ0
    have hy : xp ≤ xp * max xp 1 := le_mul_of_one_le_right hxp.le (le_max_right _ _)
    have hy0 : 0 < xp * max xp 1 := lt_of_lt_of_le hxp hy
    rw [deriv_oscK_zero hxp hx]
    have h1 := abs_deriv_oscTerm_le_oscLip (α := α) (γ := γ) hθ hxp hx
    have h2 := abs_deriv_oscTerm_le_oscLip (α := α) (γ := γ) hθ hy0 hx
    have h3 : oscLip (thK 0 xp) α γ (xp * max xp 1) ≤ oscLip (thK 0 xp) α γ xp := by
      unfold oscLip
      have : (xp * max xp 1) ^ (thK 0 xp - 1) ≤ xp ^ (thK 0 xp - 1) :=
        Real.rpow_le_rpow_of_nonpos hxp hy (by linarith)
      have : 0 ≤ |thK 0 xp| + |γ| + 2 := by positivity
      gcongr
    calc _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add h1 (h2.trans h3)
      _ = _ := by ring
  · have e : oscK θ α γ xp = oscTerm θ α γ xp := by funext z; exact oscK_of_ne hθ0 _ _ _ _
    rw [e, thK_of_ne hθ0]
    rw [thK_of_ne hθ0] at hθ
    have := abs_deriv_oscTerm_le_oscLip (α := α) (γ := γ) hθ hxp hx
    have h0 : 0 ≤ oscLip θ α γ xp := by
      unfold oscLip
      have := Real.rpow_nonneg hxp.le (θ - 1)
      positivity
    linarith

/-- On `(0, x⁺_k]` the oscillation is `∑_{j<k} R_j`. -/
lemma osc_eq_oscPart {θ : ℝ} {α γ xp : ℕ → ℝ} (hsp : Spacing xp) {k : ℕ} {x : ℝ} (hx : 0 < x)
    (hxk : x ≤ xp k) : osc θ α γ xp x = oscPart θ α γ xp k x := by
  unfold osc oscPart
  apply tsum_eq_sum
  intro j hj
  rw [Finset.mem_range, not_lt] at hj
  exact oscK_eq_zero_of_le hx (hxk.trans (hsp.strictMono.monotone hj))

lemma measurable_oscDeriv (θ : ℝ) (α γ xp : ℕ → ℝ) (k : ℕ) :
    Measurable (oscDeriv θ α γ xp k) := by
  unfold oscDeriv
  exact Finset.measurable_sum _ fun j _ => measurable_deriv _

lemma abs_oscDeriv_le {θ : ℝ} {α γ xp : ℕ → ℝ} (hθ : ∀ j, thK θ (xp j) ≤ 1)
    (hxp : ∀ j, 0 < xp j) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |oscDeriv θ α γ xp k x| ≤ ∑ j ∈ range k, oscLipK θ (α j) (γ j) (xp j) := by
  unfold oscDeriv
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j _ => abs_deriv_oscK_le_oscLipK (hθ j) (hxp j) hx)

/-- **FTC for the oscillation**: `R(v) - R(u) = ∫_u^v R'` (`0 < u ≤ v`). -/
lemma oscPart_sub_eq_integral {θ : ℝ} {α γ xp : ℕ → ℝ} (hθ : ∀ j, thK θ (xp j) ≤ 1)
    (hxp : ∀ j, 0 < xp j) (k : ℕ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    oscPart θ α γ xp k v - oscPart θ α γ xp k u = ∫ t in u..v, oscDeriv θ α γ xp k t := by
  symm
  have hfun : oscPart θ α γ xp k = fun y => ∑ j ∈ range k, oscK θ (α j) (γ j) (xp j) y := rfl
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le huv] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
    rw [hfun]
    exact HasDerivAt.fun_sum fun j _ => hasDerivAt_oscK θ _ _ (hxp j) ht0
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    refine Measure.integrableOn_of_bounded
      (M := ∑ j ∈ range k, oscLipK θ (α j) (γ j) (xp j)) (by simp)
      (measurable_oscDeriv θ α γ xp k).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact abs_oscDeriv_le hθ hxp k (lt_trans hu ht.1)

/-- **The oscillation is Lipschitz** with constant `∑_{j<k} oscLipK`. -/
lemma abs_oscPart_sub_le {θ : ℝ} {α γ xp : ℕ → ℝ} (hθ : ∀ j, thK θ (xp j) ≤ 1)
    (hxp : ∀ j, 0 < xp j) (k : ℕ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    |oscPart θ α γ xp k v - oscPart θ α γ xp k u| ≤
      (∑ j ∈ range k, oscLipK θ (α j) (γ j) (xp j)) * (v - u) := by
  have hfun : oscPart θ α γ xp k = fun y => ∑ j ∈ range k, oscK θ (α j) (γ j) (xp j) y := rfl
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (oscPart θ α γ xp k) (oscDeriv θ α γ xp k t) t := by
    intro t ht
    rw [hfun]
    exact HasDerivAt.fun_sum fun j _ => hasDerivAt_oscK θ _ _ (hxp j) (mem_Ioi.mp ht)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := oscPart θ α γ xp k)
    (s := Ioi 0) (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => by
      rw [(hd t ht).deriv, Real.norm_eq_abs]
      exact abs_oscDeriv_le hθ hxp k (mem_Ioi.mp ht))
    (convex_Ioi 0) (mem_Ioi.mpr hu) (mem_Ioi.mpr (lt_of_lt_of_le hu huv))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at h
  exact h

/-- **The slopes of the designed oscillations sum to at most `1/100`**: for the switch-on points
`x⁺_j` of Section 2.2, `|α_j| ≤ 2` and `|γ_j| ≤ 2Γ_j = (x⁺_j)^{1-θ_j}/(X₀ log x⁺_j)`. -/
lemma sum_oscLip_switchOn_le {θ X₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hX0' : 0 ≤ X₀)
    (hX : 10 ^ 8 ≤ Real.log X₀) {α γ : ℕ → ℝ} (hα : ∀ j, |α j| ≤ 2)
    (hγ : ∀ j, |γ j| ≤ 2 * DesignedZero.heightScale (thK θ (switchOn (swS θ X₀) j))
      (kappa0Param X₀) (switchOn (swS θ X₀) j)) (k : ℕ) :
    ∑ j ∈ range k, oscLipK θ (α j) (γ j) (switchOn (swS θ X₀) j) ≤ 1 / 100 := by
  set x := switchOn (swS θ X₀) with hxdef
  have hX0 : 0 < X₀ := by
    rcases hX0'.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hXe : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos hX0
  have hX100 : 100 ≤ X₀ := by linarith
  have hX2 : (100 : ℝ) ≤ X₀ ^ 2 := by nlinarith
  -- `log x_j ≥ 100 · 2^j`
  have hlog : ∀ j, 100 * 2 ^ j ≤ Real.log (x j) := by
    intro j
    induction j with
    | zero =>
      rw [hxdef, log_switchOn_zero]
      have h1 := le_swS θ X₀
      have : X₀ ^ 2 ≤ swS θ X₀ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      simp only [pow_zero, mul_one]; linarith
    | succ j ih =>
      have e : Real.log (x (j + 1)) = x j := by
        rw [hxdef]; show Real.log (Real.exp (switchOn (swS θ X₀) j)) = _; rw [Real.log_exp]
      have hL0 : 0 ≤ Real.log (x j) := le_trans (by positivity) ih
      have hxj : x j = Real.exp (Real.log (x j)) := by
        rw [Real.exp_log (lt_of_lt_of_le one_pos ((switchOn_spacing _).one_le_all j))]
      have hq := Real.quadratic_le_exp_of_nonneg hL0
      rw [e, hxj, pow_succ]
      nlinarith
  have hterm : ∀ j, oscLipK θ (α j) (γ j) (x j) ≤ 1 / 10 ^ 3 * (1 / 2) ^ j := by
    intro j
    set t := thK θ (x j) with htdef
    set L := Real.log (x j) with hL
    have hx1 : 1 ≤ x j := (switchOn_spacing _).one_le_all j
    have hx0 : 0 < x j := by linarith
    have hLj := hlog j
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hL100 : 100 ≤ L := by nlinarith
    have hLpos : 0 < L := by linarith
    have ht2 : t ≤ 1 / 2 := (thK_swS_le θ (by linarith) (by linarith) j).trans
      (thU_le hθ (by norm_num))
    have ht0 : 0 ≤ t := by
      rw [htdef]; unfold thK; split_ifs
      · have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
        positivity
      · exact hθ0
    set r := x j ^ (t - 1) with hr
    have hr0 : 0 ≤ r := Real.rpow_nonneg hx0.le _
    -- `r ≤ 48 / L³`
    have hrle : r ≤ 48 / L ^ 3 := by
      have h1 : r ≤ x j ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have h2 : x j ^ (-(1 / 2) : ℝ) = (Real.exp (L / 2))⁻¹ := by
        rw [Real.rpow_def_of_pos hx0, ← Real.exp_neg]; congr 1; rw [hL]; ring
      have h3 := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 3
      norm_num [Nat.factorial] at h3
      have h4 : (Real.exp (L / 2))⁻¹ ≤ 48 / L ^ 3 := by
        rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
        nlinarith
      linarith
    -- `r |γ_j| ≤ κ₀ / L = 1 / (X₀ L)`
    have hrγ : r * |γ j| ≤ 1 / (X₀ * L) := by
      have hrx : r * x j ^ (1 - t) = 1 := by
        rw [hr, ← Real.rpow_add hx0]; norm_num
      have := mul_le_mul_of_nonneg_left (hγ j) hr0
      refine this.trans (le_of_eq ?_)
      unfold DesignedZero.heightScale kappa0Param
      rw [← hL, ← htdef]
      have : X₀ ≠ 0 := by linarith
      field_simp
      linear_combination hrx
    have hθa : |t| = t := abs_of_nonneg ht0
    have hlip : oscLip t (α j) (γ j) (x j) ≤ 2 * r * (t + 2) + 2 * (r * |γ j|) := by
      unfold oscLip
      rw [← hr, hθa]
      have : |α j| * r * (t + |γ j| + 2) ≤ 2 * r * (t + |γ j| + 2) := by
        have : 0 ≤ t + |γ j| + 2 := by positivity
        gcongr
        exact hα j
      linarith
    have hfin : 2 * r * (t + 2) + 2 * (r * |γ j|) ≤ 5 / 100 / L := by
      have hθ2 : t + 2 ≤ 5 / 2 := by linarith
      have h5 : 2 * r * (t + 2) ≤ 3 / 100 / L := by
        calc 2 * r * (t + 2) ≤ 2 * (48 / L ^ 3) * (5 / 2) := by gcongr
          _ = 240 / L ^ 3 := by ring
          _ ≤ 3 / 100 / L := by
            rw [div_le_div_iff₀ (by positivity) hLpos]; nlinarith [sq_nonneg L]
      have h6 : 2 * (r * |γ j|) ≤ 2 / 100 / L := by
        calc 2 * (r * |γ j|) ≤ 2 * (1 / (X₀ * L)) := by linarith
          _ ≤ 2 / 100 / L := by
            rw [show 2 * (1 / (X₀ * L)) = 2 / X₀ / L by field_simp]
            gcongr
      calc 2 * r * (t + 2) + 2 * (r * |γ j|) ≤ 3 / 100 / L + 2 / 100 / L := by linarith
        _ = 5 / 100 / L := by ring
    have hend : 2 * (5 / 100 / L) ≤ 1 / 10 ^ 3 * (1 / 2) ^ j := by
      rw [show 2 * (5 / 100 / L) = 1 / 10 / L by ring, div_le_iff₀ hLpos]
      have h42 : ((1 : ℝ) / 2) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
      have hp : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hLj hp]
    unfold oscLipK
    rw [← htdef]
    linarith
  calc ∑ j ∈ range k, oscLipK θ (α j) (γ j) (x j)
      ≤ ∑ j ∈ range k, 1 / 10 ^ 3 * (1 / 2 : ℝ) ^ j := sum_le_sum fun j _ => hterm j
    _ = 1 / 10 ^ 3 * ∑ j ∈ range k, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ 1 / 10 ^ 3 * 2 := by
        gcongr
        rw [geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        linarith
    _ ≤ 1 / 100 := by norm_num

end Zeros48

end
