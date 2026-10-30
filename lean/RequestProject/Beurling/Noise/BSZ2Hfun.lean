module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# The function `h(w) = (1+w)⁴ log(2+w)/w` (Theorem 5.6, Step 7(iii))

With `m = ℓw/(1+w)`, `A(m, w) = (B/ℓ) h(w)`. The majorants of Step 7(iii) use

* the slope bound `h'(w) ≤ 8 (1+w)² log(2+w)` for `w ≥ 1` (Part II, via the mean value theorem):
  `h_sub_le`;
* the lower bound `h'(x) ≥ u³(3u-4) log(1+u)/(u-1)²` for `x ≥ u - 1 ≥ 1` (Part I, the
  coefficient of `α`): `h_sub_ge`. This uses that `(1+x)³(3x-1)/x² = (1+x)(x+2+1/x)(3-1/x)`
  is non-decreasing on `[1, ∞)`.

Also: the elementary difference bounds for `p(x) = (x - c)₊²` (`sq_pos_part_sub`).
-/

@[expose] public section

open Real Set

namespace BSaias

/-- `h(w) = (1+w)⁴ log(2+w)/w`. -/
noncomputable def hfun (w : ℝ) : ℝ := (1 + w) ^ 4 * Real.log (2 + w) / w

/-- `h'(w)`. -/
noncomputable def hder (w : ℝ) : ℝ :=
  (4 * (1 + w) ^ 3 * Real.log (2 + w) + (1 + w) ^ 4 / (2 + w)) / w
    - (1 + w) ^ 4 * Real.log (2 + w) / w ^ 2

lemma hasDerivAt_hfun {w : ℝ} (hw : 0 < w) : HasDerivAt hfun (hder w) w := by
  have h2 : (2 + w) ≠ 0 := by positivity
  have hl : HasDerivAt (fun w => Real.log (2 + w)) (1 / (2 + w)) w := by
    have := ((hasDerivAt_id w).const_add 2).log h2
    simpa using this
  have hp : HasDerivAt (fun w => (1 + w) ^ 4) (4 * (1 + w) ^ 3) w := by
    have := ((hasDerivAt_id' w).const_add 1).pow 4
    simpa [Pi.pow_def] using this
  have := (hp.mul hl).div (hasDerivAt_id w) hw.ne'
  unfold hfun hder
  convert! this using 1
  simp only [id, Pi.mul_apply]
  field_simp

lemma hder_le {x : ℝ} (hx : 1 ≤ x) : hder x ≤ 8 * (1 + x) ^ 2 * Real.log (2 + x) := by
  have hL : 1 < Real.log (2 + x) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hx0 : 0 < x := by linarith
  unfold hder
  have h1 : (1 + x) ^ 4 / (2 + x) / x ≤ (1 + x) ^ 4 * Real.log (2 + x) / x ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : x ^ 2 ≤ (2 + x) * x * Real.log (2 + x) := by nlinarith
    have hp : 0 ≤ (1 + x) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  have h2 : 4 * (1 + x) ^ 3 * Real.log (2 + x) / x ≤ 8 * (1 + x) ^ 2 * Real.log (2 + x) := by
    rw [div_le_iff₀ hx0]
    have hp : 0 ≤ (1 + x) ^ 2 * Real.log (2 + x) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 4 * (1 + x) ≤ 8 * x) hp]
  rw [add_div]
  linarith

lemma hder_ge {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ 3 * (3 * x - 1) * Real.log (2 + x) / x ^ 2 ≤ hder x := by
  have hx0 : 0 < x := by linarith
  unfold hder
  have h1 : 0 ≤ (1 + x) ^ 4 / (2 + x) / x := by positivity
  have e : (1 + x) ^ 3 * (3 * x - 1) * Real.log (2 + x) / x ^ 2 =
      4 * (1 + x) ^ 3 * Real.log (2 + x) / x - (1 + x) ^ 4 * Real.log (2 + x) / x ^ 2 := by
    field_simp; ring
  rw [e, add_div]
  linarith

/-- `k(x) = (1+x)³(3x-1)/x²` is non-decreasing on `[1, ∞)`. -/
lemma kfun_mono {y x : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    (1 + y) ^ 3 * (3 * y - 1) / y ^ 2 ≤ (1 + x) ^ 3 * (3 * x - 1) / x ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have ek : ∀ t : ℝ, 0 < t → (1 + t) ^ 3 * (3 * t - 1) / t ^ 2 =
      (1 + t) * (t + 2 + 1 / t) * (3 - 1 / t) := by
    intro t ht; field_simp; ring
  rw [ek y hy0, ek x hx0]
  have h1 : y + 2 + 1 / y ≤ x + 2 + 1 / x := by
    have : 1 / y + y ≤ 1 / x + x := by
      rw [div_add' _ _ _ hy0.ne', div_add' _ _ _ hx0.ne', div_le_div_iff₀ hy0 hx0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyx)
        (sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hy (hy.trans hyx)))]
    linarith
  have h2 : 3 - 1 / y ≤ 3 - 1 / x := by
    have := one_div_le_one_div_of_le hy0 hyx; linarith
  have h3 : 0 ≤ 3 - 1 / y := by
    have : 1 / y ≤ 1 := by rw [div_le_one hy0]; exact hy
    linarith
  have h4 : 0 ≤ y + 2 + 1 / y := by positivity
  have h5 : 0 ≤ 1 + y := by linarith
  calc (1 + y) * (y + 2 + 1 / y) * (3 - 1 / y)
      ≤ (1 + x) * (x + 2 + 1 / x) * (3 - 1 / x) := by
        apply mul_le_mul _ h2 h3 (by positivity)
        exact mul_le_mul (by linarith) h1 h4 (by linarith)

lemma hfun_continuousOn {a b : ℝ} (ha : 0 < a) : ContinuousOn hfun (Icc a b) := fun _ hx =>
  (hasDerivAt_hfun (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt

lemma hfun_diffOn {a b : ℝ} (ha : 0 < a) : DifferentiableOn ℝ hfun (interior (Icc a b)) := by
  intro x hx
  rw [interior_Icc] at hx
  exact (hasDerivAt_hfun (lt_trans ha hx.1)).differentiableAt.differentiableWithinAt

/-- Part II: `h(w) - h(u) ≤ 8(1+w)² log(2+w) (w - u)` for `1 ≤ u ≤ w`. -/
lemma h_sub_le {u w : ℝ} (hu : 1 ≤ u) (huw : u ≤ w) :
    hfun w - hfun u ≤ 8 * (1 + w) ^ 2 * Real.log (2 + w) * (w - u) := by
  refine (convex_Icc u w).image_sub_le_mul_sub_of_deriv_le (hfun_continuousOn (by linarith))
    (hfun_diffOn (by linarith)) ?_ u ⟨le_rfl, huw⟩ w ⟨huw, le_rfl⟩ huw
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_hfun (by linarith [hx.1])).deriv]
  refine (hder_le (by linarith [hx.1])).trans ?_
  have h2 : Real.log (2 + x) ≤ Real.log (2 + w) :=
    Real.log_le_log (by linarith [hx.1]) (by linarith [hx.2])
  have h3 : (1 + x) ^ 2 ≤ (1 + w) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2])
  have h4 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith [hx.1])
  nlinarith [mul_le_mul h3 h2 h4 (by positivity)]

/-- Part I: `h(u) - h(w) ≥ u³(3u-4) log(1+u)/(u-1)² · (u - w)` for `u - 1 ≤ w ≤ u`, `u ≥ 2`. -/
lemma h_sub_ge {u w : ℝ} (hu : 2 ≤ u) (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 * (u - w) ≤ hfun u - hfun w := by
  refine (convex_Icc w u).mul_sub_le_image_sub_of_le_deriv (hfun_continuousOn (by linarith))
    (hfun_diffOn (by linarith)) ?_ w ⟨le_rfl, hwu⟩ u ⟨hwu, le_rfl⟩ hwu
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_hfun (by linarith [hx.1])).deriv]
  refine le_trans ?_ (hder_ge (by linarith [hx.1]))
  have hk := kfun_mono (y := u - 1) (x := x) (by linarith) (by linarith [hx.1])
  have e1 : (1 + (u - 1)) = u := by ring
  have e2 : (3 * (u - 1) - 1) = 3 * u - 4 := by ring
  rw [e1, e2] at hk
  have hL : Real.log (1 + u) ≤ Real.log (2 + x) :=
    Real.log_le_log (by linarith) (by linarith [hx.1])
  have hL0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hk0 : 0 ≤ u ^ 3 * (3 * u - 4) / (u - 1) ^ 2 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity) (by linarith)
  have e3 : u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 =
      u ^ 3 * (3 * u - 4) / (u - 1) ^ 2 * Real.log (1 + u) := by ring
  have e4 : (1 + x) ^ 3 * (3 * x - 1) * Real.log (2 + x) / x ^ 2 =
      (1 + x) ^ 3 * (3 * x - 1) / x ^ 2 * Real.log (2 + x) := by ring
  rw [e3, e4]
  exact mul_le_mul hk hL hL0 (le_trans hk0 hk)

/-- Difference bounds for `(x - c)₊²`: for `x ≤ y`,
`2 (x - c)₊ (y - x) ≤ (y - c)₊² - (x - c)₊² ≤ 2 (y - c)₊ (y - x)`. -/
lemma sq_pos_part_sub (c x y : ℝ) (h : x ≤ y) :
    (max (y - c) 0) ^ 2 - (max (x - c) 0) ^ 2 ≤ 2 * max (y - c) 0 * (y - x) ∧
    2 * max (x - c) 0 * (y - x) ≤ (max (y - c) 0) ^ 2 - (max (x - c) 0) ^ 2 := by
  rcases le_total (y - c) 0 with h1 | h1 <;> rcases le_total (x - c) 0 with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]; constructor <;> nlinarith
  · rw [max_eq_right h1, max_eq_left h2]; constructor <;> nlinarith
  · rw [max_eq_left h1, max_eq_right h2]; constructor <;> nlinarith
  · rw [max_eq_left h1, max_eq_left h2]; constructor <;> nlinarith

end BSaias

end
