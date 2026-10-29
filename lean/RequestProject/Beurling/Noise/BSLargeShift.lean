module

public import RequestProject.Beurling.Noise.BSLargeDefs

/-!
# The shift `σ_sh = a(m, w) - φ(w)` ((P2) in the proof of Lemma 5.7)

With `m = ℓw/(1+w)`, `x = 1/(1+w)` and `m^{1/4} = u₀(1-x)^{1/4}`:

* `u0_mOf_ge_third`: `m^{1/4} ≥ u₀(1 - x/3)` for `w ≥ 1` (concavity, `x ≤ 1/2`);
* `u0_mOf_ge_fine`: `m^{1/4} ≥ u₀(1 - 0.2501x)` for `w ≥ 999`;
* `aQ_mOf_eq_zero_low`: `a(m, w) = 0` for `1 ≤ w ≤ u₀ - 3`, and `aQ_mOf_eq_zero_mid`: also for
  `u₀ - 3 ≤ w ≤ u₀ - 0.26` (`u₀ ≥ 31622`);
* `aQ_mOf_le`: for `w ≥ u₀ - 3`, `a(m,w) ≤ (w-u₀)₊²/(2√ℓ) + 0.2502 (w-u₀)₊/√ℓ + 0.0314/√ℓ`
  (the paper's `σ_sh ≤ 0.2503 (w-u₀)₊/√ℓ + 0.0314/√ℓ`, lines 394-408).
-/

@[expose] public section

open Real

namespace BSaias.Large

lemma mOf_eq {ℓ w : ℝ} (hw : 0 ≤ w) : mOf ℓ w = ℓ * (1 - 1 / (1 + w)) := by
  unfold mOf; field_simp; ring

/-- `c u₀(ℓ) ≤ u₀(m)` when `0 ≤ c` and `c⁴ ≤ 1 - 1/(1+w)`. -/
lemma u0_mOf_ge {ℓ w c : ℝ} (hℓ : 0 < ℓ) (hw : 0 ≤ w) (hc0 : 0 ≤ c)
    (hc : c ^ 4 ≤ 1 - 1 / (1 + w)) : c * u0 ℓ ≤ u0 (mOf ℓ w) := by
  show c * √(√ℓ) ≤ √(√(mOf ℓ w))
  have hs : 0 ≤ √(√ℓ) := Real.sqrt_nonneg _
  rw [Real.le_sqrt (by positivity) (Real.sqrt_nonneg _), Real.le_sqrt (by positivity)
    (by unfold mOf; positivity)]
  have e : ((c * √(√ℓ)) ^ 2) ^ 2 = c ^ 4 * ℓ := by
    have h1 : √(√ℓ) ^ 2 = √ℓ := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : √ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
    calc ((c * √(√ℓ)) ^ 2) ^ 2 = c ^ 4 * (√(√ℓ) ^ 2) ^ 2 := by ring
      _ = c ^ 4 * ℓ := by rw [h1, h2]
  rw [e, mOf_eq hw]
  nlinarith

lemma u0_mOf_le {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 ≤ w) : u0 (mOf ℓ w) ≤ u0 ℓ := by
  show √(√(mOf ℓ w)) ≤ √(√ℓ)
  apply Real.sqrt_le_sqrt; apply Real.sqrt_le_sqrt
  rw [mOf_eq hw]
  have : 0 ≤ 1 / (1 + w) := by positivity
  nlinarith

lemma u0_mOf_ge_third {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 1 ≤ w) :
    u0 ℓ - u0 ℓ / (3 * (1 + w)) ≤ u0 (mOf ℓ w) := by
  set x := 1 / (1 + w) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h := u0_mOf_ge (w := w) (c := 1 - x / 3) hℓ (by linarith) (by linarith) (by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg (mul_nonneg hx0 hx0) hx0,
      mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg hx0 hx0)])
  have e : (1 - x / 3) * u0 ℓ = u0 ℓ - u0 ℓ / (3 * (1 + w)) := by
    rw [hx]; field_simp
  linarith

lemma u0_mOf_ge_fine {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 999 ≤ w) :
    u0 ℓ - 0.2501 * u0 ℓ / (1 + w) ≤ u0 (mOf ℓ w) := by
  set x := 1 / (1 + w) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 1000 := by
    rw [hx, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h := u0_mOf_ge (w := w) (c := 1 - 0.2501 * x) hℓ (by linarith) (by linarith) (by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg (mul_nonneg hx0 hx0) hx0,
      mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg hx0 hx0),
      mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.mpr hx1)])
  have e : (1 - 0.2501 * x) * u0 ℓ = u0 ℓ - 0.2501 * u0 ℓ / (1 + w) := by
    rw [hx]; field_simp
  linarith

lemma aQ_eq_zero {m w : ℝ} (h : w ≤ u0 m) : aQ m w = 0 := by
  unfold aQ; rw [max_eq_right (by linarith)]; simp

/-- `a(m, w) = 0` for `1 ≤ w ≤ u₀ - 3` (paper, line 391-393). -/
lemma aQ_mOf_eq_zero_low {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 1 ≤ w) (hw3 : w ≤ u0 ℓ - 3) :
    aQ (mOf ℓ w) w = 0 := by
  apply aQ_eq_zero
  refine le_trans ?_ (u0_mOf_ge_third hℓ hw)
  -- `w + u₀/(3(1+w)) ≤ u₀`, a convex function of `w` checked at both ends
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ w - 1) (by linarith : (0 : ℝ) ≤ u0 ℓ - 3 - w)]

lemma u0_ge_of {ℓ : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) : 31622 ≤ u0 ℓ := by
  show 31622 ≤ √(√ℓ)
  have h1 : 1000000000 ≤ √ℓ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

/-- For `w ≥ u₀ - 3`, `u₀ - m^{1/4} ≤ 0.2501 u₀/(1+w) ≤ 0.25013`. -/
lemma shift_le {ℓ w : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) (hw : u0 ℓ - 3 ≤ w) :
    u0 ℓ - u0 (mOf ℓ w) ≤ 0.2501 * u0 ℓ / (1 + w) ∧ 0.2501 * u0 ℓ / (1 + w) ≤ 0.25013 := by
  have hu := u0_ge_of hℓ
  have hℓ0 : 0 < ℓ := by linarith
  refine ⟨by linarith [u0_mOf_ge_fine hℓ0 (w := w) (by linarith)], ?_⟩
  rw [div_le_iff₀ (by linarith)]; nlinarith

/-- `a(m, w) = 0` for `u₀ - 3 ≤ w ≤ u₀ - 0.26`. -/
lemma aQ_mOf_eq_zero_mid {ℓ w : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) (hw : u0 ℓ - 3 ≤ w)
    (hw2 : w ≤ u0 ℓ - 0.26) : aQ (mOf ℓ w) w = 0 := by
  apply aQ_eq_zero
  obtain ⟨h1, h2⟩ := shift_le hℓ hw
  linarith

/-- `1/√m ≤ (1 + 1/(2w))/√ℓ`. -/
lemma inv_sqrt_mOf_le {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    1 / √(mOf ℓ w) ≤ (1 + 1 / (2 * w)) / √ℓ := by
  have hm : 0 < mOf ℓ w := by unfold mOf; positivity
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_pos.mpr hℓ), one_mul]
  have hk : 0 ≤ 1 + 1 / (2 * w) := by positivity
  rw [← Real.sqrt_sq hk, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  unfold mOf
  have e : (1 + 1 / (2 * w)) ^ 2 * (ℓ * w / (1 + w)) =
      ℓ * ((1 + 1 / (2 * w)) ^ 2 * w / (1 + w)) := by
    ring
  rw [e]
  have : 1 ≤ (1 + 1 / (2 * w)) ^ 2 * w / (1 + w) := by
    rw [le_div_iff₀ (by linarith)]
    have : (1 + 1 / (2 * w)) ^ 2 * w = w + 1 + 1 / (4 * w) := by field_simp; ring
    rw [this]; have : 0 < 1 / (4 * w) := by positivity
    linarith
  nlinarith

/-- **(P2), the shift**: for `w ≥ u₀ - 3`,
`a(m, w) ≤ (w-u₀)₊²/(2√ℓ) + 0.2502 (w-u₀)₊/√ℓ + 0.0314/√ℓ`. -/
lemma aQ_mOf_le {ℓ w : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) (hw : u0 ℓ - 3 ≤ w) :
    aQ (mOf ℓ w) w ≤ (max (w - u0 ℓ) 0) ^ 2 / (2 * √ℓ) + 0.2502 * max (w - u0 ℓ) 0 / √ℓ
      + 0.0314 / √ℓ := by
  have hu := u0_ge_of hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hw0 : 0 < w := by linarith
  have hsℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  obtain ⟨hc1, hc2⟩ := shift_le hℓ hw
  set c := u0 ℓ - u0 (mOf ℓ w) with hc
  have hc0 : 0 ≤ c := by have := u0_mOf_le hℓ0 hw0.le; linarith
  set A := max (w - u0 ℓ) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  -- `(w - m^{1/4})₊ ≤ A + c`
  have hD : max (w - u0 (mOf ℓ w)) 0 ≤ A + c := by
    apply max_le _ (by linarith)
    have := le_max_left (w - u0 ℓ) 0
    linarith
  have hD0 : 0 ≤ max (w - u0 (mOf ℓ w)) 0 := le_max_right _ _
  have hinv := inv_sqrt_mOf_le hℓ0 hw0
  have hm : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr (by unfold mOf; positivity)
  have step1 : aQ (mOf ℓ w) w ≤ (A + c) ^ 2 * (1 + 1 / (2 * w)) / (2 * √ℓ) := by
    unfold aQ
    calc (max (w - u0 (mOf ℓ w)) 0) ^ 2 / (2 * √(mOf ℓ w))
        = (max (w - u0 (mOf ℓ w)) 0) ^ 2 / 2 * (1 / √(mOf ℓ w)) := by field_simp
      _ ≤ (A + c) ^ 2 / 2 * ((1 + 1 / (2 * w)) / √ℓ) :=
          mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hD0 hD 2) (by norm_num))
            hinv (by positivity) (by positivity)
      _ = (A + c) ^ 2 * (1 + 1 / (2 * w)) / (2 * √ℓ) := by field_simp
  -- the polynomial inequality `(A+c)²(1 + 1/(2w)) ≤ A² + 0.5004 A + 0.0628`
  have key : (A + c) ^ 2 * (1 + 1 / (2 * w)) ≤ A ^ 2 + 0.5004 * A + 0.0628 := by
    clear_value c A
    clear hc hD hinv step1 hm
    have e : (A + c) ^ 2 * (1 + 1 / (2 * w)) = ((A + c) ^ 2 * (2 * w + 1)) / (2 * w) := by
      field_simp
    rw [e, div_le_iff₀ (by linarith)]
    have hcw : c * (1 + w) ≤ 0.2501 * u0 ℓ := by
      have := hc1; rw [le_div_iff₀ (by linarith)] at this; linarith
    rcases le_or_gt w (u0 ℓ) with hwu | hwu
    · have hA' : A = 0 := by rw [hA]; exact max_eq_right (by linarith)
      rw [hA']
      have : c ^ 2 ≤ 0.0626 := by nlinarith
      nlinarith
    · have hA' : A = w - u0 ℓ := by rw [hA]; exact max_eq_left (by linarith)
      -- `4wAc + A² ≤ 1.0004 A w`, `2Ac ≤ 0.0004 A w`, `(2w+1)c² ≤ 0.1256 w`
      have h1 : 4 * w * A * c ≤ 1.0004 * A * u0 ℓ := by
        have : w * c ≤ 0.2501 * u0 ℓ := by nlinarith
        nlinarith
      have h2 : A ^ 2 = A * w - A * u0 ℓ := by rw [hA']; ring
      have h3 : 2 * A * c ≤ 0.0004 * A * w := by nlinarith
      have h4 : (2 * w + 1) * c ^ 2 ≤ 0.1256 * w := by
        have hc2 : c ^ 2 ≤ 0.0626 := by nlinarith
        have := mul_le_mul_of_nonneg_left hc2 (by linarith : (0 : ℝ) ≤ 2 * w + 1)
        linarith
      have h5 : 0.0004 * A * u0 ℓ ≤ 0.0004 * A * w := by
        have := mul_le_mul_of_nonneg_left hwu.le hA0
        linarith
      have ex1 : (A + c) ^ 2 * (2 * w + 1) =
          2 * w * A ^ 2 + A ^ 2 + 4 * w * A * c + 2 * A * c + (2 * w + 1) * c ^ 2 := by ring
      have ex2 : (A ^ 2 + 0.5004 * A + 0.0628) * (2 * w) =
          2 * w * A ^ 2 + 1.0008 * (A * w) + 0.1256 * w := by ring
      rw [ex1, ex2]
      have h2' : A ^ 2 = A * w - A * u0 ℓ := h2
      linarith
  calc aQ (mOf ℓ w) w ≤ (A + c) ^ 2 * (1 + 1 / (2 * w)) / (2 * √ℓ) := step1
    _ ≤ (A ^ 2 + 0.5004 * A + 0.0628) / (2 * √ℓ) := div_le_div_of_nonneg_right key (by positivity)
    _ = A ^ 2 / (2 * √ℓ) + 0.2502 * A / √ℓ + 0.0314 / √ℓ := by field_simp; ring

end BSaias.Large

end
