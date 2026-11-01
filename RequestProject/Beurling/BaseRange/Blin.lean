module

public import RequestProject.Beurling.BaseRange.Window

/-!
# Lemma 7.1 (properties of the linear-window target)

For a measure `h` on `ℝ` and `w > 0` the paper writes (eq. (82), `eq:MA`)
`MA_w[h](x) = h([x, x + w])/w`, and `h_{(m)}(A) = h(A/m)` for the dilate of `h` by `m`.

* (1) `rhoDet_le_one_add` and `BModel.rhoDet_le` (file `Window.lean`, `Model/Slope.lean`);
* (2) `dilation_commutation` : `MA_{κx}[h_{(m)}](x) = m⁻¹ MA_{κq}[h](q)`, `q = x/m`, for every
  measure `h` and `m > 0` (the paper's `m ≥ 1`), because the window is linear;
* (3) `partial_count_le` : the `p` with `p² ∈ (x/m, (1+κ)x/m]` number at most
  `(κ/2)√(x/m) + 1`; `partial_sum_le` : summed over the cofactors with `q = x/(pm) ≥ X₀`,
  `∑ 1/m' ≤ ∑_{m ≤ x} 0.51κ/m ≤ 0.51κ(log x + 1)` (when `κX₀ ≥ 100`); and
  `partial_correction_le` : with component densities `≤ 1.01/Λ` the correction is at most
  `κ log x/Λ`;
* (5) `ramp_mass`, `ramp_mass_bounds` : the ramp of a rigid integer `d` under the linear
  normalisation has mass `∫_{d/(1+κ)}^d du/(κu) = log(1+κ)/κ ∈ [1 - κ/2, 1]`.

Item (4) (the offset `E₀` from the ramps truncated at `X₀`) and the drift of (5) are part of
the rigid target error, `Target.abs_rigidErr_le` (the target error (8), Lemma 3.4).
-/

@[expose] public section

open Real MeasureTheory Set Filter

namespace BaseRange

/-- `MA_w[h](x) = h([x, x + w])/w` (eq. (82)). -/
noncomputable def MA (h : Measure ℝ) (w x : ℝ) : ℝ := (h (Icc x (x + w))).toReal / w

/-- The dilate `h_{(m)}(A) = h(A/m)`, i.e. the image of `h` under `t ↦ m t`. -/
noncomputable def dilate (m : ℝ) (h : Measure ℝ) : Measure ℝ := h.map fun t => m * t

/-- **Lemma 7.1(2) (dilation commutation).** For every measure `h` on `ℝ` and `m > 0`,
`MA_{κx}[h_{(m)}](x) = m⁻¹ · MA_{κq}[h](q)` with `q = x/m`. -/
theorem dilation_commutation (h : Measure ℝ) {m κ x : ℝ} (hm : 0 < m) :
    MA (dilate m h) (κ * x) x = m⁻¹ * MA h (κ * (x / m)) (x / m) := by
  unfold MA dilate
  rw [Measure.map_apply (measurable_const_mul m) measurableSet_Icc]
  have hpre : (fun t => m * t) ⁻¹' Icc x (x + κ * x) = Icc (x / m) (x / m + κ * (x / m)) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    have e : x / m + κ * (x / m) = (x + κ * x) / m := by ring
    rw [e, div_le_iff₀ hm, le_div_iff₀ hm]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hpre]
  set A := (h (Icc (x / m) (x / m + κ * (x / m)))).toReal
  rcases eq_or_ne (κ * x) 0 with h0 | h0
  · have : κ * (x / m) = 0 := by rw [mul_div_assoc', h0, zero_div]
    rw [h0, this]; simp
  · have : κ * (x / m) = κ * x / m := by ring
    rw [this]
    field_simp

/-! ### Lemma 7.1(3): partial windows -/

lemma sqrt_one_add_le {κ : ℝ} (hκ : 0 ≤ κ) : Real.sqrt (1 + κ) ≤ 1 + κ / 2 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- The number of integers in `(a, b]` is at most `b - a + 1`. -/
lemma card_Ioc_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (((Finset.Icc 1 ⌊b⌋₊).filter fun p : ℕ => a < p ∧ (p : ℝ) ≤ b).card : ℝ) ≤ b - a + 1 := by
  have hsub : ((Finset.Icc 1 ⌊b⌋₊).filter fun p : ℕ => a < p ∧ (p : ℝ) ≤ b) ⊆
      Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_Ioc]
    refine ⟨?_, hp.1.2⟩
    exact (Nat.floor_lt ha).mpr hp.2.1
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at h1
  have h2 : ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) ≤ b - a + 1 := by
    have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
    rw [Nat.cast_sub hfl]
    have := Nat.floor_le (ha.trans hab)
    have := Nat.lt_floor_add_one a
    linarith
  exact (Nat.cast_le.mpr h1).trans h2

/-- **Lemma 7.1(3), the count**: the `p` with `√(x/m) < p ≤ √((1+κ)x/m)` number at most
`(κ/2)√(x/m) + 1`. -/
theorem partial_count_le {x m κ : ℝ} (hx : 0 ≤ x) (hm : 0 < m) (hκ : 0 ≤ κ) :
    (((Finset.Icc 1 ⌊Real.sqrt ((1 + κ) * x / m)⌋₊).filter fun p : ℕ =>
        Real.sqrt (x / m) < p ∧ (p : ℝ) ≤ Real.sqrt ((1 + κ) * x / m)).card : ℝ) ≤
      κ / 2 * Real.sqrt (x / m) + 1 := by
  have hxm : 0 ≤ x / m := div_nonneg hx hm.le
  have hs : Real.sqrt ((1 + κ) * x / m) = Real.sqrt (1 + κ) * Real.sqrt (x / m) := by
    rw [mul_div_assoc, Real.sqrt_mul (by linarith)]
  have hle : Real.sqrt (x / m) ≤ Real.sqrt ((1 + κ) * x / m) := by
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc]; nlinarith
  refine (card_Ioc_le (Real.sqrt_nonneg _) hle).trans ?_
  rw [hs]
  have := sqrt_one_add_le hκ
  have h0 := Real.sqrt_nonneg (x / m)
  nlinarith

/-- The partial-window cofactors `m' = pm` at `x` with `q = x/m' ≥ X₀`: the `p` with
`p² ∈ (x/m, (1+κ)x/m]` and `x/(pm) ≥ X₀`. -/
noncomputable def partialPs (X0 κ x : ℝ) (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.sqrt ((1 + κ) * x / m)⌋₊).filter fun p : ℕ =>
    Real.sqrt (x / m) < p ∧ (p : ℝ) ≤ Real.sqrt ((1 + κ) * x / m) ∧ X0 ≤ x / (p * m)

/-- One cofactor `m`: `∑_p 1/(pm) ≤ 0.51κ/m` if `κX₀ ≥ 100`. -/
lemma partial_sum_m_le {X0 κ x : ℝ} {m : ℕ} (hm : 1 ≤ m) (hκ : 0 < κ) (hX0 : 0 < X0)
    (hκX : 100 ≤ κ * X0) (hx : 0 ≤ x) :
    ∑ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m) ≤ 0.51 * κ / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set s := Real.sqrt (x / m)
  rcases (partialPs X0 κ x m).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]; positivity
  -- some `p` exists, so `√(x/m) > X₀`
  obtain ⟨p0, hp0⟩ := hne
  simp only [partialPs, Finset.mem_filter] at hp0
  have hp0pos : (0 : ℝ) < p0 := lt_of_le_of_lt (Real.sqrt_nonneg _) hp0.2.1
  have hs_pos : 0 < s := by
    by_contra h
    push_neg at h
    have hs0 : s = 0 := le_antisymm h (Real.sqrt_nonneg _)
    have hx0 : x / m ≤ 0 := by
      have := Real.sqrt_eq_zero'.mp hs0; linarith
    have : x / (p0 * m) ≤ 0 := by
      rw [div_mul_eq_div_div_swap]
      exact div_nonpos_of_nonpos_of_nonneg hx0 hp0pos.le
    linarith [hp0.2.2.2]
  have hsX : X0 < s := by
    have h1 : X0 * p0 ≤ x / m := by
      have := hp0.2.2.2
      rw [le_div_iff₀ (by positivity)] at this
      rw [le_div_iff₀ hm0]; nlinarith
    have h2 : s * s = x / m := Real.mul_self_sqrt (div_nonneg hx hm0.le)
    by_contra h
    push_neg at h
    have : s * s < X0 * p0 := by nlinarith [hp0.2.1]
    linarith
  -- each term is `≤ 1/(m s)`
  have hterm : ∀ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m) ≤ 1 / (s * m) := by
    intro p hp
    simp only [partialPs, Finset.mem_filter] at hp
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hp.2.1])
  have hcard : ((partialPs X0 κ x m).card : ℝ) ≤ κ / 2 * s + 1 := by
    refine le_trans ?_ (partial_count_le hx hm0 hκ.le)
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro p hp
    simp only [partialPs, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  calc ∑ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m)
      ≤ ∑ _p ∈ partialPs X0 κ x m, (1 : ℝ) / (s * m) := Finset.sum_le_sum hterm
    _ = (partialPs X0 κ x m).card * (1 / (s * m)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (κ / 2 * s + 1) * (1 / (s * m)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (κ / 2 + 1 / s) / m := by field_simp
    _ ≤ 0.51 * κ / m := by
        apply div_le_div_of_nonneg_right _ hm0.le
        have : 1 / s ≤ 1 / X0 := one_div_le_one_div_of_le hX0 hsX.le
        have : 1 / X0 ≤ κ / 100 := by
          rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith
        linarith

/-- **Lemma 7.1(3), the sum**: `∑_{m ≤ x} ∑_p 1/(pm) ≤ 0.51κ(log x + 1)` over the partial-window
cofactors `m' = pm` with `x/m' ≥ X₀`, when `κX₀ ≥ 100`. -/
theorem partial_sum_le {X0 κ x : ℝ} (hκ : 0 < κ) (hX0 : 0 < X0) (hκX : 100 ≤ κ * X0)
    (hx : 1 ≤ x) :
    ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m) ≤
      0.51 * κ * (Real.log x + 1) := by
  calc ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, 0.51 * κ / (m : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        exact partial_sum_m_le (Finset.mem_Icc.mp hm).1 hκ hX0 hκX (by linarith)
    _ = 0.51 * κ * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / m := by
        rw [Finset.mul_sum]; congr 1; ext m; ring
    _ ≤ 0.51 * κ * (Real.log x + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / m = (harmonic ⌊x⌋₊ : ℝ) := by
          rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
        rw [h1]
        have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
        have h2 := harmonic_le_one_add_log ⌊x⌋₊
        have h3 : Real.log ⌊x⌋₊ ≤ Real.log x :=
          Real.log_le_log (by exact_mod_cast hfl) (Nat.floor_le (by linarith))
        linarith

/-- **Lemma 7.1(3), the correction**: with component densities `0 ≤ d ≤ 1.01/Λ`, the
partial windows contribute at most `κ log x/Λ` (for `log x ≥ 2`). -/
theorem partial_correction_le {X0 κ x Λ : ℝ} (hκ : 0 < κ) (hX0 : 0 < X0) (hκX : 100 ≤ κ * X0)
    (hx1 : 1 ≤ x) (hx : 2 ≤ Real.log x) (hΛ : 0 < Λ) (d : ℕ → ℕ → ℝ)
    (hd : ∀ m p, 0 ≤ d m p ∧ d m p ≤ 1.01 / Λ) :
    ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, d m p / (p * m) ≤
      κ * Real.log x / Λ := by
  have h1 := partial_sum_le hκ hX0 hκX hx1
  calc ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, d m p / (p * m)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, 1.01 / Λ * (1 / (p * m)) := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun p hp => ?_
        rw [div_eq_mul_one_div]
        have : (0 : ℝ) ≤ 1 / (p * m) := by positivity
        exact mul_le_mul_of_nonneg_right (hd m p).2 this
    _ = 1.01 / Λ * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ partialPs X0 κ x m, (1 : ℝ) / (p * m) := by
        rw [Finset.mul_sum]; congr 1; ext m; rw [Finset.mul_sum]
    _ ≤ 1.01 / Λ * (0.51 * κ * (Real.log x + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ κ * Real.log x / Λ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hΛ]
        nlinarith

/-! ### Lemma 7.1(5): the ramp mass -/

/-- The ramp of a rigid integer `d > 0` has mass `∫_{d/(1+κ)}^d du/(κu) = log(1+κ)/κ`. -/
theorem ramp_mass {κ d : ℝ} (hκ : 0 < κ) (hd : 0 < d) :
    ∫ u in d / (1 + κ)..d, 1 / (κ * u) = Real.log (1 + κ) / κ := by
  have hκ1 : 0 < 1 + κ := by linarith
  have ha : 0 < d / (1 + κ) := div_pos hd hκ1
  have e : (fun u : ℝ => 1 / (κ * u)) = fun u => κ⁻¹ * u⁻¹ := by
    ext u; rw [one_div, mul_inv]
  rw [e, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hd]
  have : d / (d / (1 + κ)) = 1 + κ := by field_simp
  rw [this]
  ring

/-- `1 - κ/2 ≤ log(1+κ)/κ ≤ 1` for `κ > 0`: the ramp mass is `1 - κ/2 + O(κ²)`. -/
theorem ramp_mass_bounds {κ : ℝ} (hκ : 0 < κ) :
    1 - κ / 2 ≤ Real.log (1 + κ) / κ ∧ Real.log (1 + κ) / κ ≤ 1 := by
  constructor
  · rw [le_div_iff₀ hκ]
    have h := Real.le_log_one_add_of_nonneg hκ.le
    have : (1 - κ / 2) * κ ≤ 2 * κ / (κ + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg κ, mul_pos hκ (mul_pos hκ hκ)]
    linarith
  · rw [div_le_iff₀ hκ, one_mul]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + κ)
    linarith

end BaseRange
