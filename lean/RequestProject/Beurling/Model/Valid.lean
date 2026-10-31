module

public import RequestProject.Beurling.Model.Phi
public import RequestProject.Beurling.Model.Slope

/-!
# The target of any prime data is a valid slot-model target (Lemma 3.3)

For the target (6) of arbitrary prime data `D` (`targetD`), with the designed heights:

* `targetD_split` : `T = X₀ + J + C` on `[X₀, ∞)`, with the jump part `J` (rigid integers and
  `A`, right-continuous step function) and the continuous part `C`;
* `contD_lower`, `contD_upper` : `0.08 (x' - x)/log x' ≤ C(x') - C(x) ≤ 1.01 (x' - x)`
  (Lemma 3.3; the lower bound uses (84), `ShortIntervalPNTFrom X₀`);
* `validHyp_of_HB` : `T` is non-decreasing, right-continuous, unbounded, `T(X₀) ≥ X₀`
  (§3.4: the slots `s_j = min{x : T(x) ≥ j + ϑ_s}` exist for every `ω`);
* `slopeHyp_of_HB` : `T(x') - T(x) ≥ 0.08 (x' - x)/log x'`;
* `targetD_ge_linear` : `T(x) ≥ 0.7 x - X₀ - 1`.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono Filter Topology

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The continuous part of the target of the data. -/
noncomputable def contD (θ : ℝ) (X₀ : ℕ) (D : PrimeData) : ℝ → ℝ :=
  contPart X₀ (kappaParam X₀) (absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ))
    (osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀))

/-- The jump part of the target of the data. -/
noncomputable def jumpD (X₀ : ℕ) (D : PrimeData) : ℝ → ℝ := jumpPart X₀ (countA (absSet X₀ D))

lemma targetD_split (θ : ℝ) (D : PrimeData) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    targetD θ X₀ D x = X₀ + jumpD X₀ D x + contD θ X₀ D x :=
  target_eq_split hx

lemma gammaD_range (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) :
    DesignedRange θ X₀ (gammaD θ X₀ D) := by
  have hX1 : (1 : ℝ) ≤ X₀ := (one_lt_of_logX (Nat.cast_nonneg _) hX).le
  exact designedGammaN_mem _ θ X₀ _ _ _ _ _ _ fun k => (heightScale_switchOn_pos θ hX1 k).le

/-- The designed amplitudes satisfy `1 ≤ α_k ≤ 2`. -/
lemma alphaD_mem (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) (k : ℕ) :
    alphaD θ X₀ D k ∈ Icc (1 : ℝ) 2 := by
  have hX1 : (1 : ℝ) ≤ X₀ := (one_lt_of_logX (Nat.cast_nonneg _) hX).le
  have hm := gammaD_range (θ := θ) hX D k
  set γ := gammaD θ X₀ D k
  set Γ := heightScale θ (kappa0Param X₀) (switchOn X₀ k) with hΓdef
  have hΓk : 0 < Γ := heightScale_switchOn_pos θ hX1 k
  have hγ : 0 < γ := lt_of_lt_of_le hΓk hm.1
  have hL : Real.log (switchOn X₀ k) ≠ 0 := by
    intro h0
    have : Γ = 0 := by rw [hΓdef]; unfold heightScale; rw [h0]; simp
    linarith
  have e : alphaD θ X₀ D k = 2 * Γ / γ := by
    show (kappa0Param X₀) * switchOn X₀ k ^ (1 - θ) / Real.log (switchOn X₀ k) / γ = 2 * Γ / γ
    rw [hΓdef]; unfold heightScale
    congr 1
    field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ hγ]; linarith [hm.2]
  · rw [div_le_iff₀ hγ]; nlinarith [hm.1]

lemma abs_alphaD_le (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) (k : ℕ) :
    |alphaD θ X₀ D k| ≤ 2 := by
  have h := alphaD_mem (θ := θ) hX D k
  rw [abs_of_nonneg (by linarith [h.1])]; exact h.2

lemma contD_lower (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (D : PrimeData) (hD : LocFinD D) {x x' : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    0.08 * (x' - x) / Real.log x' ≤ contD θ X₀ D x' - contD θ X₀ D x :=
  contPart_lower hθ hX (gammaD_range hX D) (absSet X₀ D) (absSet_locFin hD) hHB hx hxx

lemma contD_upper (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (D : PrimeData) (hD : LocFinD D) {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    contD θ X₀ D x' - contD θ X₀ D x ≤ 1.01 * (x' - x) :=
  contPart_upper hθ hX (gammaD_range hX D) (absSet X₀ D) (absSet_locFin hD) hx hxx

lemma contD_continuousOn (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) (hD : LocFinD D) :
    ContinuousOn (contD θ X₀ D) (Ici (X₀ : ℝ)) :=
  contPart_continuousOn hθ hX (gammaD θ X₀ D) (absSet X₀ D) (absSet_locFin hD)

lemma contD_at (θ : ℝ) (D : PrimeData) : contD θ X₀ D X₀ = 0 := by
  unfold contD contPart; simp

/-! ### The jump part -/

lemma jumpD_mono (D : PrimeData) (hD : LocFinD D) {x y : ℝ} (hxy : x ≤ y) :
    jumpD X₀ D x ≤ jumpD X₀ D y := by
  unfold jumpD jumpPart
  have h1 : (Rankin.smoothCount X₀ x : ℝ) ≤ Rankin.smoothCount X₀ y := by
    exact_mod_cast smoothCount_mono X₀ hxy
  have h2 := countA_mono (absSet_locFin (X₀ := X₀) hD) hxy
  linarith

lemma jumpD_nonneg (D : PrimeData) (hD : LocFinD D) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    0 ≤ jumpD X₀ D x := by
  have h := jumpD_mono (X₀ := X₀) D hD hx
  have h0 : 0 ≤ jumpD X₀ D X₀ := by
    unfold jumpD jumpPart; simp only [sub_self, zero_add]; exact countA_nonneg _ _
  linarith

/-- **The jump part is right-continuous**: it is constant on `[x, x + δ)` for some `δ > 0` (the
rigid integers and the locally finite `A` have no point in `(x, x + δ)`). -/
lemma jumpD_rconst (D : PrimeData) (hD : LocFinD D) {x : ℝ} (hx : 0 ≤ x) :
    ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → jumpD X₀ D y = jumpD X₀ D x := by
  obtain ⟨δ, hδ, hc⟩ := countA_rconst (absSet_locFin (X₀ := X₀) hD) x
  have hfl : 0 < (⌊x⌋₊ : ℝ) + 1 - x := by linarith [Nat.lt_floor_add_one x]
  refine ⟨min δ ((⌊x⌋₊ : ℝ) + 1 - x), lt_min hδ hfl, fun y hxy hy => ?_⟩
  have hy1 : y < x + δ := lt_of_lt_of_le hy (by linarith [min_le_left δ ((⌊x⌋₊ : ℝ) + 1 - x)])
  have hy2 : y < ⌊x⌋₊ + 1 := lt_of_lt_of_le hy
    (by linarith [min_le_right δ ((⌊x⌋₊ : ℝ) + 1 - x)])
  have hfy : ⌊y⌋₊ = ⌊x⌋₊ := by
    rw [Nat.floor_eq_iff (hx.trans hxy)]
    exact ⟨(Nat.floor_le hx).trans hxy, hy2⟩
  unfold jumpD jumpPart Rankin.smoothCount
  rw [hfy, hc y hxy hy1]

/-! ### Validity -/

lemma floor_rcont (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (⌊y⌋₊ : ℝ)) (Ici x) x := by
  rcases lt_or_ge x 0 with hx | hx
  · apply ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ => (0 : ℝ))
      continuousWithinAt_const
    · filter_upwards [inter_mem_nhdsWithin (Ici x) (Iio_mem_nhds (show x < 1 by linarith))]
        with y hy
      simp only [Nat.cast_eq_zero, Nat.floor_eq_zero]; exact hy.2
    · simp only [Nat.cast_eq_zero, Nat.floor_eq_zero]; linarith
  · apply ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ => (⌊x⌋₊ : ℝ))
      continuousWithinAt_const
    · filter_upwards [inter_mem_nhdsWithin (Ici x)
        (Iio_mem_nhds (Nat.lt_floor_add_one x))] with y hy
      have : ⌊y⌋₊ = ⌊x⌋₊ := by
        rw [Nat.floor_eq_iff (hx.trans hy.1)]
        exact ⟨(Nat.floor_le hx).trans hy.1, hy.2⟩
      rw [this]
    · rfl

/-- **The target grows linearly**: `T(x) ≥ 0.7 x - X₀ - 1` on `[X₀, ∞)`. -/
theorem targetD_ge_linear (hθ : θ ≤ 1 / 2) (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) : 7 / 10 * x - X₀ - 1 ≤ targetD θ X₀ D x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hsp := switchOn_spacing (X₀ : ℝ)
  refine target_ge_linear hX hθ (countA_nonneg _) (fun v hv => ?_)
    (fun v hv => abs_osc_le hsp (abs_alphaD_le hX D) (by linarith))
    (osc_eq_zero_of_le hsp (by linarith) (switchOn_zero_ge _)) hx
  unfold absorbedDensityCap
  refine (min_le_right _ _).trans ?_
  have hl : 10 ^ 8 ≤ Real.log v := hX.trans (Real.log_le_log (by linarith) hv)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Lemma 3.3: the target of any data is a valid slot-model target.** -/
theorem tvalid_targetD (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀) (D : PrimeData)
    (hD : LocFinD D) : TValid X₀ (targetD θ X₀ D) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  -- `T ≥ X₀` on `[X₀, ∞)`
  have hge : ∀ x, (X₀ : ℝ) ≤ x → (X₀ : ℝ) ≤ targetD θ X₀ D x := by
    intro x hx
    rw [targetD_split θ D hx]
    have h1 := jumpD_nonneg D hD hx
    have h2 := contD_lower hθ hX hHB D hD le_rfl hx
    rw [contD_at] at h2
    have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have : 0 ≤ 0.08 * (x - X₀) / Real.log x := div_nonneg (by linarith) hl
    linarith
  refine ⟨fun x y hxy => ?_, fun x => ?_, fun y => ?_, hge X₀ le_rfl⟩
  · -- monotone
    rcases lt_or_ge y X₀ with hy | hy
    · rw [targetD_low θ D (lt_of_le_of_lt hxy hy), targetD_low θ D hy]
      exact_mod_cast Nat.floor_mono hxy
    rcases lt_or_ge x X₀ with hx | hx
    · rw [targetD_low θ D hx]
      have h1 : (⌊x⌋₊ : ℝ) ≤ X₀ := by
        have : ⌊x⌋₊ ≤ ⌊(X₀ : ℝ)⌋₊ := Nat.floor_mono hx.le
        rw [Nat.floor_natCast] at this
        exact_mod_cast this
      linarith [hge y hy]
    · rw [targetD_split θ D hx, targetD_split θ D hy]
      have h1 := jumpD_mono (X₀ := X₀) D hD hxy
      have h2 := contD_lower hθ hX hHB D hD hx hxy
      have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
      have : 0 ≤ 0.08 * (y - x) / Real.log y := div_nonneg (by linarith) hl
      linarith
  · -- right-continuous
    rcases lt_or_ge x X₀ with hx | hx
    · apply (floor_rcont x).congr_of_eventuallyEq
      · filter_upwards [inter_mem_nhdsWithin (Ici x) (Iio_mem_nhds hx)] with y hy
        exact targetD_low θ D hy.2
      · exact targetD_low θ D hx
    · have hc : ContinuousWithinAt (fun y => (X₀ : ℝ) + jumpD X₀ D x + contD θ X₀ D y)
          (Ici x) x :=
        continuousWithinAt_const.add
          (((contD_continuousOn hθ hX D hD) x hx).mono (Ici_subset_Ici.mpr hx))
      obtain ⟨δ, hδ, hJ⟩ := jumpD_rconst (X₀ := X₀) D hD (show 0 ≤ x by linarith)
      apply hc.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin, inter_mem_nhdsWithin (Ici x)
          (Iio_mem_nhds (show x < x + δ by linarith))] with y hy hy'
        rw [targetD_split θ D (hx.trans hy), hJ y hy hy'.2]
      · rw [targetD_split θ D hx]
  · -- unbounded
    refine ⟨max (X₀ : ℝ) (10 / 7 * (y + X₀ + 1)), ?_⟩
    have hm : (X₀ : ℝ) ≤ max (X₀ : ℝ) (10 / 7 * (y + X₀ + 1)) := le_max_left _ _
    have h := targetD_ge_linear (θ := θ) (by linarith [hθ.2]) hX D hm
    have h2 := le_max_right (X₀ : ℝ) (10 / 7 * (y + X₀ + 1))
    linarith

/-- **`ValidHyp` from (84)**. -/
theorem validHyp_of_HB (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀) : ValidHyp θ X₀ :=
  fun D hD => tvalid_targetD hθ hX hHB D hD

/-- **`SlopeHyp` from (84)**: `T(x') - T(x) ≥ C(x') - C(x) ≥ 0.08 (x' - x)/log x'`. -/
theorem slopeHyp_of_HB (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀) : SlopeHyp θ X₀ := by
  intro D hD x x' hx hxx
  rw [targetD_split θ D hx, targetD_split θ D (hx.trans hxx)]
  have h1 := jumpD_mono (X₀ := X₀) D hD hxx
  have h2 := contD_lower hθ hX hHB D hD hx hxx
  linarith

/-- (84) from a threshold `x₁ ≤ X₀` gives it from `X₀`. -/
lemma ShortIntervalPNTFrom.mono {x₁ x₂ : ℝ} (h : ShortIntervalPNTFrom x₁) (h12 : x₁ ≤ x₂) :
    ShortIntervalPNTFrom x₂ := fun q a b hq => h q a b (h12.trans hq)

end BModel

end
