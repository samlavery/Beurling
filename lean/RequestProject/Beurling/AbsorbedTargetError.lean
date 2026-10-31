module

public import RequestProject.Beurling.AbsorbedPart

/-!
# The absorbed part of the target error (Lemma 3.4)

For the absorbed set `A ⊆ ℝ` (a locally finite set of values of elements), each `a ∈ A` is
smoothed over the window `[u_a, a]`, where `u_a + h(u_a) = a` for a window `h` (`IsWin`; the
window of the construction is the θ-free `winH`), with density `1/h`:

  `ρ_A(v) = ∑_{a ∈ A} 1[u_a ≤ v ≤ a] / h(v)`   (`absorbedDensity`),

and the target uses the capped density `ρ̄_A = min(ρ_A, 0.1/log v)` (`absorbedDensityCap`).

* `Absorbed.absorbed_target_error` : **Lemma 3.4, absorbed part**: if `A` lies above `X₀`
  (`u_a ≥ X₀ ≥ 1` for `a ∈ A`) and `ρ_A ≤ ε` on `[X₀, ∞)`, then for `x ≥ X₀`
  `|#(A ∩ [1, x]) - ∫_{X₀}^x ρ_A| ≤ ε h(x) + (1/8) ∫_{X₀}^x ρ_A(v) h(v)/v dv`.
* `Absorbed.absorbed_target_error_cap` : the same for the capped density, given the bound
  `ρ_A(v) ≤ (log v)^{-4}` of Lemma 6.27(a) and `log X₀ ≥ 3`; then the cap does not bind and the
  error is at most `((log X₀)^{-4} + (log X₀)^{-3}/24) h(x) ≤ 2 h(x)`.

As in the paper the proof splits the difference into the elements `a ≤ x`, each contributing
`1 - M_a ∈ [0, 1 - h(u_a)/h(a)] ⊆ [0, (1/8) log(a/u_a)]` with `M_a = ∫_{u_a}^a dv/h(v)` (as `h` is
non-decreasing with `d log h/d log u ≤ 1/8`), and the elements in flight (`u_a < x < a`), each
contributing `-∫_{u_a}^x dv/h(v)`, supported in `(x - h(x), x]`. (The paper bounds the first sum by
`∫ h' ρ_A ≤ (392Λ²)⁻⁴ h(x)`; the bound `(1/8) ∫ ρ_A h/v` used here gives `≤ h(x)/(24 Λ³)`.)
-/

@[expose] public section

open Set Filter MeasureTheory Finset

namespace Absorbed

open scoped Classical

/-- The contribution `1[u_a ≤ v ≤ a] / h(v)` of `a` to `ρ_A(v)` (zero off `A`). -/
noncomputable def absorbedBump (h : ℝ → ℝ) (A : Set ℝ) (u : ℝ → ℝ) (a : ℝ) (v : ℝ) : ℝ :=
  if a ∈ A then (Icc (u a) (a : ℝ)).indicator (fun w => (h w)⁻¹) v else 0

/-- The smoothed absorbed density `ρ_A(v) = ∑_{a ∈ A} 1[u_a ≤ v ≤ a] / h(v)`. -/
noncomputable def absorbedDensity (h : ℝ → ℝ) (A : Set ℝ) (u : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' a : ℝ, absorbedBump h A u a v

/-- The capped absorbed density `ρ̄_A(v) = min(ρ_A(v), 0.1/log v)` used in the target (6). -/
noncomputable def absorbedDensityCap (h : ℝ → ℝ) (A : Set ℝ) (u : ℝ → ℝ) (v : ℝ) : ℝ :=
  min (absorbedDensity h A u v) (0.1 / Real.log v)

/-- The standing hypotheses for Lemma 3.4: `h` is a window, `X₀ ≥ 1`, and every `a ∈ A` has
`u_a + h(u_a) = a` with `u_a ≥ X₀` (`A` is empty near `X₀`), and `A` is locally finite. -/
structure AbsorbedWindowHyp (h : ℝ → ℝ) (X₀ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) : Prop where
  win : IsWin h
  X₀_ge : 1 ≤ X₀
  u_ge : ∀ a ∈ A, X₀ ≤ u a
  u_eq : ∀ a ∈ A, u a + h (u a) = a
  fin : LocFin A

variable {w : ℝ → ℝ} {X₀ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}

lemma absorbedBump_nonneg (hw : IsWin w) (hX : 0 < X₀) {a : ℝ} {v : ℝ} (hv : X₀ ≤ v) :
    0 ≤ absorbedBump w A u a v := by
  unfold absorbedBump
  split_ifs
  · exact Set.indicator_apply_nonneg (fun _ => inv_nonneg.mpr (hw.pos v (by linarith)).le)
  · exact le_rfl

/-- The interval integral of `1_{[U, a]} g` over `[X, x]`, for `X ≤ U ≤ min(a, x)`. -/
lemma integral_indicator_Icc {g : ℝ → ℝ} {X x U a : ℝ} (h1 : X ≤ U) (h2 : U ≤ a) (h3 : U ≤ x) :
    ∫ v in X..x, (Icc U a).indicator g v = ∫ v in U..min a x, g v := by
  have hX : X ≤ x := h1.trans h3
  rw [intervalIntegral.integral_congr_ae (g := (Ioc U a).indicator g) ?_]
  · rw [intervalIntegral.integral_of_le hX, setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc,
      max_eq_right h1, min_comm, intervalIntegral.integral_of_le (le_min h2 h3)]
  · filter_upwards [Measure.ae_ne volume U] with v hv _
    have : v ∈ Icc U a ↔ v ∈ Ioc U a :=
      ⟨fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm hv), h.2⟩, fun h => ⟨h.1.le, h.2⟩⟩
    simp only [Set.indicator_apply, this]

lemma X₀_pos (h : AbsorbedWindowHyp w X₀ A u) : 0 < X₀ := by linarith [h.X₀_ge]

lemma u_pos (h : AbsorbedWindowHyp w X₀ A u) {a : ℝ} (ha : a ∈ A) : 0 < u a := by
  linarith [h.u_ge a ha, h.X₀_ge]

lemma u_lt (h : AbsorbedWindowHyp w X₀ A u) {a : ℝ} (ha : a ∈ A) : u a < a := by
  have := h.win.pos (u a) (u_pos h ha)
  linarith [h.u_eq a ha]

/-- `1/h` is continuous on `[X, x]` for `X > 0`. -/
lemma continuousOn_inv_win (hw : IsWin w) {X x : ℝ} (hX : 0 < X) :
    ContinuousOn (fun v => (w v)⁻¹) (Icc X x) :=
  (hw.cont.mono fun v hv => lt_of_lt_of_le hX hv.1).inv₀
    fun v hv => (hw.pos v (lt_of_lt_of_le hX hv.1)).ne'

/-- `M_a = ∫_{u_a}^a dv/h(v) ∈ [(u_a/a)^{1/8}, 1]`. -/
lemma mass_bounds (h : AbsorbedWindowHyp w X₀ A u) {a : ℝ} (ha : a ∈ A) :
    (u a / a) ^ (1 / 8 : ℝ) ≤ ∫ v in u a..(a : ℝ), (w v)⁻¹ ∧
      ∫ v in u a..(a : ℝ), (w v)⁻¹ ≤ 1 := by
  have hU := u_pos h ha
  have hUa := u_lt h ha
  have hcont : ContinuousOn (fun v : ℝ => (w v)⁻¹) (uIcc (u a) a) := by
    rw [uIcc_of_le hUa.le]; exact continuousOn_inv_win h.win hU
  have hdiff : (a : ℝ) - u a = w (u a) := by linarith [h.u_eq a ha]
  have hha := h.win.pos a (by linarith)
  have hhu := h.win.pos (u a) hU
  constructor
  · have := intervalIntegral.integral_mono_on hUa.le (f := fun _ => (w a)⁻¹)
      (intervalIntegrable_const (μ := volume)) hcont.intervalIntegrable
      (fun v hv => inv_anti₀ (h.win.pos v (by linarith [hv.1])) (h.win.mono' (by linarith [hv.1])
        hv.2))
    simp only [intervalIntegral.integral_const, smul_eq_mul, hdiff] at this
    have hr := h.win.ratio' hU hUa.le
    have : (u a / a) ^ (1 / 8 : ℝ) ≤ w (u a) * (w a)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hha]; exact hr
    linarith
  · have := intervalIntegral.integral_mono_on hUa.le (g := fun _ => (w (u a))⁻¹)
      hcont.intervalIntegrable (intervalIntegrable_const (μ := volume))
      (fun v hv => inv_anti₀ hhu (h.win.mono' hU hv.1))
    simp only [intervalIntegral.integral_const, smul_eq_mul, hdiff] at this
    rwa [mul_inv_cancel₀ hhu.ne'] at this

/-- The density is a finite sum on `[X₀, x]`, over the elements `a ≤ 2x` of `A`. -/
lemma absorbedDensity_eq_sum (h : AbsorbedWindowHyp w X₀ A u) {x v : ℝ} (hv : X₀ ≤ v)
    (hvx : v ≤ x) :
    absorbedDensity w A u v = ∑ a ∈ below h.fin (2 * x), absorbedBump w A u a v := by
  unfold absorbedDensity
  apply tsum_eq_sum
  intro a ha
  rw [mem_below] at ha
  unfold absorbedBump
  split_ifs with hA
  · have ha' : 2 * x < a := by by_contra hc; exact ha ⟨hA, not_lt.mp hc⟩
    apply Set.indicator_of_notMem
    rintro ⟨h1, h2⟩
    have hU := u_pos h hA
    have hx1 : 1 ≤ x := by linarith [h.X₀_ge]
    have e1 : w (u a) ≤ w x := h.win.mono' hU (h1.trans hvx)
    have e2 : w x ≤ x := h.win.le_self hx1
    linarith [h.u_eq a hA]
  · rfl

lemma intervalIntegrable_absorbedBump (h : AbsorbedWindowHyp w X₀ A u) (a : ℝ) {x : ℝ}
    (hx : X₀ ≤ x) : IntervalIntegrable (absorbedBump w A u a) volume X₀ x := by
  by_cases hA : a ∈ A
  · have hc : IntervalIntegrable (fun v : ℝ => (w v)⁻¹) volume X₀ x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hx]; exact continuousOn_inv_win h.win (X₀_pos h)
    have he : absorbedBump w A u a = (Icc (u a) (a : ℝ)).indicator (fun v => (w v)⁻¹) := by
      ext v; simp [absorbedBump, hA]
    rw [he]
    rw [intervalIntegrable_iff] at hc ⊢
    exact hc.indicator measurableSet_Icc
  · have he : absorbedBump w A u a = fun _ => 0 := by ext v; simp [absorbedBump, hA]
    rw [he]; exact intervalIntegrable_const

/-- `v ↦ h(v)/v` is continuous on `[X, x]` for `X > 0`. -/
lemma continuousOn_win_div (hw : IsWin w) {X x : ℝ} (hX : 0 < X) :
    ContinuousOn (fun v => w v / v) (Icc X x) :=
  (hw.cont.mono fun v hv => lt_of_lt_of_le hX hv.1).div continuousOn_id
    fun v hv => (lt_of_lt_of_le hX hv.1).ne'

/-- The elements `a ≤ x`: `1 - M_a ≤ (1/8) log(a/u_a) = (1/8) ∫ 1[u_a ≤ v ≤ a] (h(v)/v) / h(v) dv`. -/
lemma bump_upper (h : AbsorbedWindowHyp w X₀ A u) (a : ℝ) {x : ℝ} (hx : X₀ ≤ x) :
    (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) - ∫ v in X₀..x, absorbedBump w A u a v ≤
      1 / 8 * ∫ v in X₀..x, absorbedBump w A u a v * (w v / v) := by
  have hX0 := X₀_pos h
  by_cases hcase : a ∈ A ∧ (a : ℝ) ≤ x
  · obtain ⟨hA, hax⟩ := hcase
    rw [if_pos ⟨hA, hax⟩]
    have hUX := h.u_ge a hA
    have hU := u_pos h hA
    have hUa := u_lt h hA
    have ha0 : (0 : ℝ) < a := by linarith
    have hbump : absorbedBump w A u a = (Icc (u a) (a : ℝ)).indicator (fun v => (w v)⁻¹) := by
      ext v; simp [absorbedBump, hA]
    have hI : ∫ v in X₀..x, absorbedBump w A u a v = ∫ v in u a..(a : ℝ), (w v)⁻¹ := by
      rw [hbump, integral_indicator_Icc hUX hUa.le (hUa.le.trans hax), min_eq_left hax]
    have hJ : ∫ v in X₀..x, absorbedBump w A u a v * (w v / v) = Real.log (a / u a) := by
      have he : (fun v => absorbedBump w A u a v * (w v / v)) =
          (Icc (u a) (a : ℝ)).indicator (fun v => (w v)⁻¹ * (w v / v)) := by
        ext v; rw [hbump, Set.indicator_mul_left]
      rw [he, integral_indicator_Icc hUX hUa.le (hUa.le.trans hax), min_eq_left hax,
        ← integral_inv_of_pos hU ha0]
      apply intervalIntegral.integral_congr
      intro v hv; rw [uIcc_of_le hUa.le] at hv
      have hv0 : 0 < v := by linarith [hv.1]
      have := (h.win.pos v hv0).ne'
      simp only
      field_simp
    rw [hI, hJ]
    have hM := (mass_bounds h hA).1
    have key : (u a / a) ^ (1 / 8 : ℝ) = Real.exp (-(1 / 8 * Real.log (a / u a))) := by
      rw [Real.rpow_def_of_pos (div_pos hU ha0),
        show Real.log (u a / a) = -Real.log (a / u a) by rw [← Real.log_inv, inv_div]]
      ring_nf
    linarith [Real.add_one_le_exp (-(1 / 8 * Real.log (a / u a)))]
  · rw [if_neg hcase]
    have hI : 0 ≤ ∫ v in X₀..x, absorbedBump w A u a v :=
      intervalIntegral.integral_nonneg hx fun v hv => absorbedBump_nonneg h.win hX0 hv.1
    have hJ : 0 ≤ ∫ v in X₀..x, absorbedBump w A u a v * (w v / v) :=
      intervalIntegral.integral_nonneg hx fun v hv =>
        mul_nonneg (absorbedBump_nonneg h.win hX0 hv.1)
          (div_nonneg (h.win.pos v (by linarith [hv.1])).le (by linarith [hv.1]))
    nlinarith

/-- The elements in flight: their contribution is supported in `(x - h(x), x]`. -/
lemma bump_lower (h : AbsorbedWindowHyp w X₀ A u) (a : ℝ) {x : ℝ} (hx : X₀ ≤ x) :
    -∫ v in X₀..x, (Ioi (x - w x)).indicator (absorbedBump w A u a) v ≤
      (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) - ∫ v in X₀..x, absorbedBump w A u a v := by
  have hX0 := X₀_pos h
  by_cases hA : a ∈ A
  · have hUX := h.u_ge a hA
    have hU := u_pos h hA
    have hUa := u_lt h hA
    have hbump : absorbedBump w A u a = (Icc (u a) (a : ℝ)).indicator (fun v => (w v)⁻¹) := by
      ext v; simp [absorbedBump, hA]
    have hJ : 0 ≤ ∫ v in X₀..x, (Ioi (x - w x)).indicator (absorbedBump w A u a) v :=
      intervalIntegral.integral_nonneg hx fun v hv =>
        Set.indicator_apply_nonneg fun _ => absorbedBump_nonneg h.win hX0 hv.1
    by_cases hax : (a : ℝ) ≤ x
    · rw [if_pos ⟨hA, hax⟩]
      have hI : ∫ v in X₀..x, absorbedBump w A u a v = ∫ v in u a..(a : ℝ), (w v)⁻¹ := by
        rw [hbump, integral_indicator_Icc hUX hUa.le (hUa.le.trans hax), min_eq_left hax]
      rw [hI]
      linarith [(mass_bounds h hA).2]
    · rw [if_neg (fun hc => hax hc.2), zero_sub, neg_le_neg_iff]
      apply le_of_eq
      apply intervalIntegral.integral_congr
      intro v hv; rw [uIcc_of_le hx] at hv
      simp only [Set.indicator_apply]
      split_ifs with hv'
      · rfl
      · rw [hbump]
        apply Set.indicator_of_notMem
        rintro ⟨h1, h2⟩
        have e1 : w (u a) ≤ w x := h.win.mono' hU (h1.trans hv.2)
        simp only [Set.mem_Ioi, not_lt] at hv'
        push_neg at hax
        linarith [h.u_eq a hA]
  · have he : absorbedBump w A u a = fun _ => 0 := by ext v; simp [absorbedBump, hA]
    simp [he, hA]

lemma one_le_of_mem (h : AbsorbedWindowHyp w X₀ A u) {a : ℝ} (ha : a ∈ A) : 1 ≤ a := by
  linarith [u_lt h ha, h.u_ge a ha, h.X₀_ge]

lemma countA_eq_sum (h : AbsorbedWindowHyp w X₀ A u) {x : ℝ} (hx : X₀ ≤ x) :
    countA A x = ∑ a ∈ below h.fin (2 * x), (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) := by
  have hx0 : 0 ≤ x := by linarith [h.X₀_ge]
  rw [countA_eq_cnt (fun a ha => one_le_of_mem h ha) (below h.fin (2 * x))
    (fun a ha => ((mem_below h.fin).1 ha).1)
    (fun a ha hax => (mem_below h.fin).2 ⟨ha, by linarith⟩)]
  unfold cnt
  refine Finset.sum_congr rfl fun a ha => ?_
  have := ((mem_below h.fin).1 ha).1
  simp [this]

/-- `∫_{X₀}^x 1_{(x - h, ∞)} g ≤ c h` when `g ≤ c` on `[X₀, x]` and `h ≥ 0`. -/
lemma integral_window_le {g : ℝ → ℝ} {x c h : ℝ} (hx : X₀ ≤ x) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (hg : IntervalIntegrable g volume X₀ x) (hg1 : ∀ v ∈ Icc X₀ x, g v ≤ c) :
    ∫ v in X₀..x, (Ioi (x - h)).indicator g v ≤ c * h := by
  have hm : X₀ ⊔ (x - h) ≤ x := max_le hx (by linarith)
  have hconst : ∫ v in X₀..x, (Ioi (x - h)).indicator (fun _ => c) v = (x - X₀ ⊔ (x - h)) * c := by
    rw [intervalIntegral.integral_of_le hx, setIntegral_indicator measurableSet_Ioi,
      Set.Ioc_inter_Ioi, ← intervalIntegral.integral_of_le hm]
    simp
  have hmono : ∫ v in X₀..x, (Ioi (x - h)).indicator g v ≤
      ∫ v in X₀..x, (Ioi (x - h)).indicator (fun _ => c) v := by
    apply intervalIntegral.integral_mono_on hx
    · rw [intervalIntegrable_iff] at hg ⊢; exact hg.indicator measurableSet_Ioi
    · rw [intervalIntegrable_iff]
      exact (integrableOn_const (by simp)).indicator measurableSet_Ioi
    · intro v hv
      simp only [Set.indicator_apply]
      split_ifs
      · exact hg1 v hv
      · exact le_rfl
  rw [hconst] at hmono
  have : x - X₀ ⊔ (x - h) ≤ h := by have := le_max_right X₀ (x - h); linarith
  nlinarith

/-- **Lemma 3.4, absorbed part.** If every `a ∈ A` has `u_a + h(u_a) = a`, `u_a ≥ X₀ ≥ 1`, and
`ρ_A ≤ ε` on `[X₀, ∞)`, then for `x ≥ X₀`,
`|#(A ∩ [1, x]) - ∫_{X₀}^x ρ_A| ≤ ε h(x) + (1/8) ∫_{X₀}^x ρ_A(v) h(v)/v dv`. -/
theorem absorbed_target_error_loc (h : AbsorbedWindowHyp w X₀ A u) {ε : ℝ}
    {x : ℝ} (hx : X₀ ≤ x) (hρ : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensity w A u v ≤ ε) :
    |countA A x - ∫ v in X₀..x, absorbedDensity w A u v| ≤
      ε * w x + 1 / 8 * ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) := by
  have hX0 := X₀_pos h
  have hx0 : 0 < x := by linarith
  set S := below h.fin (2 * x)
  have hε : 0 ≤ ε := by
    refine le_trans ?_ (hρ X₀ le_rfl hx)
    rw [absorbedDensity_eq_sum h le_rfl hx]
    exact Finset.sum_nonneg fun a _ => absorbedBump_nonneg h.win hX0 le_rfl
  have hint := fun a => intervalIntegrable_absorbedBump h a hx
  have hU : uIcc X₀ x = Icc X₀ x := uIcc_of_le hx
  -- the integral of the density is the sum of the integrals of the bumps
  have hρsum : ∫ v in X₀..x, absorbedDensity w A u v =
      ∑ a ∈ S, ∫ v in X₀..x, absorbedBump w A u a v := by
    rw [← intervalIntegral.integral_finset_sum fun a _ => hint a]
    apply intervalIntegral.integral_congr
    intro v hv; rw [hU] at hv
    exact absorbedDensity_eq_sum h hv.1 hv.2
  have hdiff : countA A x - ∫ v in X₀..x, absorbedDensity w A u v =
      ∑ a ∈ S, ((if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) -
        ∫ v in X₀..x, absorbedBump w A u a v) := by
    rw [hρsum, countA_eq_sum h hx, Finset.sum_sub_distrib]
  have hcont : ContinuousOn (fun v : ℝ => w v / v) (uIcc X₀ x) := by
    rw [hU]; exact continuousOn_win_div h.win hX0
  -- upper bound
  have hup : countA A x - ∫ v in X₀..x, absorbedDensity w A u v ≤
      1 / 8 * ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) := by
    rw [hdiff]
    refine le_trans (Finset.sum_le_sum fun a _ => bump_upper h a hx) ?_
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum fun a _ =>
      (hint a).mul_continuousOn hcont]
    apply le_of_eq
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv; rw [hU] at hv
    simp only
    rw [← Finset.sum_mul, ← absorbedDensity_eq_sum h hv.1 hv.2]
  have hJ0 : 0 ≤ ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) := by
    apply intervalIntegral.integral_nonneg hx
    intro v hv
    rw [absorbedDensity_eq_sum h hv.1 hv.2]
    exact mul_nonneg (Finset.sum_nonneg fun a _ => absorbedBump_nonneg h.win hX0 hv.1)
      (div_nonneg (h.win.pos v (by linarith [hv.1])).le (by linarith [hv.1]))
  -- lower bound
  have hlo : -(ε * w x) ≤ countA A x - ∫ v in X₀..x, absorbedDensity w A u v := by
    rw [hdiff]
    refine le_trans ?_ (Finset.sum_le_sum fun a _ => bump_lower h a hx)
    rw [Finset.sum_neg_distrib, neg_le_neg_iff,
      ← intervalIntegral.integral_finset_sum fun a _ => ?_]
    · have hcongr : ∫ v in X₀..x, ∑ a ∈ S, (Ioi (x - w x)).indicator (absorbedBump w A u a) v =
          ∫ v in X₀..x, (Ioi (x - w x)).indicator (absorbedDensity w A u) v := by
        apply intervalIntegral.integral_congr
        intro v hv; rw [hU] at hv
        simp only [Set.indicator_apply]
        split_ifs
        · exact (absorbedDensity_eq_sum h hv.1 hv.2).symm
        · simp
      rw [hcongr]
      apply integral_window_le hx (h.win.pos x hx0).le hε
      · refine (IntervalIntegrable.sum S fun a _ => hint a).congr ?_
        intro v hv
        rw [uIoc_of_le hx] at hv
        simp only [Finset.sum_apply]
        exact (absorbedDensity_eq_sum h hv.1.le hv.2).symm
      · intro v hv; exact hρ v hv.1 hv.2
    · have ha := hint a
      rw [intervalIntegrable_iff] at ha ⊢
      exact ha.indicator measurableSet_Ioi
  have := mul_nonneg hε (h.win.pos x hx0).le
  refine abs_le.mpr ⟨by linarith, by linarith⟩

theorem absorbed_target_error (h : AbsorbedWindowHyp w X₀ A u) {ε : ℝ}
    (hρ : ∀ v ≥ X₀, absorbedDensity w A u v ≤ ε) {x : ℝ} (hx : X₀ ≤ x) :
    |countA A x - ∫ v in X₀..x, absorbedDensity w A u v| ≤
      ε * w x + 1 / 8 * ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) :=
  absorbed_target_error_loc h hx fun v hv _ => hρ v hv

/-- `∫_{X}^x dv/(v log⁴ v) ≤ 1/(3 log³ X)` for `1 < X ≤ x`. -/
lemma integral_inv_log_pow_four_le {X x : ℝ} (hX : 1 < X) (hx : X ≤ x) :
    ∫ v in X..x, (Real.log v ^ 4)⁻¹ * v⁻¹ ≤ (Real.log X ^ 3)⁻¹ / 3 := by
  have hpos : ∀ v ∈ uIcc X x, 0 < Real.log v := fun v hv => by
    rw [uIcc_of_le hx] at hv; exact Real.log_pos (by linarith [hv.1])
  have hderiv : ∀ v ∈ uIcc X x, HasDerivAt (fun v => -(Real.log v ^ 3)⁻¹ / 3)
      ((Real.log v ^ 4)⁻¹ * v⁻¹) v := by
    intro v hv
    have hl := hpos v hv
    have hv0 : v ≠ 0 := by rw [uIcc_of_le hx] at hv; linarith [hv.1]
    have h1 : HasDerivAt (fun v => Real.log v ^ 3) (3 * Real.log v ^ 2 * v⁻¹) v := by
      have := (Real.hasDerivAt_log hv0).pow 3
      convert this using 1
    have h2 := ((h1.inv (pow_pos hl 3).ne').neg).div_const 3
    convert h2 using 1
    field_simp
  have hcont : ContinuousOn (fun v => (Real.log v ^ 4)⁻¹ * v⁻¹) (uIcc X x) := by
    intro v hv
    have hl := hpos v hv
    have hv0 : v ≠ 0 := by rw [uIcc_of_le hx] at hv; linarith [hv.1]
    exact (((Real.continuousAt_log hv0).pow 4).inv₀ (pow_pos hl 4).ne' |>.mul
      (continuousAt_inv₀ hv0)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have : 0 ≤ (Real.log x ^ 3)⁻¹ := by
    have := hpos x (by rw [uIcc_of_le hx]; exact ⟨hx, le_rfl⟩); positivity
  linarith

/-- **Lemma 3.4, absorbed part, for the capped density of the target.** With the density bound
`ρ_A(v) ≤ (log v)^{-4}` of Lemma 6.27(a) on `[X₀, ∞)` and `log X₀ ≥ 3`, the cap does not bind and
`|#(A ∩ [1, x]) - ∫_{X₀}^x ρ̄_A| ≤ ((log X₀)^{-4} + (log X₀)^{-3}/24) h(x) ≤ 2 h(x)` for
`x ≥ X₀`. -/
theorem absorbed_target_error_cap_loc (h : AbsorbedWindowHyp w X₀ A u)
    (hlog : 3 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x)
    (hρ : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensity w A u v ≤ (Real.log v) ^ (-4 : ℤ)) :
    |countA A x - ∫ v in X₀..x, absorbedDensityCap w A u v| ≤ 2 * w x := by
  have hX0 := X₀_pos h
  have hX1 : 1 < X₀ := by
    by_contra hc; push_neg at hc
    have := Real.log_le_sub_one_of_pos hX0; linarith
  have hlogv : ∀ v ≥ X₀, Real.log X₀ ≤ Real.log v := fun v hv => Real.log_le_log hX0 hv
  have hcap : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensityCap w A u v = absorbedDensity w A u v := by
    intro v hv hvx
    have hl : 3 ≤ Real.log v := hlog.trans (hlogv v hv)
    apply min_eq_left
    refine (hρ v hv hvx).trans ?_
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    have hl0 : 0 < Real.log v := by linarith
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : 0.1 / Real.log v * Real.log v ^ 4 = 0.1 * Real.log v ^ 3 := by
      field_simp
    rw [this]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hl 3]
  have hint : ∫ v in X₀..x, absorbedDensityCap w A u v =
      ∫ v in X₀..x, absorbedDensity w A u v := by
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le hx] at hv
    exact hcap v hv.1 hv.2
  rw [hint]
  have hL0 : 0 < Real.log X₀ := by linarith
  have hx0 : 0 < x := by linarith
  have hwx := h.win.pos x hx0
  have hε : (Real.log X₀) ^ (-4 : ℤ) ≤ 1 := by
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hρ' : ∀ v, X₀ ≤ v → v ≤ x → absorbedDensity w A u v ≤ (Real.log X₀) ^ (-4 : ℤ) := by
    intro v hv hvx
    refine (hρ v hv hvx).trans ?_
    rw [zpow_neg, zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hL0.le (hlogv v hv) 4)
  -- the second term: `∫ ρ_A h/v ≤ h(x) ∫ dv/(v log⁴ v) ≤ h(x)/(3 log³ X₀) ≤ h(x)`
  have hJ : ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) ≤ w x := by
    have hle : ∫ v in X₀..x, absorbedDensity w A u v * (w v / v) ≤
        ∫ v in X₀..x, w x * ((Real.log v ^ 4)⁻¹ * v⁻¹) := by
      apply intervalIntegral.integral_mono_on hx
      · have hc : ContinuousOn (fun v : ℝ => w v / v) (uIcc X₀ x) := by
          rw [uIcc_of_le hx]; exact continuousOn_win_div h.win hX0
        refine ((IntervalIntegrable.sum (below h.fin (2 * x)) fun a _ =>
          intervalIntegrable_absorbedBump h a hx).mul_continuousOn hc).congr ?_
        intro v hv
        rw [uIoc_of_le hx] at hv
        simp only [Finset.sum_apply]
        rw [absorbedDensity_eq_sum h hv.1.le hv.2]
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hx]
        intro v hv
        have hv0 : v ≠ 0 := by linarith [hv.1]
        have hl : 0 < Real.log v := Real.log_pos (by linarith [hv.1])
        exact (continuousAt_const.mul ((((Real.continuousAt_log hv0).pow 4).inv₀
          (pow_pos hl 4).ne').mul (continuousAt_inv₀ hv0))).continuousWithinAt
      · intro v hv
        have hv0 : 0 < v := by linarith [hv.1]
        have hl : 0 < Real.log v := Real.log_pos (by linarith [hv.1])
        have h1 := hρ v hv.1 hv.2
        rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast] at h1
        have h0 : 0 ≤ absorbedDensity w A u v := by
          rw [absorbedDensity_eq_sum h hv.1 hv.2]
          exact Finset.sum_nonneg fun a _ => absorbedBump_nonneg h.win hX0 hv.1
        have h2 : w v / v ≤ w x * v⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (h.win.mono' hv0 hv.2) (inv_nonneg.mpr hv0.le)
        calc absorbedDensity w A u v * (w v / v) ≤ (Real.log v ^ 4)⁻¹ * (w x * v⁻¹) :=
              mul_le_mul h1 h2 (div_nonneg (h.win.pos v hv0).le hv0.le) (by positivity)
          _ = w x * ((Real.log v ^ 4)⁻¹ * v⁻¹) := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    have h3 := integral_inv_log_pow_four_le hX1 hx
    have h4 : (Real.log X₀ ^ 3)⁻¹ / 3 ≤ 1 := by
      have : 1 ≤ Real.log X₀ ^ 3 := one_le_pow₀ (by linarith)
      have := inv_le_one_of_one_le₀ this
      linarith
    calc _ ≤ w x * ∫ v in X₀..x, (Real.log v ^ 4)⁻¹ * v⁻¹ := hle
      _ ≤ w x * 1 := mul_le_mul_of_nonneg_left (h3.trans h4) hwx.le
      _ = w x := mul_one _
  refine (absorbed_target_error_loc h hx hρ').trans ?_
  have : (Real.log X₀) ^ (-4 : ℤ) * w x ≤ 1 * w x := mul_le_mul_of_nonneg_right hε hwx.le
  linarith

theorem absorbed_target_error_cap (h : AbsorbedWindowHyp w X₀ A u)
    (hlog : 3 ≤ Real.log X₀)
    (hρ : ∀ v ≥ X₀, absorbedDensity w A u v ≤ (Real.log v) ^ (-4 : ℤ)) {x : ℝ} (hx : X₀ ≤ x) :
    |countA A x - ∫ v in X₀..x, absorbedDensityCap w A u v| ≤ 2 * w x :=
  absorbed_target_error_cap_loc h hlog hx fun v hv _ => hρ v hv

end Absorbed

end
