module

public import RequestProject.Beurling.AbsorbedPart

/-!
# The absorbed part of the target error (Lemma 3.4)

For the absorbed set `A ⊆ ℝ` (a locally finite set of values of elements), each `a ∈ A` is
smoothed over the window `[u_a, a]`, where
`u_a + h(u_a) = a` and `h(u) = u^b`, with density `1/h`:

  `ρ_A(v) = ∑_{a ∈ A} 1[u_a ≤ v ≤ a] / h(v)`   (`absorbedDensity`),

and the target uses the capped density `ρ̄_A = min(ρ_A, 0.1/log v)` (`absorbedDensityCap`).

* `Absorbed.absorbed_target_error` : **Lemma 3.4, absorbed part**: if `A` lies above `X₀`
  (`u_a ≥ X₀ ≥ 1` for `a ∈ A`), `0 < b ≤ 1` and `ρ_A ≤ ε` on `[X₀, ∞)`, then
  `|#(A ∩ [1, x]) - ∫_{X₀}^x ρ_A| ≤ ε x^b` for `x ≥ X₀`.
* `Absorbed.absorbed_target_error_cap` : the same for the capped density, given the bound
  `ρ_A(v) ≤ (log v)^{-4}` of Lemma 6.27(a) and `log X₀ ≥ 3`; then the cap does not bind and the
  error is at most `(log X₀)^{-4} x^b ≤ 2 x^b`.

As in the paper the proof splits the difference into the elements `a ≤ x`, each contributing
`1 - M_a ∈ [0, b log(a/u_a)]` with `M_a = ∫_{u_a}^a dv/h(v)`, and the elements in flight
(`u_a < x < a`), each contributing `-∫_{u_a}^x dv/h(v)`, supported in `(x - h(x), x]`.
-/

@[expose] public section

open Set Filter MeasureTheory Finset

namespace Absorbed

open scoped Classical

/-- The contribution `1[u_a ≤ v ≤ a] / h(v)` (`h(v) = v^b`) of `a` to `ρ_A(v)` (zero off `A`). -/
noncomputable def absorbedBump (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (a : ℝ) (v : ℝ) : ℝ :=
  if a ∈ A then (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b)) v else 0

/-- The smoothed absorbed density `ρ_A(v) = ∑_{a ∈ A} 1[u_a ≤ v ≤ a] / v^b`. -/
noncomputable def absorbedDensity (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' a : ℝ, absorbedBump b A u a v

/-- The capped absorbed density `ρ̄_A(v) = min(ρ_A(v), 0.1/log v)` used in the target (6). -/
noncomputable def absorbedDensityCap (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (v : ℝ) : ℝ :=
  min (absorbedDensity b A u v) (0.1 / Real.log v)

/-- The standing hypotheses for Lemma 3.4: `0 < b ≤ 1`, `X₀ ≥ 1`, and every `a ∈ A` has
`u_a + u_a^b = a` with `u_a ≥ X₀` (`A` is empty near `X₀`), and `A` is locally finite. -/
structure AbsorbedWindowHyp (b X₀ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) : Prop where
  b_pos : 0 < b
  b_le : b ≤ 1
  X₀_ge : 1 ≤ X₀
  u_ge : ∀ a ∈ A, X₀ ≤ u a
  u_eq : ∀ a ∈ A, u a + u a ^ b = a
  fin : LocFin A

variable {b X₀ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}

lemma absorbedBump_nonneg (hX : 0 < X₀) {a : ℝ} {v : ℝ} (hv : X₀ ≤ v) :
    0 ≤ absorbedBump b A u a v := by
  unfold absorbedBump
  split_ifs
  · exact Set.indicator_apply_nonneg (fun _ => Real.rpow_nonneg (by linarith) _)
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

lemma u_lt (h : AbsorbedWindowHyp b X₀ A u) {a : ℝ} (ha : a ∈ A) : u a < a := by
  have hU : 0 < u a := by linarith [h.u_ge a ha, h.X₀_ge]
  have := Real.rpow_pos_of_pos hU b
  linarith [h.u_eq a ha]

/-- `M_a = ∫_{u_a}^a v^{-b} dv ∈ [(u_a/a)^b, 1]`. -/
lemma mass_bounds (h : AbsorbedWindowHyp b X₀ A u) {a : ℝ} (ha : a ∈ A) :
    (u a) ^ b * (a : ℝ) ^ (-b) ≤ ∫ v in u a..(a : ℝ), v ^ (-b) ∧
      ∫ v in u a..(a : ℝ), v ^ (-b) ≤ 1 := by
  have hU : 0 < u a := by linarith [h.u_ge a ha, h.X₀_ge]
  have hUa := u_lt h ha
  have hb := h.b_pos
  have hcont : ContinuousOn (fun v : ℝ => v ^ (-b)) (uIcc (u a) a) := by
    intro v hv; rw [uIcc_of_le hUa.le] at hv
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  have hdiff : (a : ℝ) - u a = u a ^ b := by linarith [h.u_eq a ha]
  constructor
  · have := intervalIntegral.integral_mono_on hUa.le (f := fun _ => (a : ℝ) ^ (-b))
      (intervalIntegrable_const (μ := volume)) hcont.intervalIntegrable
      (fun v hv => Real.rpow_le_rpow_of_nonpos (by linarith [hv.1]) hv.2 (by linarith))
    simpa [hdiff] using this
  · have := intervalIntegral.integral_mono_on hUa.le (g := fun _ => (u a) ^ (-b))
      hcont.intervalIntegrable (intervalIntegrable_const (μ := volume))
      (fun v hv => Real.rpow_le_rpow_of_nonpos hU hv.1 (by linarith))
    simp only [intervalIntegral.integral_const, smul_eq_mul, hdiff] at this
    rwa [← Real.rpow_add hU, add_neg_cancel, Real.rpow_zero] at this

/-- The density is a finite sum on `[X₀, x]`, over the elements `a ≤ 2x` of `A`. -/
lemma absorbedDensity_eq_sum (h : AbsorbedWindowHyp b X₀ A u) {x v : ℝ} (hv : X₀ ≤ v)
    (hvx : v ≤ x) :
    absorbedDensity b A u v = ∑ a ∈ below h.fin (2 * x), absorbedBump b A u a v := by
  unfold absorbedDensity
  apply tsum_eq_sum
  intro a ha
  rw [mem_below] at ha
  unfold absorbedBump
  split_ifs with hA
  · have ha' : 2 * x < a := by by_contra hc; exact ha ⟨hA, not_lt.mp hc⟩
    apply Set.indicator_of_notMem
    rintro ⟨h1, h2⟩
    have hU : 0 ≤ u a := by linarith [h.u_ge a hA, h.X₀_ge]
    have hx1 : 1 ≤ x := by linarith [h.X₀_ge]
    have e1 : u a ^ b ≤ x ^ b := Real.rpow_le_rpow hU (h1.trans hvx) h.b_pos.le
    have e2 : x ^ b ≤ x := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 h.b_le
    linarith [h.u_eq a hA]
  · rfl

lemma intervalIntegrable_absorbedBump (h : AbsorbedWindowHyp b X₀ A u) (a : ℝ) {x : ℝ}
    (hx : X₀ ≤ x) : IntervalIntegrable (absorbedBump b A u a) volume X₀ x := by
  by_cases hA : a ∈ A
  · have hc : IntervalIntegrable (fun w : ℝ => w ^ (-b)) volume X₀ x := by
      apply ContinuousOn.intervalIntegrable
      intro v hv; rw [uIcc_of_le hx] at hv
      exact (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [hv.1, h.X₀_ge]))).continuousWithinAt
    have he : absorbedBump b A u a = (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b)) := by
      ext v; simp [absorbedBump, hA]
    rw [he]
    rw [intervalIntegrable_iff] at hc ⊢
    exact hc.indicator measurableSet_Icc
  · have he : absorbedBump b A u a = fun _ => 0 := by ext v; simp [absorbedBump, hA]
    rw [he]; exact intervalIntegrable_const

/-- The elements `a ≤ x`: `1 - M_a ≤ b log(a/u_a) = b ∫ 1[u_a ≤ v ≤ a] v^{b-1} / h(v) dv`. -/
lemma bump_upper (h : AbsorbedWindowHyp b X₀ A u) (a : ℝ) {x : ℝ} (hx : X₀ ≤ x) :
    (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) - ∫ v in X₀..x, absorbedBump b A u a v ≤
      b * ∫ v in X₀..x, absorbedBump b A u a v * v ^ (b - 1) := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hb := h.b_pos
  by_cases hcase : a ∈ A ∧ (a : ℝ) ≤ x
  · obtain ⟨hA, hax⟩ := hcase
    rw [if_pos ⟨hA, hax⟩]
    have hUX := h.u_ge a hA
    have hU : 0 < u a := by linarith
    have hUa := u_lt h hA
    have ha0 : (0 : ℝ) < a := by linarith
    have hbump : absorbedBump b A u a = (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b)) := by
      ext v; simp [absorbedBump, hA]
    have hI : ∫ v in X₀..x, absorbedBump b A u a v = ∫ v in u a..(a : ℝ), v ^ (-b) := by
      rw [hbump, integral_indicator_Icc hUX hUa.le (hUa.le.trans hax), min_eq_left hax]
    have hJ : ∫ v in X₀..x, absorbedBump b A u a v * v ^ (b - 1) = Real.log (a / u a) := by
      have he : (fun v => absorbedBump b A u a v * v ^ (b - 1)) =
          (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b) * w ^ (b - 1)) := by
        ext v; rw [hbump, Set.indicator_mul_left]
      rw [he, integral_indicator_Icc hUX hUa.le (hUa.le.trans hax), min_eq_left hax,
        ← integral_inv_of_pos hU ha0]
      apply intervalIntegral.integral_congr
      intro v hv; rw [uIcc_of_le hUa.le] at hv
      have hv0 : 0 < v := by linarith [hv.1]
      simp only
      rw [← Real.rpow_add hv0, show -b + (b - 1) = -1 by ring, Real.rpow_neg_one]
    rw [hI, hJ]
    have hM := (mass_bounds h hA).1
    have key : u a ^ b * (a : ℝ) ^ (-b) = Real.exp (-(b * Real.log (a / u a))) := by
      rw [Real.rpow_neg ha0.le, ← div_eq_mul_inv, ← Real.div_rpow hU.le ha0.le,
        Real.rpow_def_of_pos (div_pos hU ha0),
        show Real.log (u a / a) = -Real.log (a / u a) by rw [← Real.log_inv, inv_div]]
      ring_nf
    linarith [Real.add_one_le_exp (-(b * Real.log (a / u a)))]
  · rw [if_neg hcase]
    have hI : 0 ≤ ∫ v in X₀..x, absorbedBump b A u a v :=
      intervalIntegral.integral_nonneg hx fun v hv => absorbedBump_nonneg hX0 hv.1
    have hJ : 0 ≤ ∫ v in X₀..x, absorbedBump b A u a v * v ^ (b - 1) :=
      intervalIntegral.integral_nonneg hx fun v hv =>
        mul_nonneg (absorbedBump_nonneg hX0 hv.1) (Real.rpow_nonneg (by linarith [hv.1]) _)
    nlinarith

/-- The elements in flight: their contribution is supported in `(x - x^b, x]`. -/
lemma bump_lower (h : AbsorbedWindowHyp b X₀ A u) (a : ℝ) {x : ℝ} (hx : X₀ ≤ x) :
    -∫ v in X₀..x, (Ioi (x - x ^ b)).indicator (absorbedBump b A u a) v ≤
      (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) - ∫ v in X₀..x, absorbedBump b A u a v := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hx0 : 0 < x := by linarith
  have hb := h.b_pos
  by_cases hA : a ∈ A
  · have hUX := h.u_ge a hA
    have hU : 0 < u a := by linarith
    have hUa := u_lt h hA
    have hbump : absorbedBump b A u a = (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b)) := by
      ext v; simp [absorbedBump, hA]
    have hJ : 0 ≤ ∫ v in X₀..x, (Ioi (x - x ^ b)).indicator (absorbedBump b A u a) v :=
      intervalIntegral.integral_nonneg hx fun v hv =>
        Set.indicator_apply_nonneg fun _ => absorbedBump_nonneg hX0 hv.1
    by_cases hax : (a : ℝ) ≤ x
    · rw [if_pos ⟨hA, hax⟩]
      have hI : ∫ v in X₀..x, absorbedBump b A u a v = ∫ v in u a..(a : ℝ), v ^ (-b) := by
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
        have e1 : u a ^ b ≤ x ^ b := Real.rpow_le_rpow hU.le (h1.trans hv.2) hb.le
        simp only [Set.mem_Ioi, not_lt] at hv'
        push_neg at hax
        linarith [h.u_eq a hA]
  · have he : absorbedBump b A u a = fun _ => 0 := by ext v; simp [absorbedBump, hA]
    simp [he, hA]

lemma one_le_of_mem (h : AbsorbedWindowHyp b X₀ A u) {a : ℝ} (ha : a ∈ A) : 1 ≤ a := by
  linarith [u_lt h ha, h.u_ge a ha, h.X₀_ge]

lemma countA_eq_sum (h : AbsorbedWindowHyp b X₀ A u) {x : ℝ} (hx : X₀ ≤ x) :
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

/-- **Lemma 3.4, absorbed part.** If every `a ∈ A` has `u_a + u_a^b = a`, `u_a ≥ X₀ ≥ 1`,
`0 < b ≤ 1`, and `ρ_A ≤ ε` on `[X₀, ∞)`, then for `x ≥ X₀`,
`|#(A ∩ [1, x]) - ∫_{X₀}^x ρ_A| ≤ ε x^b`. -/
theorem absorbed_target_error (h : AbsorbedWindowHyp b X₀ A u) {ε : ℝ}
    (hρ : ∀ v ≥ X₀, absorbedDensity b A u v ≤ ε) {x : ℝ} (hx : X₀ ≤ x) :
    |countA A x - ∫ v in X₀..x, absorbedDensity b A u v| ≤ ε * x ^ b := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hx0 : 0 < x := by linarith
  set S := below h.fin (2 * x)
  have hε : 0 ≤ ε := by
    refine le_trans ?_ (hρ X₀ le_rfl)
    rw [absorbedDensity_eq_sum h le_rfl hx]
    exact Finset.sum_nonneg fun a _ => absorbedBump_nonneg hX0 le_rfl
  have hint := fun a => intervalIntegrable_absorbedBump h a hx
  have hU : uIcc X₀ x = Icc X₀ x := uIcc_of_le hx
  -- the integral of the density is the sum of the integrals of the bumps
  have hρsum : ∫ v in X₀..x, absorbedDensity b A u v =
      ∑ a ∈ S, ∫ v in X₀..x, absorbedBump b A u a v := by
    rw [← intervalIntegral.integral_finset_sum fun a _ => hint a]
    apply intervalIntegral.integral_congr
    intro v hv; rw [hU] at hv
    exact absorbedDensity_eq_sum h hv.1 hv.2
  have hdiff : countA A x - ∫ v in X₀..x, absorbedDensity b A u v =
      ∑ a ∈ S, ((if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) -
        ∫ v in X₀..x, absorbedBump b A u a v) := by
    rw [hρsum, countA_eq_sum h hx, Finset.sum_sub_distrib]
  have hcont : ContinuousOn (fun v : ℝ => v ^ (b - 1)) (uIcc X₀ x) := by
    intro v hv; rw [hU] at hv
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  -- upper bound
  have hup : countA A x - ∫ v in X₀..x, absorbedDensity b A u v ≤ ε * x ^ b := by
    rw [hdiff]
    refine le_trans (Finset.sum_le_sum fun a _ => bump_upper h a hx) ?_
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum fun a _ =>
      (hint a).mul_continuousOn hcont]
    have hle : ∫ v in X₀..x, ∑ a ∈ S, absorbedBump b A u a v * v ^ (b - 1) ≤
        ∫ v in X₀..x, ε * v ^ (b - 1) := by
      apply intervalIntegral.integral_mono_on hx
      · have := IntervalIntegrable.sum S fun a _ => (hint a).mul_continuousOn hcont
        convert! this using 1; ext v; simp [Finset.sum_apply]
      · exact (hcont.intervalIntegrable).const_mul ε
      · intro v hv
        rw [← Finset.sum_mul, ← absorbedDensity_eq_sum h hv.1 hv.2]
        exact mul_le_mul_of_nonneg_right (hρ v hv.1)
          (Real.rpow_nonneg (by linarith [hv.1]) _)
    have hcalc : ∫ v in X₀..x, ε * v ^ (b - 1) = ε * ((x ^ b - X₀ ^ b) / b) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith [h.b_pos]))]
      simp
    have hb := h.b_pos
    calc b * ∫ v in X₀..x, ∑ a ∈ S, absorbedBump b A u a v * v ^ (b - 1)
        ≤ b * (ε * ((x ^ b - X₀ ^ b) / b)) := by
          rw [← hcalc]; exact mul_le_mul_of_nonneg_left hle hb.le
      _ = ε * (x ^ b - X₀ ^ b) := by field_simp
      _ ≤ ε * x ^ b := by
          have := Real.rpow_nonneg hX0.le b
          nlinarith
  -- lower bound
  have hlo : -(ε * x ^ b) ≤ countA A x - ∫ v in X₀..x, absorbedDensity b A u v := by
    rw [hdiff]
    refine le_trans ?_ (Finset.sum_le_sum fun a _ => bump_lower h a hx)
    rw [Finset.sum_neg_distrib, neg_le_neg_iff,
      ← intervalIntegral.integral_finset_sum fun a _ => ?_]
    · have hcongr : ∫ v in X₀..x, ∑ a ∈ S, (Ioi (x - x ^ b)).indicator (absorbedBump b A u a) v =
          ∫ v in X₀..x, (Ioi (x - x ^ b)).indicator (absorbedDensity b A u) v := by
        apply intervalIntegral.integral_congr
        intro v hv; rw [hU] at hv
        simp only [Set.indicator_apply]
        split_ifs
        · exact (absorbedDensity_eq_sum h hv.1 hv.2).symm
        · simp
      rw [hcongr]
      apply integral_window_le hx (Real.rpow_nonneg hx0.le _) hε
      · refine (IntervalIntegrable.sum S fun a _ => hint a).congr ?_
        intro v hv
        rw [uIoc_of_le hx] at hv
        simp only [Finset.sum_apply]
        exact (absorbedDensity_eq_sum h hv.1.le hv.2).symm
      · intro v hv; exact hρ v hv.1
    · have ha := hint a
      rw [intervalIntegrable_iff] at ha ⊢
      exact ha.indicator measurableSet_Ioi
  exact abs_le.mpr ⟨hlo, hup⟩

/-- **Lemma 3.4, absorbed part, for the capped density of the target.** With the density bound
`ρ_A(v) ≤ (log v)^{-4}` of Lemma 6.27(a) on `[X₀, ∞)` and `log X₀ ≥ 3`, the cap does not bind and
`|#(A ∩ [1, x]) - ∫_{X₀}^x ρ̄_A| ≤ (log X₀)^{-4} x^b ≤ 2 x^b` for `x ≥ X₀`. -/
theorem absorbed_target_error_cap (h : AbsorbedWindowHyp b X₀ A u)
    (hlog : 3 ≤ Real.log X₀)
    (hρ : ∀ v ≥ X₀, absorbedDensity b A u v ≤ (Real.log v) ^ (-4 : ℤ)) {x : ℝ} (hx : X₀ ≤ x) :
    |countA A x - ∫ v in X₀..x, absorbedDensityCap b A u v| ≤ 2 * x ^ b := by
  have hX0 : 0 < X₀ := by linarith [h.X₀_ge]
  have hlogv : ∀ v ≥ X₀, Real.log X₀ ≤ Real.log v := fun v hv => Real.log_le_log hX0 hv
  have hcap : ∀ v ≥ X₀, absorbedDensityCap b A u v = absorbedDensity b A u v := by
    intro v hv
    have hl : 3 ≤ Real.log v := hlog.trans (hlogv v hv)
    apply min_eq_left
    refine (hρ v hv).trans ?_
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    have hl0 : 0 < Real.log v := by linarith
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : 0.1 / Real.log v * Real.log v ^ 4 = 0.1 * Real.log v ^ 3 := by
      field_simp
    rw [this]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hl 3]
  have hint : ∫ v in X₀..x, absorbedDensityCap b A u v =
      ∫ v in X₀..x, absorbedDensity b A u v := by
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le hx] at hv
    exact hcap v hv.1
  rw [hint]
  have hL0 : 0 < Real.log X₀ := by linarith
  have hε : (Real.log X₀) ^ (-4 : ℤ) ≤ 2 := by
    rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    have : 1 ≤ Real.log X₀ ^ 4 := one_le_pow₀ (by linarith)
    calc (Real.log X₀ ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      _ ≤ 2 := by norm_num
  refine le_trans (absorbed_target_error h (ε := (Real.log X₀) ^ (-4 : ℤ)) ?_ hx) ?_
  · intro v hv
    refine (hρ v hv).trans ?_
    rw [zpow_neg, zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hL0.le (hlogv v hv) 4)
  · exact mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg (by linarith) _)

end Absorbed

end
