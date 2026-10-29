module

public import RequestProject.Beurling.LocalPNT.HBS

/-!
# Step 1 of the proof of Theorem 5.24: the extension `ζ^♯`

`ζ^♯ = Z_B + R̂ + D̂^♯` is the transform of `N^♯ = N` on `[1, y]`,
`N^♯(u) = N(y) + T₀(u) - T₀(y)` for `u > y`. For `σ > 1`,

  `ζ^♯(s) = ∑_{n ∈ 𝒩, n ≤ y} n^{-s} + s ∫_y^∞ (T₀(x) - T₀(y)) x^{-s-1} dx`

(`zetaSharp_eq`), and `ζ^♯` is holomorphic on `σ > θ`, `s ≠ 1` (`differentiableAt_zetaSharp`),
with `|D̂^♯(s)| ≤ |s| X₀⁻^{θ'-σ}/(σ-θ') + y^{θ'-σ}` for `σ > θ'` (`norm_earlyNoise_le`).
-/

@[expose] public section

open Set Real MeasureTheory Complex Oscillation DesignedZero BaseFactor Decomp Remark12
  Construction

namespace LocalPNT

/-! ## Abel summation over the elements `≤ y` -/

lemma integral_Ioc_cpow_neg {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y) {s : ℂ} (hs : s ≠ 0) :
    s * ∫ x in Ioc v y, (x : ℂ) ^ (-s - 1) = (v : ℂ) ^ (-s) - (y : ℂ) ^ (-s) := by
  rw [← intervalIntegral.integral_of_le hvy]
  rw [integral_cpow (Or.inr ⟨by
      intro h; apply hs; linear_combination -h, by
      rw [Set.uIcc_of_le hvy]; intro h; exact absurd h.1 (not_le.mpr hv)⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e]
  field_simp
  ring

lemma abel_elems (P : BeurlingSystem) {y : ℝ} {s : ℂ} (hs : s ≠ 0) :
    s * (∫ x in Ioc 1 y, (P.N x : ℂ) * (x : ℂ) ^ (-s - 1)) + (P.N y : ℂ) * (y : ℂ) ^ (-s) =
      ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s) := by
  classical
  have hN : ∀ x ∈ Ioc (1 : ℝ) y, (P.N x : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∑ e ∈ P.elems y, (Ici (P.val e)).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    rw [BeurlingSystem.N_eq_card]
    have : P.elems x = (P.elems y).filter (fun e => P.val e ≤ x) := by
      ext e; simp only [BeurlingSystem.mem_elems, Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.trans hx.2, h⟩
      · intro h; exact h.2
    rw [this, Finset.sum_indicator_eq_sum_filter, Finset.card_eq_sum_ones]
    · push_cast
      rw [Finset.sum_mul, one_mul]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext e; simp [Finset.mem_filter]
  rw [setIntegral_congr_fun measurableSet_Ioc hN]
  have hint : ∀ e ∈ P.elems y, IntegrableOn
      (fun x => (Ici (P.val e)).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) x) (Ioc 1 y) := by
    intro e _
    refine IntegrableOn.indicator ?_ measurableSet_Ici
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_ofReal_cpow_const
    right; exact_mod_cast (show x ≠ 0 by linarith [hx.1])
  rw [integral_finset_sum _ hint, Finset.mul_sum]
  have hterm : ∀ e ∈ P.elems y, s * ∫ x in Ioc 1 y,
      (Ici (P.val e)).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) x =
        ((P.val e : ℝ) : ℂ) ^ (-s) - (y : ℂ) ^ (-s) := by
    intro e he
    have hv1 := P.one_le_val e
    have hvy : P.val e ≤ y := (BeurlingSystem.mem_elems P).mp he
    rw [setIntegral_indicator measurableSet_Ici]
    have hset : (Ioc 1 y ∩ Ici (P.val e) : Set ℝ) =ᵐ[volume] (Ioc (P.val e) y : Set ℝ) := by
      rcases hv1.lt_or_eq with h1 | h1
      · have : Ioc 1 y ∩ Ici (P.val e) = Icc (P.val e) y := by
          ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
        rw [this]; exact Ioc_ae_eq_Icc.symm
      · rw [← h1]
        have : Ioc 1 y ∩ Ici (1 : ℝ) = Ioc 1 y := by
          ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici]
          constructor
          · rintro ⟨h, _⟩; exact h
          · intro h; exact ⟨h, h.1.le⟩
        rw [this]
    rw [setIntegral_congr_set hset]
    exact integral_Ioc_cpow_neg (by linarith) hvy hs
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, BeurlingSystem.N_eq_card]
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring


/-! ## Holomorphy of `R̂ = ∑_k R̂_k` -/

lemma locallyIntegrable_indicator_Ioi {E : ℝ → ℝ} (hE : Measurable E) {C γ : ℝ} (hγ : 0 ≤ γ)
    (hb : ∀ x, 1 < x → |E x| ≤ C * x ^ γ) : LocallyIntegrable ((Ioi (1 : ℝ)).indicator E) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hC : ∀ x, 1 < x → 0 ≤ C * x ^ γ := fun x hx => (abs_nonneg _).trans (hb x hx)
  refine Measure.integrableOn_of_bounded (M := |C| * (max R 1) ^ γ) hK.measure_lt_top.ne
    ((hE.indicator measurableSet_Ioi).aestronglyMeasurable) ?_
  refine (ae_restrict_mem hK.measurableSet).mono fun x hx => ?_
  rw [Real.norm_eq_abs]
  by_cases h1 : x ∈ Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem h1]
    have hx1 : 1 < x := h1
    have hxR : x ≤ max R 1 := by
      have := hR hx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact (le_abs_self x).trans (this.trans (le_max_left _ _))
    calc |E x| ≤ C * x ^ γ := hb x hx1
      _ ≤ |C| * x ^ γ := mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg (by linarith) _)
      _ ≤ |C| * (max R 1) ^ γ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) hxR hγ) (abs_nonneg _)
  · rw [Set.indicator_of_notMem h1, abs_zero]; positivity

lemma tailMellin_indicator_Ioi (E : ℝ → ℝ) (s : ℂ) :
    tailMellin ((Ioi (1 : ℝ)).indicator E) s = tailMellin E s := by
  unfold tailMellin
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [Set.indicator_of_mem hx]

lemma differentiableOn_oscHat {θ α γ xk : ℝ} (hθ : 0 ≤ θ) :
    DifferentiableOn ℂ (oscHat θ α γ xk) {s : ℂ | θ < s.re} := by
  have hb : ∀ x, 1 < x → |oscTerm θ α γ xk x| ≤ |α| * x ^ θ := by
    intro x hx
    have := Decomp.abs_oscTerm_le (θ := θ) (α := α) (γ := γ) (xp := xk) (by linarith : 0 < x)
    split_ifs at this
    · exact this
    · exact this.trans (by positivity)
  have hL := locallyIntegrable_indicator_Ioi (Decomp.measurable_oscTerm θ α γ xk) hθ hb
  have hb' : ∀ x ≥ (1 : ℝ), |(Ioi (1 : ℝ)).indicator (oscTerm θ α γ xk) x| ≤ |α| * x ^ θ := by
    intro x hx
    by_cases h1 : x ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem h1]; exact hb x h1
    · rw [Set.indicator_of_notMem h1, abs_zero]
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hd := tailMellin_differentiableOn hL hb'
  have e : oscHat θ α γ xk = fun s => s * tailMellin ((Ioi (1 : ℝ)).indicator
      (oscTerm θ α γ xk)) s := by
    funext s; rw [tailMellin_indicator_Ioi]; rfl
  rw [e]
  exact differentiableOn_id.mul hd

/-- `R̂ = ∑_k R̂_k` is holomorphic on `σ > θ + 2/5`. -/
lemma differentiableOn_oscHatSum {θ : ℝ} (hθ : 0 ≤ θ) {α γ xp : ℕ → ℝ}
    (hα : ∀ k, |α k| ≤ 2) (hX : ∀ k, (2 : ℝ) ^ k ≤ xp k) :
    DifferentiableOn ℂ (oscHatSum θ α γ xp) {s : ℂ | θ + 2 / 5 < s.re} := by
  intro s0 hs0
  set U : Set ℂ := {s : ℂ | θ + 2 / 5 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨hs0, by simp⟩
  set q : ℝ := (2 : ℝ) ^ (-(2 / 5 : ℝ))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum : Summable (fun k : ℕ => 5 * (‖s0‖ + 1) * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hd : DifferentiableOn ℂ (fun w => ∑' k, oscHat θ (α k) (γ k) (xp k) w) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun k => ?_) hU ?_
    · exact (differentiableOn_oscHat hθ).mono fun w hw => by
        have : θ + 2 / 5 < w.re := hw.1
        show θ < w.re; linarith
    · intro k w hw
      have hxk : 1 ≤ xp k := le_trans (one_le_pow₀ (by norm_num)) (hX k)
      have h1 := norm_oscHat_le_of_re (θ := θ) (γ := γ k) hxk (hα k) hw.1.le
      have hw' : ‖w‖ ≤ ‖s0‖ + 1 := by
        have := hw.2; rw [Metric.mem_ball, dist_zero_right] at this; exact this.le
      have h2 : xp k ^ (-(2 / 5 : ℝ)) ≤ q ^ k := by
        have h3 : xp k ^ (-(2 / 5 : ℝ)) ≤ ((2 : ℝ) ^ k) ^ (-(2 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (hX k) (by norm_num)
        refine h3.trans (le_of_eq ?_)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), mul_comm]
      calc ‖oscHat θ (α k) (γ k) (xp k) w‖ ≤ 5 * ‖w‖ * xp k ^ (-(2 / 5 : ℝ)) := h1
        _ ≤ 5 * (‖s0‖ + 1) * q ^ k := by gcongr
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

/-! ## The lag `D = N - T₀` on `[1, y]` -/

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma T0_X0 : T0 θ X₀ α γ xp X₀ = X₀ := by
  rw [h.T0_high le_rfl]
  simp [Target.rigidErr, h.osc_X0]

/-- `T₀` is non-decreasing on `ℝ`. -/
lemma T0_monotone : Monotone (T0 θ X₀ α γ xp) := by
  intro a b hab
  rcases lt_or_ge b X₀ with hb | hb
  · rw [LPHyp.T0_low (lt_of_le_of_lt hab hb), LPHyp.T0_low hb]
    exact_mod_cast Nat.floor_mono hab
  rcases lt_or_ge a X₀ with ha | ha
  · rw [LPHyp.T0_low ha]
    have h1 := h.T0_mono (self_mem_Ici) hb hb
    rw [h.T0_X0] at h1
    have : (⌊a⌋₊ : ℝ) ≤ X₀ := by
      rcases le_or_gt 0 a with ha0 | ha0
      · exact (Nat.floor_le ha0).trans ha.le
      · rw [Nat.floor_of_nonpos ha0.le]; simp
    linarith
  · exact h.T0_mono ha hb hab

lemma lag0_low {u : ℝ} (hu : u < Xm) : lag0 P θ X₀ α γ xp u = 0 := by
  simp [lag0, h.lpa_low u hu]

lemma measurable_lag0 : Measurable (lag0 P θ X₀ α γ xp) :=
  (BeurlingSystem.N_mono P).measurable.sub h.T0_monotone.measurable

/-- `|D(u)| ≤ u^{θ'}` on `[X₀⁻, y]`, `D = 0` below `X₀⁻`. -/
lemma abs_lag0_le {u : ℝ} (hu : u ≤ y) :
    |lag0 P θ X₀ α γ xp u| ≤ (Ici Xm).indicator (fun x => x ^ thetaPrime θ X₀) u := by
  rcases lt_or_ge u Xm with h1 | h1
  · rw [h.lag0_low h1, Set.indicator_of_notMem (by simpa using h1)]; simp
  · rw [Set.indicator_of_mem (by simpa using h1)]; exact h.lag_le h1 hu

lemma abs_lag0_le_const {u : ℝ} (hu1 : 1 ≤ u) (hu : u ≤ y) :
    |lag0 P θ X₀ α γ xp u| ≤ y ^ thetaPrime θ X₀ := by
  refine (h.abs_lag0_le hu).trans ?_
  have htp := (thetaPrime_bounds h.theta_mem h.logX).1
  by_cases hm : u ∈ Ici Xm
  · rw [Set.indicator_of_mem hm]
    exact Real.rpow_le_rpow (by linarith) hu (by linarith [h.theta_mem.1])
  · rw [Set.indicator_of_notMem hm]
    exact Real.rpow_nonneg (by linarith [h.y_ge, h.X0_pos]) _

lemma integrableOn_lag0 : IntegrableOn (lag0 P θ X₀ α γ xp) (Ioc 1 y) := by
  refine Measure.integrableOn_of_bounded (M := y ^ thetaPrime θ X₀) measure_Ioc_lt_top.ne
    h.measurable_lag0.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun u hu => ?_
  rw [Real.norm_eq_abs]; exact h.abs_lag0_le_const hu.1.le hu.2

/-- `D̂^♯` is entire. -/
lemma differentiable_earlyNoise : Differentiable ℂ (earlyNoise (lag0 P θ X₀ α γ xp) y) :=
  differentiable_earlyNoise_of_integrableOn (by linarith [h.y_ge, h.one_le_X0])
    h.integrableOn_lag0 (fun u hu => h.abs_lag0_le_const hu.1.le hu.2)

/-- **Step 1**: `|D̂^♯(s)| ≤ |s| X₀⁻^{θ'-σ}/(σ-θ') + y^{θ'-σ}` for `σ > θ'`. -/
lemma norm_earlyNoise_le {s : ℂ} (hs : thetaPrime θ X₀ < s.re) :
    ‖earlyNoise (lag0 P θ X₀ α γ xp) y s‖ ≤
      ‖s‖ * Xm ^ (thetaPrime θ X₀ - s.re) / (s.re - thetaPrime θ X₀) +
        y ^ (thetaPrime θ X₀ - s.re) := by
  set θ' := thetaPrime θ X₀
  have hXm0 := h.Xm_pos
  have hy0 : 0 < y := by linarith [h.y_ge, h.X0_pos]
  have hy1 : 1 ≤ y := by linarith [h.y_ge, h.one_le_X0]
  unfold earlyNoise
  have hlt : θ' - s.re - 1 < -1 := by linarith
  have hgi : IntegrableOn (fun x : ℝ => x ^ (θ' - s.re - 1)) (Ioi Xm) :=
    integrableOn_Ioi_rpow_of_lt hlt hXm0
  have hgiI : IntegrableOn (fun x : ℝ => x ^ (θ' - s.re - 1)) (Ici Xm) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hgi
  have hI : ‖∫ x in Ioc 1 y, (lag0 P θ X₀ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤
      Xm ^ (θ' - s.re) / (s.re - θ') := by
    have hval : ∫ x in Ioi Xm, x ^ (θ' - s.re - 1) = Xm ^ (θ' - s.re) / (s.re - θ') := by
      rw [integral_Ioi_rpow_of_lt hlt hXm0]
      have : θ' - s.re - 1 + 1 = θ' - s.re := by ring
      rw [this, neg_div, ← div_neg, neg_sub]
    rw [← hval]
    calc ‖∫ x in Ioc 1 y, (lag0 P θ X₀ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1)‖
        ≤ ∫ x in Ioc 1 y, (Ici Xm).indicator (fun x => x ^ (θ' - s.re - 1)) x := by
          refine norm_integral_le_of_norm_le ?_ ?_
          · exact ((integrable_indicator_iff measurableSet_Ici).mpr hgiI).integrableOn
          · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
            have hx0 : 0 < x := by linarith [hx.1]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_cpow_eq_rpow_re_of_pos hx0]
            have hb := h.abs_lag0_le hx.2
            by_cases hm : x ∈ Ici Xm
            · rw [Set.indicator_of_mem hm] at hb ⊢
              have e : x ^ (θ' - s.re - 1) = x ^ θ' * x ^ ((-s - 1).re) := by
                rw [← Real.rpow_add hx0]; congr 1; simp; ring
              rw [e]
              exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx0.le _)
            · rw [Set.indicator_of_notMem hm] at hb ⊢
              have : |lag0 P θ X₀ α γ xp x| = 0 := le_antisymm hb (abs_nonneg _)
              rw [this, zero_mul]
      _ ≤ ∫ x in Ioi 1, (Ici Xm).indicator (fun x => x ^ (θ' - s.re - 1)) x := by
          refine setIntegral_mono_set ?_ ?_ (Ioc_subset_Ioi_self).eventuallyLE
          · exact ((integrable_indicator_iff measurableSet_Ici).mpr hgiI).integrableOn
          · exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
              by_cases hm : x ∈ Ici Xm
              · rw [Set.indicator_of_mem hm]
                exact Real.rpow_nonneg (by linarith [hx.out]) _
              · rw [Set.indicator_of_notMem hm]; rfl
      _ = ∫ x in Ioi Xm, x ^ (θ' - s.re - 1) := by
          rw [setIntegral_indicator measurableSet_Ici]
          have : Ioi (1 : ℝ) ∩ Ici Xm = Ici Xm := by
            ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
            constructor
            · exact fun h => h.2
            · intro hx; exact ⟨by linarith [h.Xm_ge_e7], hx⟩
          rw [this, integral_Ici_eq_integral_Ioi]
  have hD : ‖(lag0 P θ X₀ α γ xp y : ℂ) * (y : ℂ) ^ (-s)‖ ≤ y ^ (θ' - s.re) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      Complex.neg_re, sub_eq_add_neg, Real.rpow_add hy0]
    have hb := h.abs_lag0_le (le_refl y)
    have hb' : |lag0 P θ X₀ α γ xp y| ≤ y ^ θ' := by
      by_cases hm : y ∈ Ici Xm
      · rwa [Set.indicator_of_mem hm] at hb
      · rw [Set.indicator_of_notMem hm] at hb; exact hb.trans (Real.rpow_nonneg hy0.le _)
    exact mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hy0.le _)
  calc _ ≤ ‖s * ∫ x in Ioc 1 y, (lag0 P θ X₀ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1)‖ +
        ‖(lag0 P θ X₀ α γ xp y : ℂ) * (y : ℂ) ^ (-s)‖ := norm_add_le _ _
    _ ≤ ‖s‖ * (Xm ^ (θ' - s.re) / (s.re - θ')) + y ^ (θ' - s.re) := by
        rw [norm_mul]; gcongr
    _ = _ := by ring

omit h in
/-- `T₀ = (T_base - x) + x + R`. -/
lemma T0_eq_baseErr (hsp : Spacing xp) (hxp : (X₀ : ℝ) ≤ xp 0) (hX1 : 1 ≤ X₀) {x : ℝ}
    (hx : 0 < x) :
    T0 θ X₀ α γ xp x = baseErr X₀ (kap X₀) x + x + osc θ α γ xp x := by
  have hR0 : osc θ α γ xp X₀ = 0 :=
    Target.osc_eq_zero_of_le hsp (by exact_mod_cast hX1) hxp
  unfold T0 Target.target baseErr
  by_cases hlt : x < X₀
  · rw [if_pos hlt, if_pos hlt, Target.osc_eq_zero_of_le hsp hx (hlt.le.trans hxp)]; ring
  · rw [if_neg hlt, if_neg hlt, hR0]
    simp only [intervalIntegral.integral_zero, Target.rigidErr]
    ring

lemma smooth_X0 : X₀ ∈ X₀.smoothNumbers := by
  have h4 : 4 ≤ X₀ := by
    have : (4 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀)
      rw [Real.exp_log h.X0_pos] at this; linarith [h.logX]
    exact_mod_cast this
  exact even_mem_smoothNumbers h.even h4

/-- **Step 1, the identity**: for `σ > 1`,
`ζ^♯(s) = ∑_{n ≤ y} n^{-s} + s ∫_y^∞ (T₀(x) - T₀(y)) x^{-s-1} dx`. -/
theorem zetaSharp_eq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y : ℝ) : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi y) ∧
    zetaSharp P θ X₀ α γ xp y s = (∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)) +
      s * ∫ x in Ioi y, ((T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  set T := T0 θ X₀ α γ xp with hT
  set D := lag0 P θ X₀ α γ xp with hD
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro e; rw [e] at hs; simp at hs
  have hsne : s ≠ 0 := by intro e; rw [e] at hs; simp at hs; linarith
  have hy1 : 1 ≤ y := by linarith [h.y_ge, h.one_le_X0]
  have hy0 : 0 < y := by linarith
  have hX1 : 1 ≤ X₀ := by exact_mod_cast h.one_le_X0
  have hκ : 0 < kap X₀ := kappa_pos_aux h.logX
  obtain ⟨hiB, heB⟩ := mellin_baseErr h.smooth_X0 hκ hs0 hs1
  obtain ⟨hiR, heR⟩ := mellin_osc (θ := θ) (γ := γ) h.spacing (C := 2) h.alpha_le
    (show θ < s.re by linarith [h.theta_mem.2])
  have hlt : (-s).re < -1 := by simp; linarith
  have hiX : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hlt one_pos
  have hXval : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hlt one_pos]
    have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [Complex.ofReal_one, Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div,
      neg_neg]
  have hxeq : ∀ x ∈ Ioi (1 : ℝ), ((x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith [hx.out])
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  have hiX' : IntegrableOn (fun x : ℝ => ((x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    hiX.congr_fun (fun x hx => (hxeq x hx).symm) measurableSet_Ioi
  -- `T₀ x^{-s-1}` is integrable on `(1, ∞)`
  have hTsplit : ∀ x ∈ Ioi (1 : ℝ), ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      ((baseErr X₀ (kap X₀) x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((osc θ α γ xp x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    rw [hT, T0_eq_baseErr h.spacing h.X0_le_xp hX1 (by linarith [hx.out])]
    push_cast; ring
  have hiBX : IntegrableOn (fun x : ℝ => ((baseErr X₀ (kap X₀) x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
      ((x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := hiB.add hiX'
  have hiBXR : IntegrableOn (fun x : ℝ =>
      ((baseErr X₀ (kap X₀) x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((osc θ α γ xp x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := hiBX.add hiR
  have hiT : IntegrableOn (fun x : ℝ => ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    IntegrableOn.congr_fun hiBXR (fun x hx => (hTsplit x hx).symm) measurableSet_Ioi
  have hIT : s * ∫ x in Ioi (1 : ℝ), ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      ZBcont X₀ (kap X₀) s + oscHatSum θ α γ xp s := by
    rw [setIntegral_congr_fun measurableSet_Ioi hTsplit, integral_add hiBX hiR,
      integral_add hiB hiX', setIntegral_congr_fun measurableSet_Ioi hxeq, hXval]
    unfold tailMellin at heB heR
    unfold oscHatSum
    rw [← heR]
    have : s * (1 / (s - 1)) = s / (s - 1) := by ring
    linear_combination heB
  -- splitting `(1, ∞) = (1, y] ∪ (y, ∞)`
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hiT.mono_set Ioc_subset_Ioi_self) (hiT.mono_set (Ioi_subset_Ioi hy1))
  rw [Ioc_union_Ioi_eq_Ioi hy1] at hsplit
  -- the tail
  have hiY : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi y) := by
    have : (-s - 1).re < -1 := by simp; linarith
    exact integrableOn_Ioi_cpow_of_lt this hy0
  have hYval : s * ∫ x in Ioi y, (x : ℂ) ^ (-s - 1) = (y : ℂ) ^ (-s) := by
    have : (-s - 1).re < -1 := by simp; linarith
    rw [integral_Ioi_cpow_of_lt this hy0]
    have e : -s - 1 + 1 = -s := by ring
    rw [e]; field_simp
  have hiTy : IntegrableOn (fun x : ℝ => ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi y) := by
    have : IntegrableOn (fun x : ℝ => ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) -
        ((T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi y) :=
      (hiT.mono_set (Ioi_subset_Ioi hy1)).sub (hiY.const_mul ((T y : ℝ) : ℂ))
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    push_cast; ring
  refine ⟨hiTy, ?_⟩
  have hTy : s * ∫ x in Ioi y, ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      s * (∫ x in Ioi y, ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
        ((T y : ℝ) : ℂ) * (y : ℂ) ^ (-s) := by
    rw [← hYval]
    have e : ∫ x in Ioi y, ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
        (∫ x in Ioi y, ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
          ((T y : ℝ) : ℂ) * ∫ x in Ioi y, (x : ℂ) ^ (-s - 1) := by
      rw [← integral_const_mul, ← integral_add hiTy (hiY.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      push_cast; ring
    rw [e]; ring
  -- the early part
  have hiN : IntegrableOn (fun x : ℝ => ((P.N x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 y) := by
    have hiD : IntegrableOn (fun x : ℝ => ((D x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 y) := by
      refine Measure.integrableOn_of_bounded (M := y ^ thetaPrime θ X₀ * 1)
        measure_Ioc_lt_top.ne ?_ ?_
      · exact ((Complex.measurable_ofReal.comp h.measurable_lag0).mul
          (by fun_prop : Measurable fun x : ℝ => (x : ℂ) ^ (-s - 1))).aestronglyMeasurable
      · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
        have hx0 : 0 < x := by linarith [hx.1]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        refine mul_le_mul (h.abs_lag0_le_const hx.1.le hx.2) ?_ (by positivity)
          (Real.rpow_nonneg (by linarith [h.y_ge, h.X0_pos]) _)
        exact Real.rpow_le_one_of_one_le_of_nonpos hx.1.le (by simp; linarith)
    have : IntegrableOn (fun x : ℝ => ((D x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 y) :=
      hiD.add (hiT.mono_set Ioc_subset_Ioi_self)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioc
    simp only [hD, lag0]; push_cast; ring
  have hED : earlyNoise D y s = s * (∫ x in Ioc 1 y, ((P.N x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
      s * (∫ x in Ioc 1 y, ((T x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
        (((P.N y - T y : ℝ)) : ℂ) * (y : ℂ) ^ (-s) := by
    unfold earlyNoise
    rw [← mul_sub, ← integral_sub hiN (hiT.mono_set Ioc_subset_Ioi_self)]
    congr 2
    · refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      simp only [hD, lag0]; push_cast; ring
  have hab := abel_elems P (y := y) hsne
  unfold zetaSharp
  rw [← hIT, hsplit, mul_add, hED, hTy, ← hab]
  push_cast
  ring

/-- `ζ^♯` is holomorphic on `σ > θ + 2/5`, `s ≠ 1`. -/
theorem differentiableAt_zetaSharp {s : ℂ} (hs : θ + 2 / 5 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (zetaSharp P θ X₀ α γ xp y) s := by
  have hθ0 : 0 ≤ θ := by linarith [h.theta_mem.1]
  have hO : IsOpen {s : ℂ | θ + 2 / 5 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 := differentiableAt_ZBcont X₀ (kappa_pos_aux h.logX) (by linarith) hs1
  have h2 := (differentiableOn_oscHatSum (γ := γ) hθ0 h.alpha_le
    (Decomp.Spacing.two_pow_le h.spacing)).differentiableAt (hO.mem_nhds hs)
  have h3 := h.differentiable_earlyNoise s
  exact (h1.add h2).add h3

end LPHyp

end LocalPNT

end
