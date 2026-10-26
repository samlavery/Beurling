module

public import Mathlib

/-!
# Lemma 4.8 (Good heights exist)

For an entire function `f`:

* `sq_norm_le_circle` : `2π |f(c)|² ≤ ∫_{-π}^{π} |f(c + ρ e^{iθ})|² dθ` (mean value property of
  `f²`);
* `sq_norm_le_ball` : `π r² |f(c)|² ≤ ∬_{|z-c|<r} |f|²` (subharmonicity of `|f|²`);
* `measure_bad_le` : the "Reduction" step of the proof of Lemma 4.8(ii): the set of
  `γ ∈ [Γ, 2Γ]` at which `|f| > 1/16` somewhere on `|s - (1+iγ)| ≤ 1/8` has measure at most
  `(8192/π) ∬_Q |f|²`, `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`;
* `lemma_4_8`, `lemma_4_8_exists` : the conclusion of Lemma 4.8 (`S_k` has measure `≥ 0.018 Γ`,
  so a good height exists) from the two analytic inputs of its proof: the density bound for (i)
  and the norm bound `‖D̂_{<a_k}‖ ≤ 12 X₀^{-3/16}` for (ii). These two inputs rest on the mean value
  theorem (19) of Montgomery and Vaughan, which is not in Mathlib.
-/

@[expose] public section

open Complex Metric Set MeasureTheory Real

namespace GoodHeights

/-- The mean value property of `f²`: `2π |f(c)|² ≤ ∫_{-π}^{π} |f(c + ρ e^{iθ})|² dθ`. -/
lemma sq_norm_le_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (ρ : ℝ) :
    2 * π * ‖f c‖ ^ 2 ≤
      ∫ θ in (-π)..π, ‖f (c + ρ * (Real.cos θ + Real.sin θ * I))‖ ^ 2 := by
  set g : ℂ → ℂ := fun z => f z ^ 2
  have hg : Differentiable ℂ g := hf.pow 2
  have hmv := (hg.diffContOnCl (s := ball c |ρ|)).circleAverage
  rw [circleAverage_eq_integral_add (-π)] at hmv
  have hshift : ∫ θ in (0:ℝ)..2 * π, g (circleMap c ρ (θ + -π)) =
      ∫ θ in (-π)..π, g (c + ρ * (Real.cos θ + Real.sin θ * I)) := by
    rw [intervalIntegral.integral_comp_add_right (fun θ => g (circleMap c ρ θ))]
    rw [show (0:ℝ) + -π = -π by ring, show 2 * π + -π = π by ring]
    congr 1; funext θ; simp only [circleMap]; congr 2
    rw [Complex.exp_mul_I]; push_cast; ring
  rw [hshift] at hmv
  have h1 : ‖f c‖ ^ 2 = ‖g c‖ := by simp [g, norm_pow]
  rw [h1, ← hmv, norm_smul]
  have h2 := intervalIntegral.norm_integral_le_integral_norm (f := fun θ : ℝ =>
    g (c + ρ * (Real.cos θ + Real.sin θ * I))) (μ := volume) (a := -π) (b := π)
    (by linarith [Real.pi_pos])
  have h3 : ∀ θ : ℝ, ‖g (c + ρ * (Real.cos θ + Real.sin θ * I))‖ =
      ‖f (c + ρ * (Real.cos θ + Real.sin θ * I))‖ ^ 2 := fun θ => by simp [g, norm_pow]
  simp_rw [h3] at h2
  rw [norm_inv, Real.norm_of_nonneg (by positivity)]
  have hpi := Real.pi_pos
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  exact h2

/-- Subharmonicity of `|f|²`: `π r² |f(c)|² ≤ ∬_{|z-c|<r} |f|²`. -/
lemma sq_norm_le_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (π * r ^ 2 * ‖f c‖ ^ 2) ≤
      ∫⁻ z in ball c r, ENNReal.ofReal (‖f z‖ ^ 2) := by
  set F : ℂ → ENNReal := fun z => ENNReal.ofReal (‖f z‖ ^ 2)
  have htrans : ∫⁻ z in ball c r, F z =
      ∫⁻ z, (ball (0:ℂ) r).indicator (fun z => F (c + z)) z := by
    rw [← lintegral_indicator measurableSet_ball]
    rw [← lintegral_add_left_eq_self (μ := volume) _ c]
    congr 1; funext z
    simp only [indicator, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [htrans, ← Complex.lintegral_comp_polarCoord_symm]
  have hsub : Ioo 0 r ×ˢ Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact prod_mono (fun x hx => hx.1) subset_rfl
  refine le_trans ?_ (lintegral_mono_set hsub)
  have hon : ∀ p ∈ Ioo 0 r ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • (ball (0:ℂ) r).indicator (fun z => F (c + z))
        (Complex.polarCoord.symm p) =
      ENNReal.ofReal (p.1 * ‖f (c + p.1 * (Real.cos p.2 + Real.sin p.2 * I))‖ ^ 2) := by
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    have hmem : Complex.polarCoord.symm (ρ, θ) ∈ ball (0:ℂ) r := by
      rw [mem_ball, dist_zero_right, norm_polarCoord_symm, abs_of_pos hρ.1]; exact hρ.2
    rw [indicator_of_mem hmem, Complex.polarCoord_symm_apply, smul_eq_mul,
      ← ENNReal.ofReal_mul hρ.1.le]
  rw [setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) hon]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul measurable_fst
    apply Measurable.pow_const
    apply continuous_norm.measurable.comp
    apply hf.continuous.measurable.comp
    fun_prop
  have hinner : ∀ ρ ∈ Ioo 0 r, ENNReal.ofReal (ρ * (2 * π * ‖f c‖ ^ 2)) ≤
      ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (ρ * ‖f (c + ρ * (Real.cos θ + Real.sin θ * I))‖ ^ 2) := by
    intro ρ hρ
    have hcont : Continuous fun θ : ℝ =>
        ρ * ‖f (c + ρ * (Real.cos θ + Real.sin θ * I))‖ ^ 2 := by
      apply Continuous.mul continuous_const
      apply Continuous.pow
      apply continuous_norm.comp
      apply hf.continuous.comp
      fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · apply ENNReal.ofReal_le_ofReal
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (sq_norm_le_circle hf c ρ) hρ.1.le
    · exact (hcont.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun θ => by
        have := hρ.1; positivity
  calc ENNReal.ofReal (π * r ^ 2 * ‖f c‖ ^ 2) =
      ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal (ρ * (2 * π * ‖f c‖ ^ 2)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
            intervalIntegral.integral_mul_const, integral_id]
          ring
        · exact (continuous_id.mul continuous_const).integrableOn_Icc.mono_set
            Ioo_subset_Icc_self
        · refine (ae_restrict_mem measurableSet_Ioo).mono fun ρ hρ => ?_
          have := hρ.1; simp only [Pi.zero_apply]; positivity
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hinner

/-- The box `[3/4, 5/4] × [a, b]` in the coordinates `(σ, t)`. -/
def box (a b : ℝ) : Set ℂ := {z | 3 / 4 ≤ z.re ∧ z.re ≤ 5 / 4 ∧ a ≤ z.im ∧ z.im ≤ b}

lemma measurableSet_box (a b : ℝ) : MeasurableSet (box a b) := by
  unfold box
  refine (measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_le Complex.measurable_re measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
    (measurableSet_le Complex.measurable_im measurable_const)))

/-- The disc `|z - s| ≤ 1/8` around a point `s` with `|s - (1 + iγ)| ≤ 1/8` lies in
`Q_γ = [3/4, 5/4] × [γ - 1/4, γ + 1/4]`. -/
lemma ball_subset_box {γ : ℝ} {s : ℂ} (hs : s ∈ closedBall (1 + γ * I) (1 / 8)) :
    ball s (1 / 8) ⊆ box (γ - 1 / 4) (γ + 1 / 4) := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hs
  rw [mem_ball, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (s - (1 + γ * I))
  have h2 := Complex.abs_im_le_norm (s - (1 + γ * I))
  have h3 := Complex.abs_re_le_norm (z - s)
  have h4 := Complex.abs_im_le_norm (z - s)
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.one_im, Complex.mul_im] at h1 h2 h3 h4
  norm_num at h1 h2
  have a1 := abs_le.mp (h1.trans hs); have a2 := abs_le.mp (h2.trans hs)
  have a3 := abs_le.mp (h3.trans hz.le); have a4 := abs_le.mp (h4.trans hz.le)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Lemma 4.8(ii), reduction step.** For an entire `f` and `Γ > 0`, let `B` be the set of
`γ ∈ [Γ, 2Γ]` at which `|f| > 1/16` somewhere on `|s - (1 + iγ)| ≤ 1/8`. Then
`(π/16384) · |B| ≤ (1/2) ∬_Q |f|²`, `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`; that is,
`|B| ≤ (8192/π) ∬_Q |f|²`. -/
theorem measure_bad_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (Γ : ℝ) :
    ENNReal.ofReal (π / 16384) *
      volume {γ ∈ Icc Γ (2 * Γ) | ∃ s ∈ closedBall (1 + γ * I) (1 / 8), 1 / 16 < ‖f s‖} ≤
      ENNReal.ofReal (1 / 2) *
        ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) := by
  set F : ℂ → ENNReal := fun z => ENNReal.ofReal (‖f z‖ ^ 2)
  have hFm : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    exact (continuous_norm.comp hf.continuous).measurable.pow_const _
  set K : ℝ → ℂ → ENNReal := fun γ z => (box (γ - 1 / 4) (γ + 1 / 4)).indicator F z
  have hKm : Measurable (Function.uncurry K) := by
    have hset : MeasurableSet {p : ℝ × ℂ | p.2 ∈ box (p.1 - 1 / 4) (p.1 + 1 / 4)} := by
      simp only [box, Set.mem_setOf_eq]
      refine (measurableSet_le measurable_const (Complex.measurable_re.comp measurable_snd)).inter
        ((measurableSet_le (Complex.measurable_re.comp measurable_snd) measurable_const).inter
        ((measurableSet_le (by fun_prop) (Complex.measurable_im.comp measurable_snd)).inter
        (measurableSet_le (Complex.measurable_im.comp measurable_snd) (by fun_prop))))
    have : Function.uncurry K =
        {p : ℝ × ℂ | p.2 ∈ box (p.1 - 1 / 4) (p.1 + 1 / 4)}.indicator (fun p => F p.2) := by
      funext ⟨γ, z⟩
      simp only [Function.uncurry_apply_pair, K, Set.indicator, Set.mem_setOf_eq]
    rw [this]
    exact (hFm.comp measurable_snd).indicator hset
  set G : ℝ → ENNReal := fun γ => ∫⁻ z, K γ z
  have hGm : Measurable G := hKm.lintegral_prod_right'
  set c : ENNReal := ENNReal.ofReal (π / 16384)
  -- step 1: on the bad set, `G γ ≥ c`
  have hbad : {γ ∈ Icc Γ (2 * Γ) | ∃ s ∈ closedBall (1 + γ * I) (1 / 8), 1 / 16 < ‖f s‖} ⊆
      {γ | c ≤ G γ} ∩ Icc Γ (2 * Γ) := by
    rintro γ ⟨hγ, s, hs, hfs⟩
    refine ⟨?_, hγ⟩
    have h1 := sq_norm_le_ball hf s (show (0:ℝ) < 1 / 8 by norm_num)
    have h2 : ∫⁻ z in ball s (1 / 8), F z ≤ G γ := by
      simp only [G, K]
      rw [lintegral_indicator (measurableSet_box _ _)]
      exact lintegral_mono_set (ball_subset_box hs)
    refine le_trans ?_ (h1.trans h2)
    apply ENNReal.ofReal_le_ofReal
    have : (1 / 16 : ℝ) ^ 2 ≤ ‖f s‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hfs.le 2
    have hpi := Real.pi_pos
    nlinarith
  -- step 2: Markov
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (Icc Γ (2 * Γ)))
    hGm.aemeasurable c
  have hB : volume {γ ∈ Icc Γ (2 * Γ) | ∃ s ∈ closedBall (1 + γ * I) (1 / 8), 1 / 16 < ‖f s‖} ≤
      (volume.restrict (Icc Γ (2 * Γ))) {γ | c ≤ G γ} :=
    (measure_mono hbad).trans (Measure.le_restrict_apply _ _)
  -- step 3: Tonelli
  have hswap : ∫⁻ γ in Icc Γ (2 * Γ), G γ = ∫⁻ z, ∫⁻ γ in Icc Γ (2 * Γ), K γ z := by
    simp only [G]
    exact lintegral_lintegral_swap (hKm.aemeasurable)
  have hinner : ∀ z, ∫⁻ γ in Icc Γ (2 * Γ), K γ z ≤
      ENNReal.ofReal (1 / 2) * (box (Γ - 1 / 4) (2 * Γ + 1 / 4)).indicator F z := by
    intro z
    by_cases hz : z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4)
    · rw [indicator_of_mem hz]
      have hle : ∀ γ, K γ z ≤ (Icc (z.im - 1 / 4) (z.im + 1 / 4)).indicator (fun _ => F z) γ := by
        intro γ
        simp only [K, Set.indicator]
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2; obtain ⟨_, _, h3, h4⟩ := h1; constructor <;> linarith
        · exact zero_le _
        · exact le_rfl
      calc ∫⁻ γ in Icc Γ (2 * Γ), K γ z ≤ ∫⁻ γ, K γ z := setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ γ, (Icc (z.im - 1 / 4) (z.im + 1 / 4)).indicator (fun _ => F z) γ :=
            lintegral_mono hle
        _ = ENNReal.ofReal (1 / 2) * F z := by
            rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
              mul_comm]
            congr 2; ring
    · rw [indicator_of_notMem hz, mul_zero]
      have : ∀ γ ∈ Icc Γ (2 * Γ), K γ z = 0 := by
        intro γ hγ
        simp only [K]
        rw [indicator_of_notMem]
        intro h; apply hz
        obtain ⟨h1, h2, h3, h4⟩ := h
        exact ⟨h1, h2, by linarith [hγ.1], by linarith [hγ.2]⟩
      rw [setLIntegral_congr_fun measurableSet_Icc this, lintegral_zero]
  calc c * volume {γ ∈ Icc Γ (2 * Γ) | ∃ s ∈ closedBall (1 + γ * I) (1 / 8), 1 / 16 < ‖f s‖}
      ≤ c * (volume.restrict (Icc Γ (2 * Γ))) {γ | c ≤ G γ} := by gcongr
    _ ≤ ∫⁻ γ in Icc Γ (2 * Γ), G γ := hmarkov
    _ = ∫⁻ z, ∫⁻ γ in Icc Γ (2 * Γ), K γ z := hswap
    _ ≤ ∫⁻ z, ENNReal.ofReal (1 / 2) * (box (Γ - 1 / 4) (2 * Γ + 1 / 4)).indicator F z :=
        lintegral_mono hinner
    _ = _ := by
        rw [lintegral_const_mul _ ((hFm.indicator (measurableSet_box _ _))),
          lintegral_indicator (measurableSet_box _ _)]

lemma exp_large : (3 * 10 ^ 7 : ℝ) ≤ Real.exp (50 * (3 / 8)) := by
  have h1 : Real.exp 18 ≤ Real.exp (50 * (3 / 8)) := Real.exp_le_exp.mpr (by norm_num)
  have h2 : (2.7182818283 : ℝ) ^ 18 ≤ Real.exp 18 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 18
  have h3 : (3 * 10 ^ 7 : ℝ) ≤ (2.7182818283 : ℝ) ^ 18 := by norm_num
  linarith

/-- **Lemma 4.8 (Good heights exist), from its two analytic inputs.** Let `f = D̂_{<a_k}` (an
entire function) and `Γ = Γ_k > 0`, and let `S_k` be the set of `γ ∈ [Γ, 2Γ]` with
(i) `|Z_B(1 + iγ)| ≥ 0.6` and (ii) `|f| ≤ 1/16` on `|s - (1 + iγ)| ≤ 1/8`. Suppose:

* (i) fails on a set of measure at most `0.964 Γ` (the paper shows `|Z_∞(1+it)| ≥ 2^{-1/2}` on a
  set of density `≥ 0.036`, by Paley–Zygmund and the mean value theorem (19));
* `∬_Q |f|² ≤ 144 X₀^{-3/8} Γ`, i.e. `‖f‖ ≤ 12 X₀^{-3/16}` (the norm bound of the paper's proof
  of (ii)), with `X₀ ≥ e^{50}`.

Then `S_k` has measure at least `0.018 Γ`; in particular it is nonempty. -/
theorem lemma_4_8 {f ZB : ℂ → ℂ} (hf : Differentiable ℂ f) {Γ X₀ : ℝ} (hΓ : 0 < Γ)
    (hX : Real.exp 50 ≤ X₀)
    (hi : volume {γ ∈ Icc Γ (2 * Γ) | ‖ZB (1 + γ * I)‖ < 0.6} ≤ ENNReal.ofReal (0.964 * Γ))
    (hii : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (144 * X₀ ^ (-(3 / 8 : ℝ)) * Γ)) :
    ENNReal.ofReal (0.018 * Γ) ≤ volume {γ ∈ Icc Γ (2 * Γ) | 0.6 ≤ ‖ZB (1 + γ * I)‖ ∧
      ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
  set B1 := {γ ∈ Icc Γ (2 * Γ) | ‖ZB (1 + γ * I)‖ < 0.6}
  set B2 := {γ ∈ Icc Γ (2 * Γ) | ∃ s ∈ closedBall (1 + γ * I) (1 / 8), 1 / 16 < ‖f s‖}
  have hX0 : 0 < X₀ := lt_of_lt_of_le (Real.exp_pos _) hX
  -- `X₀^{-3/8} ≤ 1/(3·10⁷)`
  have hXp : X₀ ^ (-(3 / 8 : ℝ)) ≤ 1 / (3 * 10 ^ 7) := by
    have h1 : X₀ ^ (-(3 / 8 : ℝ)) ≤ (Real.exp 50) ^ (-(3 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hX (by norm_num)
    rw [← Real.exp_mul, show 50 * (-(3 / 8 : ℝ)) = -(50 * (3 / 8)) by ring, Real.exp_neg] at h1
    have h2 := exp_large
    have h3 : (Real.exp (50 * (3 / 8)))⁻¹ ≤ 1 / (3 * 10 ^ 7) := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h2
    linarith
  have hXp0 : 0 ≤ X₀ ^ (-(3 / 8 : ℝ)) := Real.rpow_nonneg hX0.le _
  -- the measure of `B2`
  have hB2 : volume B2 ≤ ENNReal.ofReal (0.018 * Γ) := by
    have h := measure_bad_le hf Γ
    have h' : ENNReal.ofReal (π / 16384) * volume B2 ≤
        ENNReal.ofReal (π / 16384) * ENNReal.ofReal (0.018 * Γ) := by
      refine h.trans ?_
      calc ENNReal.ofReal (1 / 2) *
            ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2)
          ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (144 * X₀ ^ (-(3 / 8 : ℝ)) * Γ) := by
            gcongr
        _ = ENNReal.ofReal (1 / 2 * (144 * X₀ ^ (-(3 / 8 : ℝ)) * Γ)) :=
            (ENNReal.ofReal_mul (by norm_num)).symm
        _ ≤ ENNReal.ofReal (π / 16384 * (0.018 * Γ)) := by
            apply ENNReal.ofReal_le_ofReal
            have hpi := Real.pi_gt_three
            nlinarith
        _ = ENNReal.ofReal (π / 16384) * ENNReal.ofReal (0.018 * Γ) :=
            ENNReal.ofReal_mul (by positivity)
    have hc0 : ENNReal.ofReal (π / 16384) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    exact (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp h'
  -- the good set contains `[Γ, 2Γ] \ (B1 ∪ B2)`
  have hsub : Icc Γ (2 * Γ) \ (B1 ∪ B2) ⊆ {γ ∈ Icc Γ (2 * Γ) | 0.6 ≤ ‖ZB (1 + γ * I)‖ ∧
      ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
    rintro γ ⟨hγ, hn⟩
    simp only [B1, B2, mem_union, mem_setOf_eq, not_or, not_and, not_lt, not_exists] at hn
    exact ⟨hγ, hn.1 hγ, fun s hs => hn.2 hγ s hs⟩
  have hU : volume (B1 ∪ B2) ≤ ENNReal.ofReal (0.982 * Γ) := by
    refine (measure_union_le _ _).trans ?_
    calc volume B1 + volume B2 ≤ ENNReal.ofReal (0.964 * Γ) + ENNReal.ofReal (0.018 * Γ) :=
          add_le_add hi hB2
      _ = ENNReal.ofReal (0.982 * Γ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hI : volume (Icc Γ (2 * Γ)) = ENNReal.ofReal Γ := by
    rw [Real.volume_Icc]; congr 1; ring
  calc ENNReal.ofReal (0.018 * Γ) = ENNReal.ofReal Γ - ENNReal.ofReal (0.982 * Γ) := by
        rw [← ENNReal.ofReal_sub _ (by positivity)]; congr 1; ring
    _ ≤ volume (Icc Γ (2 * Γ)) - volume (B1 ∪ B2) := by
        rw [hI]; exact tsub_le_tsub_left hU _
    _ ≤ volume (Icc Γ (2 * Γ) \ (B1 ∪ B2)) := le_measure_diff
    _ ≤ _ := measure_mono hsub

/-- In particular, under the hypotheses of `lemma_4_8`, a good height exists. -/
theorem lemma_4_8_exists {f ZB : ℂ → ℂ} (hf : Differentiable ℂ f) {Γ X₀ : ℝ} (hΓ : 0 < Γ)
    (hX : Real.exp 50 ≤ X₀)
    (hi : volume {γ ∈ Icc Γ (2 * Γ) | ‖ZB (1 + γ * I)‖ < 0.6} ≤ ENNReal.ofReal (0.964 * Γ))
    (hii : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (144 * X₀ ^ (-(3 / 8 : ℝ)) * Γ)) :
    ∃ γ ∈ Icc Γ (2 * Γ), 0.6 ≤ ‖ZB (1 + γ * I)‖ ∧
      ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16 := by
  have h := lemma_4_8 hf hΓ hX hi hii
  have hpos : (0 : ENNReal) < ENNReal.ofReal (0.018 * Γ) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨γ, hγ⟩ := nonempty_of_measure_ne_zero (lt_of_lt_of_le hpos h).ne'
  exact ⟨γ, hγ.1, hγ.2⟩

end GoodHeights

end
