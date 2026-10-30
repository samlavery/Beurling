module

public import RequestProject.Beurling.Noise.KRFacts

/-!
# The variable-width step of §5.9 (proof of Theorem 5.15)

For a cofactor `w > 0` and a width function `H`, the nominal step without its scalar filter is

  `𝒬_w ν = ∫ bx_{H(v/w)}(· - v/w) dν(v)`.

We keep the distribution-function model of `KRFacts.lean`. The distribution function of
`bx_{H(c)}(· - c)` is the ramp `K(t; c) = clamp((t - c)/H(c) + 1/2, 0, 1)`; with `c = v/w` we write
`Kv H w t v`. Since a measure `ν` of distribution function `F` has `∫ K(t; ·) dν = -∫ F ∂_v K`,
we define the step on distribution functions by

  `Qv H w F t = ∫ F(v) J(t, v) dv`,  `J(t, v) = -∂_v K(t; v/w)`

(`Jv`, written out: `J = (1 + (t - c) H'(c)/H(c))/(w H(c))` on `|t - c| < H(c)/2`, `0` off it).
This is the measure step, as the two faithfulness lemmas show:

* `Qv_stepF` : on `δ_a` (distribution function `stepF a`), `Qv` gives `K(·; a/w)`, the
  distribution function of `bx_{H(a/w)}(· - a/w)`; `Kv_eq_boxAvg` identifies it with the box of
  `KRFacts.lean`;
* `Qv_density` : on an absolutely continuous measure `g(v) dv` (distribution function
  `F(v) = ∫_{s ≤ v} g`), `Qv` gives `t ↦ ∫ g(s) K(t; s/w) ds`, the distribution function of
  `∫ bx_{H(s/w)}(· - s/w) g(s) ds`.

The two properties of the proof of Theorem 5.15 (paper, (Q1) and (Q2)):

* `KRn_Qv_le` : (Q1) `‖𝒬_w ν‖_KR ≤ ‖ν‖_KR / w`. (The paper proves this with the factor
  `1 + ϑ_u`; for `|H'| ≤ 2` the factor is `1`, because `∫ J(t, v) dt = 1/w` exactly.)
* `eVariationOn_Qv_le` : (Q2) `TV(𝒬_w ν) ≤ ∫ |F_ν(v)| (2 + |H'(v/w)|)/(w H(v/w)) dv`.

Hypotheses on `H` (`WidthReg`): `H > 0`, `H` is `1`-Lipschitz, and differentiable off a countable
set (the paper's `H` is continuous, non-decreasing and piecewise `C¹`, with `H' ≤ 4·10⁻⁶ H/v`).
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ENNReal

namespace KR

/-- The regularity of the width function used for the variable-width step. -/
structure WidthReg (H : ℝ → ℝ) : Prop where
  pos : ∀ y, 0 < H y
  lip : LipschitzWith 1 H
  diff : ∃ S : Set ℝ, S.Countable ∧ ∀ y ∉ S, DifferentiableAt ℝ H y

/-- `clamp(s, 0, 1)`. -/
noncomputable def ramp (s : ℝ) : ℝ := max 0 (min 1 s)

/-- The distribution function at `t` of `bx_{H(v/w)}(· - v/w)`. -/
noncomputable def Kv (H : ℝ → ℝ) (w t v : ℝ) : ℝ := ramp ((t - v / w) / H (v / w) + 1 / 2)

/-- `J(t, v) = -∂_v Kv(t, v)`. -/
noncomputable def Jv (H : ℝ → ℝ) (w t v : ℝ) : ℝ :=
  if |t - v / w| < H (v / w) / 2 then
    (1 + (t - v / w) * deriv H (v / w) / H (v / w)) / (w * H (v / w)) else 0

/-- The variable-width step on distribution functions: `Qv H w F t = ∫ F(v) J(t, v) dv`. -/
noncomputable def Qv (H : ℝ → ℝ) (w : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ v, F v * Jv H w t v

variable {H : ℝ → ℝ}

namespace WidthReg

lemma abs_sub (hH : WidthReg H) (y z : ℝ) : |H y - H z| ≤ |y - z| := by
  have := hH.lip.dist_le_mul y z
  simpa [Real.dist_eq] using this

lemma abs_deriv_le (hH : WidthReg H) (y : ℝ) : |deriv H y| ≤ 1 := by
  have := norm_deriv_le_of_lipschitz (x₀ := y) hH.lip
  simpa using this

lemma continuous (hH : WidthReg H) : Continuous H := hH.lip.continuous

/-- In the window `|t - y| < H(y)/2`: `|t - y| < H(t)` and `H(y) > (2/3) H(t)`. -/
lemma window (hH : WidthReg H) {t y : ℝ} (h : |t - y| < H y / 2) :
    |t - y| < H t ∧ 2 / 3 * H t < H y := by
  have h1 := abs_le.mp (hH.abs_sub y t)
  have h2 : |y - t| = |t - y| := abs_sub_comm _ _
  rw [h2] at h1
  constructor <;> linarith [h1.1, h1.2]

end WidthReg

/-! ## Basic properties of `J` -/

lemma Jv_nonneg (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t v : ℝ) : 0 ≤ Jv H w t v := by
  unfold Jv
  split_ifs with h
  · have hp := hH.pos (v / w)
    have hd := hH.abs_deriv_le (v / w)
    have : |(t - v / w) * deriv H (v / w) / H (v / w)| ≤ 1 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hp, div_le_iff₀ hp]
      have := mul_le_mul h.le hd (abs_nonneg _) (by positivity)
      linarith
    have := neg_abs_le ((t - v / w) * deriv H (v / w) / H (v / w))
    apply div_nonneg (by linarith) (by positivity)
  · exact le_rfl

lemma Jv_eq_zero (hH : WidthReg H) {w t v : ℝ} (h : H t ≤ |t - v / w|) : Jv H w t v = 0 := by
  unfold Jv
  rw [if_neg]
  intro h'
  exact absurd (hH.window h').1 (not_lt.mpr h)

lemma Jv_le (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t v : ℝ) :
    Jv H w t v ≤ 9 / 4 / (w * H t) := by
  unfold Jv
  have hHt := hH.pos t
  split_ifs with h
  · have hp := hH.pos (v / w)
    obtain ⟨-, h2⟩ := hH.window h
    have hd := hH.abs_deriv_le (v / w)
    have : (t - v / w) * deriv H (v / w) / H (v / w) ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      have := mul_le_mul h.le hd (abs_nonneg _) (by positivity)
      have := le_abs_self ((t - v / w) * deriv H (v / w))
      rw [abs_mul] at this
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx0 : 0 ≤ 1 + (t - v / w) * deriv H (v / w) / H (v / w) := by
      have := Jv_nonneg hH hw t v
      unfold Jv at this; rw [if_pos h] at this
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by
        nlinarith [h.2, mul_pos hw hp])
    have e1 : (1 + (t - v / w) * deriv H (v / w) / H (v / w)) * (w * H t) ≤
        3 / 2 * (w * H t) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : w * H t ≤ 3 / 2 * (w * H (v / w)) := by nlinarith
    nlinarith
  · positivity

lemma measurable_Jv (hH : WidthReg H) (w : ℝ) :
    Measurable (Function.uncurry (Jv H w)) := by
  have hc := hH.continuous
  have hm : Measurable fun p : ℝ × ℝ => p.2 / w := measurable_snd.div_const w
  have hHm : Measurable fun p : ℝ × ℝ => H (p.2 / w) := hc.measurable.comp hm
  have hdm : Measurable fun p : ℝ × ℝ => deriv H (p.2 / w) := (measurable_deriv H).comp hm
  unfold Jv
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt ((measurable_fst.sub hm).abs) (hHm.div_const 2)
  · exact ((measurable_const.add (((measurable_fst.sub hm).mul hdm).div hHm)).div
      (measurable_const.mul hHm))

lemma measurable_Jv_right (hH : WidthReg H) (w t : ℝ) : Measurable (Jv H w t) :=
  (measurable_Jv hH w).comp (measurable_const.prodMk measurable_id)

lemma measurable_Jv_left (hH : WidthReg H) (w v : ℝ) : Measurable fun t => Jv H w t v :=
  (measurable_Jv hH w).comp (measurable_id.prodMk measurable_const)

/-- For fixed `t`, `J(t, ·)` vanishes off `w (t - H(t), t + H(t))`. -/
lemma Jv_support (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {t v : ℝ} (h : Jv H w t v ≠ 0) :
    w * (t - H t) < v ∧ v < w * (t + H t) := by
  by_contra hc
  apply h
  apply Jv_eq_zero hH
  rw [not_and_or, not_lt, not_lt] at hc
  have hHt := hH.pos t
  rcases hc with hc | hc
  · have : v / w ≤ t - H t := by rw [div_le_iff₀ hw]; linarith
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : t + H t ≤ v / w := by rw [le_div_iff₀ hw]; linarith
    rw [abs_of_nonpos (by linarith)]; linarith

lemma integrable_Jv (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) :
    Integrable (Jv H w t) := by
  have hb : ∀ v, Jv H w t v = (Icc (w * (t - H t)) (w * (t + H t))).indicator (Jv H w t) v := by
    intro v
    by_cases h : Jv H w t v = 0
    · rw [Set.indicator_apply]; split_ifs <;> simp [h]
    · have := Jv_support hH hw h
      rw [Set.indicator_of_mem (show v ∈ Icc (w * (t - H t)) (w * (t + H t)) from
        ⟨this.1.le, this.2.le⟩)]
  rw [show Jv H w t = (Icc (w * (t - H t)) (w * (t + H t))).indicator (Jv H w t) from funext hb]
  refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
  refine Measure.integrableOn_of_bounded (M := 9 / 4 / (w * H t)) ?_
    (measurable_Jv_right hH w t).aestronglyMeasurable ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Jv_nonneg hH hw t v)]
    exact Jv_le hH hw t v

/-! ## The ramp and its derivative in `v` -/

lemma ramp_of_mem {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : ramp s = s := by
  unfold ramp; rw [min_eq_right h1.le, max_eq_right h0.le]

lemma ramp_of_nonpos {s : ℝ} (h : s ≤ 0) : ramp s = 0 := by
  unfold ramp; rw [max_eq_left (min_le_of_right_le h)]

lemma ramp_of_one_le {s : ℝ} (h : 1 ≤ s) : ramp s = 1 := by
  unfold ramp; rw [min_eq_left h, max_eq_right zero_le_one]

lemma continuous_ramp : Continuous ramp := by
  unfold ramp; fun_prop

/-- `φ(v) = (t - v/w)/H(v/w) + 1/2`, so that `Kv = ramp ∘ φ`. -/
noncomputable def phiV (H : ℝ → ℝ) (w t v : ℝ) : ℝ := (t - v / w) / H (v / w) + 1 / 2

lemma continuous_phiV (hH : WidthReg H) (w t : ℝ) : Continuous (phiV H w t) := by
  unfold phiV
  have hc := hH.continuous
  exact ((continuous_const.sub (continuous_id.div_const w)).div
    (hc.comp (continuous_id.div_const w)) fun v => (hH.pos _).ne').add continuous_const

lemma continuous_Kv (hH : WidthReg H) (w t : ℝ) : Continuous (Kv H w t) :=
  continuous_ramp.comp (continuous_phiV hH w t)

lemma hasDerivAt_phiV (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) {v : ℝ}
    (hd : DifferentiableAt ℝ H (v / w)) :
    HasDerivAt (phiV H w t)
      (-((1 + (t - v / w) * deriv H (v / w) / H (v / w)) / (w * H (v / w)))) v := by
  have hp := hH.pos (v / w)
  have hc : HasDerivAt (fun v => v / w) (1 / w) v := (hasDerivAt_id v).div_const w
  have hHd : HasDerivAt (fun v => H (v / w)) (deriv H (v / w) * (1 / w)) v :=
    hd.hasDerivAt.comp v hc
  have hnum : HasDerivAt (fun v => t - v / w) (-(1 / w)) v := (hc.const_sub t)
  have := (hnum.div hHd hp.ne').add_const (1 / 2 : ℝ)
  unfold phiV
  convert! this using 1
  field_simp
  ring

lemma phiV_lt_zero_iff (hH : WidthReg H) {w t v : ℝ} :
    phiV H w t v < 0 ↔ t - v / w < -(H (v / w) / 2) := by
  have hp := hH.pos (v / w)
  unfold phiV
  constructor
  · intro h
    have : (t - v / w) / H (v / w) < -(1 / 2) := by linarith
    rw [div_lt_iff₀ hp] at this; linarith
  · intro h
    have : (t - v / w) / H (v / w) < -(1 / 2) := by rw [div_lt_iff₀ hp]; linarith
    linarith

lemma one_lt_phiV_iff (hH : WidthReg H) {w t v : ℝ} :
    1 < phiV H w t v ↔ H (v / w) / 2 < t - v / w := by
  have hp := hH.pos (v / w)
  unfold phiV
  constructor
  · intro h
    have : 1 / 2 < (t - v / w) / H (v / w) := by linarith
    rw [lt_div_iff₀ hp] at this; linarith
  · intro h
    have : 1 / 2 < (t - v / w) / H (v / w) := by rw [lt_div_iff₀ hp]; linarith
    linarith

lemma mem_window_iff (hH : WidthReg H) {w t v : ℝ} :
    (0 < phiV H w t v ∧ phiV H w t v < 1) ↔ |t - v / w| < H (v / w) / 2 := by
  have hp := hH.pos (v / w)
  unfold phiV
  rw [abs_lt]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · have : -(1 / 2) < (t - v / w) / H (v / w) := by linarith
      rw [lt_div_iff₀ hp] at this; linarith
    · have : (t - v / w) / H (v / w) < 1 / 2 := by linarith
      rw [div_lt_iff₀ hp] at this; linarith
  · rintro ⟨h0, h1⟩
    constructor
    · have : -(1 / 2) < (t - v / w) / H (v / w) := by rw [lt_div_iff₀ hp]; linarith
      linarith
    · have : (t - v / w) / H (v / w) < 1 / 2 := by rw [div_lt_iff₀ hp]; linarith
      linarith

/-- Off the countable exceptional set, `∂_v Kv(t, v) = -J(t, v)`. -/
lemma hasDerivAt_Kv (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) {v : ℝ}
    (hd : DifferentiableAt ℝ H (v / w)) (h0 : phiV H w t v ≠ 0) (h1 : phiV H w t v ≠ 1) :
    HasDerivAt (Kv H w t) (-Jv H w t v) v := by
  have hφ := hasDerivAt_phiV hH hw t hd
  have hcφ := continuous_phiV hH w t
  have hK : Kv H w t = ramp ∘ phiV H w t := rfl
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · -- left of the window: `Kv = 0` near `v`
    have hJ : Jv H w t v = 0 := by
      unfold Jv; rw [if_neg]; rw [abs_lt, not_and_or]; left
      push_neg; exact ((phiV_lt_zero_iff hH).mp hneg).le
    rw [hJ, neg_zero]
    apply (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hcφ.continuousAt.eventually (Iio_mem_nhds hneg)] with u hu
    rw [hK]; exact ramp_of_nonpos (le_of_lt hu)
  rcases lt_or_gt_of_ne h1 with hin | hbig
  · have hJ : Jv H w t v =
        (1 + (t - v / w) * deriv H (v / w) / H (v / w)) / (w * H (v / w)) := by
      unfold Jv; rw [if_pos ((mem_window_iff hH).mp ⟨hpos, hin⟩)]
    rw [hJ]
    apply hφ.congr_of_eventuallyEq
    filter_upwards [hcφ.continuousAt.eventually (Ioo_mem_nhds hpos hin)] with u hu
    rw [hK]; exact ramp_of_mem hu.1 hu.2
  · have hJ : Jv H w t v = 0 := by
      unfold Jv; rw [if_neg]; rw [abs_lt, not_and_or]; right
      push_neg; exact ((one_lt_phiV_iff hH).mp hbig).le
    rw [hJ, neg_zero]
    apply (hasDerivAt_const v (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hcφ.continuousAt.eventually (Ioi_mem_nhds hbig)] with u hu
    rw [hK]; exact ramp_of_one_le (le_of_lt hu)

/-- The exceptional set is countable: `y ↦ y ∓ H(y)/2` is strictly increasing. -/
lemma countable_exc (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) {S : Set ℝ}
    (hS : S.Countable) :
    ((fun v => v / w) ⁻¹' S ∪ {v | phiV H w t v = 0} ∪ {v | phiV H w t v = 1}).Countable := by
  have hinj : Function.Injective fun v : ℝ => v / w := fun a b h => by
    simpa [div_left_inj' hw.ne'] using h
  have hmono : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      StrictMono fun v : ℝ => v / w + σ * (H (v / w) / 2) := by
    intro σ hσ a b hab
    have hab' : a / w < b / w := div_lt_div_of_pos_right hab hw
    have h1 := abs_le.mp (hH.abs_sub (b / w) (a / w))
    rw [abs_of_pos (by linarith)] at h1
    rcases hσ with rfl | rfl <;> simp only <;> nlinarith [h1.1, h1.2]
  have hsub0 : {v | phiV H w t v = 0} ⊆
      (fun v : ℝ => v / w + (-1) * (H (v / w) / 2)) ⁻¹' {t} := by
    intro v hv
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff] at hv ⊢
    have hp := hH.pos (v / w)
    unfold phiV at hv
    have : (t - v / w) / H (v / w) = -(1 / 2) := by linarith
    rw [div_eq_iff hp.ne'] at this; linarith
  have hsub1 : {v | phiV H w t v = 1} ⊆
      (fun v : ℝ => v / w + 1 * (H (v / w) / 2)) ⁻¹' {t} := by
    intro v hv
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff] at hv ⊢
    have hp := hH.pos (v / w)
    unfold phiV at hv
    have : (t - v / w) / H (v / w) = 1 / 2 := by linarith
    rw [div_eq_iff hp.ne'] at this; linarith
  refine ((hS.preimage hinj).union ?_).union ?_
  · exact ((Set.countable_singleton t).preimage (hmono (-1) (Or.inr rfl)).injective).mono hsub0
  · exact ((Set.countable_singleton t).preimage (hmono 1 (Or.inl rfl)).injective).mono hsub1

lemma Kv_eq_zero (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {t v : ℝ} (hv : w * (t + H t) ≤ v) :
    Kv H w t v = 0 := by
  apply ramp_of_nonpos
  have hc : t + H t ≤ v / w := by rw [le_div_iff₀ hw]; linarith
  have h1 := abs_le.mp (hH.abs_sub (v / w) t)
  have hp := hH.pos (v / w)
  have hHt := hH.pos t
  have : H (v / w) ≤ 2 * (v / w - t) := by
    rw [abs_of_nonneg (by linarith)] at h1; linarith [h1.2]
  have : (t - v / w) / H (v / w) ≤ -(1 / 2) := by rw [div_le_iff₀ hp]; linarith
  linarith

lemma Kv_eq_one (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {t v : ℝ} (hv : v ≤ w * (t - H t)) :
    Kv H w t v = 1 := by
  apply ramp_of_one_le
  have hc : v / w ≤ t - H t := by rw [div_le_iff₀ hw]; linarith
  have h1 := abs_le.mp (hH.abs_sub (v / w) t)
  have hp := hH.pos (v / w)
  have hHt := hH.pos t
  have : H (v / w) ≤ 2 * (t - v / w) := by
    rw [abs_of_nonpos (by linarith)] at h1; linarith [h1.2]
  have : 1 / 2 ≤ (t - v / w) / H (v / w) := by rw [le_div_iff₀ hp]; linarith
  linarith

/-- `∫_a^b J(t, v) dv = Kv(t, a) - Kv(t, b)`. -/
lemma integral_Jv (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ v in a..b, Jv H w t v = Kv H w t a - Kv H w t b := by
  obtain ⟨S, hS, hdS⟩ := hH.diff
  have h := integral_eq_of_hasDerivAt_off_countable_of_le (Kv H w t) (fun v => -Jv H w t v)
    hab (countable_exc hH hw t hS) (continuous_Kv hH w t).continuousOn ?_
    (integrable_Jv hH hw t).intervalIntegrable.neg
  · rw [intervalIntegral.integral_neg] at h; linarith
  · intro v hv
    simp only [mem_diff, mem_union, mem_preimage, mem_setOf_eq, not_or] at hv
    exact hasDerivAt_Kv hH hw t (hdS _ hv.2.1.1) hv.2.1.2 hv.2.2

/-- **Faithfulness on `δ_a`**: `Qv` maps `δ_a` to `bx_{H(a/w)}(· - a/w)`. -/
theorem Qv_stepF (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (a t : ℝ) :
    Qv H w (stepF a) t = Kv H w t a := by
  set B := max a (w * (t + H t))
  have hB : a ≤ B := le_max_left _ _
  have hJB : ∀ v, B < v → Jv H w t v = 0 := by
    intro v hv
    by_contra h
    have := (Jv_support hH hw h).2
    have : w * (t + H t) ≤ B := le_max_right _ _
    linarith
  have e : (fun v => stepF a v * Jv H w t v) = (Icc a B).indicator (Jv H w t) := by
    funext v
    unfold stepF
    by_cases h1 : a ≤ v
    · by_cases h2 : v ≤ B
      · rw [if_pos h1, one_mul, Set.indicator_of_mem (show v ∈ Icc a B from ⟨h1, h2⟩)]
      · push_neg at h2
        rw [if_pos h1, one_mul, hJB v h2,
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr h2))]
    · rw [if_neg h1, zero_mul, Set.indicator_of_notMem (fun h => h1 h.1)]
  unfold Qv
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hB, integral_Jv hH hw t hB,
    Kv_eq_zero hH hw (le_max_right _ _), sub_zero]

/-- `∫ J(t, v) dv = 1`. -/
lemma integral_Jv_univ (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t : ℝ) :
    ∫ v, Jv H w t v = 1 := by
  set a := w * (t - H t) - 1
  have h := Qv_stepF hH hw a t
  have ha : Kv H w t a = 1 := Kv_eq_one hH hw (by simp only [a]; linarith)
  rw [ha] at h
  rw [← h]
  unfold Qv
  congr 1
  funext v
  unfold stepF
  by_cases hv : a ≤ v
  · rw [if_pos hv, one_mul]
  · rw [if_neg hv, zero_mul]
    by_contra hc
    have := (Jv_support hH hw hc).1
    simp only [a] at hv; linarith

/-- **Faithfulness on densities**: for an integrable density `g`, with distribution function
`F(v) = ∫_{s ≤ v} g(s) ds`, `Qv F (t) = ∫ g(s) Kv(t, s) ds`, the distribution function at `t` of
`∫ bx_{H(s/w)}(· - s/w) g(s) ds`. -/
theorem Qv_density (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {g : ℝ → ℝ} (hg : Integrable g)
    (t : ℝ) :
    Qv H w (fun v => ∫ s, stepF s v * g s) t = ∫ s, g s * Kv H w t s := by
  unfold Qv
  have hJ := integrable_Jv hH hw t
  have hstep : Measurable (Function.uncurry fun v s : ℝ => stepF s v) := by
    unfold stepF
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const
      measurable_const
  have hint : Integrable (Function.uncurry fun v s => g s * (stepF s v * Jv H w t v))
      (volume.prod volume) := by
    have hprod := hJ.mul_prod hg
    refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hg.aestronglyMeasurable.comp_snd).mul
        ((hstep.aestronglyMeasurable).mul
          ((measurable_Jv_right hH w t).aestronglyMeasurable.comp_fst))
    · simp only [Function.uncurry, norm_mul]
      have : ‖stepF p.2 p.1‖ ≤ 1 := by unfold stepF; split_ifs <;> simp
      have h0 := norm_nonneg (Jv H w t p.1)
      have h1 := norm_nonneg (g p.2)
      have := mul_le_mul_of_nonneg_right this h0
      nlinarith [mul_le_mul_of_nonneg_left this h1]
  calc ∫ v, (∫ s, stepF s v * g s) * Jv H w t v
      = ∫ v, ∫ s, g s * (stepF s v * Jv H w t v) := by
        congr 1; funext v
        rw [← integral_mul_const]
        congr 1; funext s; ring
    _ = ∫ s, ∫ v, g s * (stepF s v * Jv H w t v) := integral_integral_swap hint
    _ = ∫ s, g s * Kv H w t s := by
        congr 1; funext s
        rw [integral_const_mul]
        congr 1
        exact Qv_stepF hH hw s t

/-- `Kv` is the box of `KRFacts.lean`: `Kv(t, a) = boxAvg_{H(a/w)} (stepF (a/w)) t`. -/
lemma Kv_eq_boxAvg (hH : WidthReg H) (w t a : ℝ) :
    Kv H w t a = boxAvg (H (a / w)) (stepF (a / w)) t := by
  have hp := hH.pos (a / w)
  rw [boxAvg_stepF hp]
  unfold Kv ramp
  set h := H (a / w)
  set c := a / w
  rcases le_or_gt (t + h / 2 - c) 0 with h1 | h1
  · rw [max_eq_left h1, max_eq_left (by linarith : t - h / 2 - c ≤ 0)]
    have : (t - c) / h + 1 / 2 ≤ 0 := by
      have : (t - c) / h ≤ -(1 / 2) := by rw [div_le_iff₀ hp]; linarith
      linarith
    rw [max_eq_left (min_le_of_right_le this)]; simp
  rcases le_or_gt 0 (t - h / 2 - c) with h2 | h2
  · rw [max_eq_right h1.le, max_eq_right h2]
    have : 1 ≤ (t - c) / h + 1 / 2 := by
      have : 1 / 2 ≤ (t - c) / h := by rw [le_div_iff₀ hp]; linarith
      linarith
    rw [min_eq_left this, max_eq_right zero_le_one]
    field_simp; ring
  · rw [max_eq_right h1.le, max_eq_left h2.le, sub_zero]
    have e : (t - c) / h + 1 / 2 = h⁻¹ * (t + h / 2 - c) := by field_simp; ring
    rw [e, min_eq_right, max_eq_right]
    · exact mul_nonneg (inv_pos.mpr hp).le h1.le
    · rw [inv_mul_le_iff₀ hp]; linarith

/-! ## (Q1): the KR norm -/

/-- `J(·, v)` is the indicator of the window `(c - h/2, c + h/2)` of an affine function. -/
lemma Jv_left_eq (H : ℝ → ℝ) (w v : ℝ) :
    (fun t => Jv H w t v) = (Ioo (v / w - H (v / w) / 2) (v / w + H (v / w) / 2)).indicator
      (fun t => (1 + (t - v / w) * deriv H (v / w) / H (v / w)) / (w * H (v / w))) := by
  funext t
  unfold Jv
  simp only [Set.indicator, Set.mem_Ioo, abs_lt]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `∫ J(t, v) dt = 1/w`, and `J(·, v)` is integrable. -/
lemma integral_Jv_left (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (v : ℝ) :
    Integrable (fun t => Jv H w t v) ∧ ∫ t, Jv H w t v = w⁻¹ := by
  rw [Jv_left_eq]
  set c := v / w
  set h := H c
  set d := deriv H c
  have hp : 0 < h := hH.pos c
  have hcont : Continuous fun t : ℝ => (1 + (t - c) * d / h) / (w * h) := by fun_prop
  refine ⟨(hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator
    measurableSet_Ioo, ?_⟩
  rw [integral_indicator measurableSet_Ioo, integral_Ioc_eq_integral_Ioo.symm,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_div]
  have e : ∫ x in (c - h / 2)..(c + h / 2), (1 + (x - c) * d / h) = h := by
    rw [intervalIntegral.integral_comp_sub_right (fun y => 1 + y * d / h) c]
    have c2 : IntervalIntegrable (fun y : ℝ => y * d / h) volume (c - h / 2 - c) (c + h / 2 - c) :=
      ((continuous_id.mul continuous_const).div_const h).intervalIntegrable _ _
    rw [intervalIntegral.integral_add intervalIntegrable_const c2]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
      intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [e]
  field_simp

/-- **(Q1)**: `‖𝒬_w ν‖_KR ≤ ‖ν‖_KR / w` (exact factor `1/w`, see the module docstring). -/
theorem KRn_Qv_le (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {F : ℝ → ℝ} (hF : Measurable F) :
    KRn (Qv H w F) ≤ ENNReal.ofReal w⁻¹ * KRn F := by
  unfold KRn Qv
  have hJm := measurable_Jv hH w
  have hjoint : Measurable (Function.uncurry fun t v => ‖F v‖ₑ * ‖Jv H w t v‖ₑ) :=
    (hF.comp measurable_snd).enorm.mul hJm.enorm
  have hJt : ∀ v, ∫⁻ t, ‖Jv H w t v‖ₑ = ENNReal.ofReal w⁻¹ := by
    intro v
    obtain ⟨hi, he⟩ := integral_Jv_left hH hw v
    rw [← he, ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun t => Jv_nonneg hH hw t v)]
    congr 1; funext t
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Jv_nonneg hH hw t v)]
  calc ∫⁻ t, ‖∫ v, F v * Jv H w t v‖ₑ
      ≤ ∫⁻ t, ∫⁻ v, ‖F v‖ₑ * ‖Jv H w t v‖ₑ := by
        refine lintegral_mono fun t => ?_
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1; funext v; rw [enorm_mul]
    _ = ∫⁻ v, ∫⁻ t, ‖F v‖ₑ * ‖Jv H w t v‖ₑ := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ v, ‖F v‖ₑ * ENNReal.ofReal w⁻¹ := by
        congr 1; funext v
        rw [lintegral_const_mul _ ((measurable_Jv_left hH w v).enorm), hJt]
    _ = ENNReal.ofReal w⁻¹ * ∫⁻ v, ‖F v‖ₑ := by
        rw [lintegral_mul_const _ hF.enorm, mul_comm]

/-! ## Regularity and linearity of `Qv` -/

lemma integrable_mul_Jv (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {F : ℝ → ℝ} (hF : BM F)
    (t : ℝ) : Integrable fun v => F v * Jv H w t v := by
  obtain ⟨hm, M, hM⟩ := hF
  refine (integrable_Jv hH hw t).bdd_mul (c := M) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]; exact hM v

lemma BM.Qv (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {F : ℝ → ℝ} (hF : BM F) :
    BM (KR.Qv H w F) := by
  refine ⟨?_, hF.2.choose, fun t => ?_⟩
  · have hj : Measurable (Function.uncurry fun t v => F v * Jv H w t v) :=
      (hF.1.comp measurable_snd).mul (measurable_Jv hH w)
    exact (hj.stronglyMeasurable.integral_prod_right).measurable
  · have hM := hF.2.choose_spec
    have hM0 : 0 ≤ hF.2.choose := (abs_nonneg _).trans (hM 0)
    unfold KR.Qv
    rw [← Real.norm_eq_abs]
    calc ‖∫ v, F v * Jv H w t v‖ ≤ ∫ v, hF.2.choose * Jv H w t v := by
          apply norm_integral_le_of_norm_le ((integrable_Jv hH hw t).const_mul _)
          refine Filter.Eventually.of_forall fun v => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Jv_nonneg hH hw t v)]
          exact mul_le_mul_of_nonneg_right (hM v) (Jv_nonneg hH hw t v)
      _ = hF.2.choose := by rw [integral_const_mul, integral_Jv_univ hH hw t, mul_one]

lemma Qv_add (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {F G : ℝ → ℝ} (hF : BM F) (hG : BM G)
    (t : ℝ) : Qv H w (fun v => F v + G v) t = Qv H w F t + Qv H w G t := by
  unfold Qv
  rw [← integral_add (integrable_mul_Jv hH hw hF t) (integrable_mul_Jv hH hw hG t)]
  congr 1; funext v; ring

lemma Qv_const_mul (c : ℝ) (F : ℝ → ℝ) (w t : ℝ) :
    Qv H w (fun v => c * F v) t = c * Qv H w F t := by
  unfold Qv
  rw [← integral_const_mul]
  congr 1; funext v; ring

lemma Qv_sum (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, BM (F i)) (t : ℝ) :
    Qv H w (fun v => ∑ i ∈ s, F i v) t = ∑ i ∈ s, Qv H w (F i) t := by
  unfold Qv
  rw [← integral_finset_sum _ fun i hi => integrable_mul_Jv hH hw (hF i hi) t]
  congr 1; funext v; rw [Finset.sum_mul]

lemma Qv_congr {F G : ℝ → ℝ} (h : ∀ v, F v = G v) (w t : ℝ) : Qv H w F t = Qv H w G t := by
  rw [show F = G from funext h]

/-- Support propagation: if `F` vanishes off `[p - R, p + R]` and every `y` with
`|y - p/w| ≤ R/w` has `R/w + H(y)/2 ≤ R'`, then `𝒬_w F` vanishes off `[p/w - R', p/w + R']`. -/
lemma Qv_eq_zero_of_support {w : ℝ} (hw : 0 < w) {F : ℝ → ℝ} {p R R' : ℝ}
    (hF : ∀ v, R < |v - p| → F v = 0)
    (hR : ∀ y, |y - p / w| ≤ R / w → R / w + H y / 2 ≤ R') {t : ℝ} (ht : R' < |t - p / w|) :
    Qv H w F t = 0 := by
  unfold Qv
  have : (fun v => F v * Jv H w t v) = fun _ => 0 := by
    funext v
    by_cases h1 : R < |v - p|
    · rw [hF v h1, zero_mul]
    push_neg at h1
    have hy : |v / w - p / w| ≤ R / w := by
      rw [← sub_div, abs_div, abs_of_pos hw]; exact div_le_div_of_nonneg_right h1 hw.le
    unfold Jv
    rw [if_neg, mul_zero]
    intro hJ
    have := hR _ hy
    have htri : |t - p / w| ≤ |t - v / w| + |v / w - p / w| := abs_sub_le _ _ _
    linarith
  rw [this, integral_zero]

/-! ## (Q2): the total variation -/

/-- The variation function of a "tent" `j = (A₀ + s(t - L)) 1[L < t < R]`. -/
noncomputable def tentM (L R A0 s t : ℝ) : ℝ :=
  if t ≤ L then 0 else if t < R then A0 + |s| * (t - L) else A0 + |s| * (R - L) + (A0 + s * (R - L))

set_option linter.unusedSimpArgs false in
lemma tent_var {L R A0 s a b : ℝ} (hLR : L < R) (hA0 : 0 ≤ A0) (hAR : 0 ≤ A0 + s * (R - L))
    (hab : a ≤ b) :
    |(if L < b ∧ b < R then A0 + s * (b - L) else 0) -
        (if L < a ∧ a < R then A0 + s * (a - L) else 0)| ≤ tentM L R A0 s b - tentM L R A0 s a := by
  have hs1 := le_abs_self s
  have hs2 := neg_abs_le s
  have hs0 := abs_nonneg s
  have hk := mul_le_mul_of_nonneg_left hab hs0
  unfold tentM
  rcases le_or_gt a L with ha | ha
  · have hna : ¬ (L < a ∧ a < R) := fun h => by linarith [h.1]
    rcases le_or_gt b L with hb | hb
    · have hnb : ¬ (L < b ∧ b < R) := fun h => by linarith [h.1]
      simp only [ha, hb, hna, hnb, 
        if_true, if_false, and_self, and_false, false_and, and_true, true_and]; simp
    rcases lt_or_ge b R with hb' | hb'
    · have hpb : L < b ∧ b < R := ⟨hb, hb'⟩
      have hnb : ¬ b ≤ L := not_le.mpr hb
      simp only [ha, hpb, hna, hnb, hb', 
        if_true, if_false, and_self, and_false, false_and, and_true, true_and]
      rw [abs_le]; constructor <;> nlinarith
    · have hnb : ¬ (L < b ∧ b < R) := fun h => by linarith [h.2]
      have hnb1 : ¬ b ≤ L := not_le.mpr hb
      have hnb2 : ¬ b < R := not_lt.mpr hb'
      simp only [ha, hna, hnb, hnb1, hnb2, 
        if_true, if_false, and_self, and_false, false_and, and_true, true_and]
      rw [abs_le]; constructor <;> nlinarith
  rcases lt_or_ge a R with ha' | ha'
  · have hpa : L < a ∧ a < R := ⟨ha, ha'⟩
    have hna1 : ¬ a ≤ L := not_le.mpr ha
    have hnb1 : ¬ b ≤ L := fun h => by linarith
    rcases lt_or_ge b R with hb' | hb'
    · have hpb : L < b ∧ b < R := ⟨by linarith, hb'⟩
      simp only [hpa, hpb, hna1, hnb1, ha', hb', 
        if_true, if_false, and_self, and_false, false_and, and_true, true_and]
      rw [abs_le]; constructor <;> nlinarith
    · have hnb : ¬ (L < b ∧ b < R) := fun h => by linarith [h.2]
      have hnb2 : ¬ b < R := not_lt.mpr hb'
      simp only [hpa, hnb, hna1, hnb1, ha', hnb2, 
        if_true, if_false, and_self, and_false, false_and, and_true, true_and]
      rw [abs_le]; constructor <;> nlinarith
  · have hna : ¬ (L < a ∧ a < R) := fun h => by linarith [h.2]
    have hnb : ¬ (L < b ∧ b < R) := fun h => by linarith [h.2]
    have hna1 : ¬ a ≤ L := not_le.mpr ha
    have hnb1 : ¬ b ≤ L := fun h => by linarith
    have hna2 : ¬ a < R := not_lt.mpr ha'
    have hnb2 : ¬ b < R := fun h => by linarith
    simp only [hna, hnb, hna1, hnb1, hna2, hnb2,
      if_false, and_false, false_and, and_true, true_and]; simp

/-- The tent parameters of `J(·, v)`. -/
noncomputable def tL (H : ℝ → ℝ) (w v : ℝ) : ℝ := v / w - H (v / w) / 2
noncomputable def tR (H : ℝ → ℝ) (w v : ℝ) : ℝ := v / w + H (v / w) / 2
noncomputable def tA (H : ℝ → ℝ) (w v : ℝ) : ℝ := (1 - deriv H (v / w) / 2) / (w * H (v / w))
noncomputable def tS (H : ℝ → ℝ) (w v : ℝ) : ℝ := deriv H (v / w) / (w * H (v / w) ^ 2)

/-- The variation function of `J(·, v)`. -/
noncomputable def Mv (H : ℝ → ℝ) (w t v : ℝ) : ℝ :=
  tentM (tL H w v) (tR H w v) (tA H w v) (tS H w v) t

lemma Jv_eq_tent (hH : WidthReg H) (w t v : ℝ) (hw : 0 < w) :
    Jv H w t v = if tL H w v < t ∧ t < tR H w v then
      tA H w v + tS H w v * (t - tL H w v) else 0 := by
  have h := congrFun (Jv_left_eq H w v) t
  rw [h, Set.indicator_apply]
  simp only [Set.mem_Ioo, tL, tR]
  by_cases hc : v / w - H (v / w) / 2 < t ∧ t < v / w + H (v / w) / 2
  · simp only [hc, ↓reduceIte, and_self]
    unfold tA tS
    have hp := hH.pos (v / w)
    field_simp
    ring
  · simp only [hc, ↓reduceIte]

lemma tent_params (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (v : ℝ) :
    tL H w v < tR H w v ∧ 0 ≤ tA H w v ∧ 0 ≤ tA H w v + tS H w v * (tR H w v - tL H w v) ∧
      tA H w v + |tS H w v| * (tR H w v - tL H w v) +
        (tA H w v + tS H w v * (tR H w v - tL H w v)) =
          (2 + |deriv H (v / w)|) / (w * H (v / w)) := by
  have hp := hH.pos (v / w)
  have hd := abs_le.mp (hH.abs_deriv_le (v / w))
  unfold tL tR tA tS
  refine ⟨by linarith, div_nonneg (by linarith) (by positivity), ?_, ?_⟩
  · have e : (1 - deriv H (v / w) / 2) / (w * H (v / w)) + deriv H (v / w) / (w * H (v / w) ^ 2) *
        (v / w + H (v / w) / 2 - (v / w - H (v / w) / 2)) =
        (1 + deriv H (v / w) / 2) / (w * H (v / w)) := by field_simp; ring
    rw [e]; exact div_nonneg (by linarith) (by positivity)
  · rw [abs_div, abs_of_pos (by positivity : 0 < w * H (v / w) ^ 2)]
    field_simp
    ring

lemma measurable_Mv (hH : WidthReg H) (w t : ℝ) : Measurable (Mv H w t) := by
  have hc := hH.continuous
  have hm : Measurable fun v : ℝ => v / w := measurable_id.div_const w
  have hHm : Measurable fun v : ℝ => H (v / w) := hc.measurable.comp hm
  have hdm : Measurable fun v : ℝ => deriv H (v / w) := (measurable_deriv H).comp hm
  have hL : Measurable (tL H w) := hm.sub (hHm.div_const 2)
  have hR : Measurable (tR H w) := hm.add (hHm.div_const 2)
  have hA : Measurable (tA H w) := (measurable_const.sub (hdm.div_const 2)).div
    (measurable_const.mul hHm)
  have hS : Measurable (tS H w) := hdm.div (measurable_const.mul (hHm.pow_const 2))
  unfold Mv tentM
  refine Measurable.ite (measurableSet_le measurable_const hL) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_const hR) ?_ ?_
  · exact hA.add (hS.abs.mul (measurable_const.sub hL))
  · exact (hA.add (hS.abs.mul (hR.sub hL))).add (hA.add (hS.mul (hR.sub hL)))

lemma Jv_sub_le (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (v : ℝ) {a b : ℝ} (hab : a ≤ b) :
    |Jv H w b v - Jv H w a v| ≤ Mv H w b v - Mv H w a v := by
  obtain ⟨h1, h2, h3, -⟩ := tent_params hH hw v
  rw [Jv_eq_tent hH w b v hw, Jv_eq_tent hH w a v hw]
  exact tent_var h1 h2 h3 hab

lemma Mv_le (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t v : ℝ) :
    Mv H w t v ≤ (2 + |deriv H (v / w)|) / (w * H (v / w)) := by
  obtain ⟨h1, -, -, h4⟩ := tent_params hH hw v
  have := Jv_sub_le hH hw v (le_max_left t (tR H w v))
  have e : Mv H w (max t (tR H w v)) v = (2 + |deriv H (v / w)|) / (w * H (v / w)) := by
    unfold Mv tentM
    rw [if_neg (by have := le_max_right t (tR H w v); linarith),
      if_neg (not_lt.mpr (le_max_right _ _)), h4]
  rw [e] at this
  linarith [abs_nonneg (Jv H w (max t (tR H w v)) v - Jv H w t v)]

lemma Mv_nonneg (hH : WidthReg H) {w : ℝ} (hw : 0 < w) (t v : ℝ) : 0 ≤ Mv H w t v := by
  obtain ⟨h1, -, -, -⟩ := tent_params hH hw v
  have := Jv_sub_le hH hw v (min_le_left t (tL H w v))
  have e : Mv H w (min t (tL H w v)) v = 0 := by
    unfold Mv tentM; rw [if_pos (min_le_right _ _)]
  rw [e] at this
  linarith [abs_nonneg (Jv H w t v - Jv H w (min t (tL H w v)) v)]

/-- **(Q2)**: `TV(𝒬_w ν) ≤ ∫ |F_ν(v)| (2 + |H'(v/w)|)/(w H(v/w)) dv`. -/
theorem eVariationOn_Qv_le (hH : WidthReg H) {w : ℝ} (hw : 0 < w) {F : ℝ → ℝ} (hF : BM F) :
    eVariationOn (Qv H w F) univ ≤
      ∫⁻ v, ‖F v‖ₑ * ENNReal.ofReal ((2 + |deriv H (v / w)|) / (w * H (v / w))) := by
  have key : ∀ a b, a ≤ b → edist (Qv H w F b) (Qv H w F a) ≤
      ∫⁻ v, ‖F v‖ₑ * ENNReal.ofReal (Mv H w b v - Mv H w a v) := by
    intro a b hab
    rw [edist_eq_enorm_sub]
    unfold Qv
    rw [← integral_sub (integrable_mul_Jv hH hw hF b) (integrable_mul_Jv hH hw hF a)]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun v => ?_)
    rw [← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs (Jv H w b v - Jv H w a v)]
    gcongr
    exact Jv_sub_le hH hw v hab
  have hmeas : ∀ a b, Measurable fun v => ‖F v‖ₑ * ENNReal.ofReal (Mv H w b v - Mv H w a v) :=
    fun a b => hF.1.enorm.mul (((measurable_Mv hH w b).sub (measurable_Mv hH w a)).ennreal_ofReal)
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, -⟩ := p
  calc ∑ i ∈ Finset.range n, edist (Qv H w F (u (i + 1))) (Qv H w F (u i))
      ≤ ∑ i ∈ Finset.range n,
          ∫⁻ v, ‖F v‖ₑ * ENNReal.ofReal (Mv H w (u (i + 1)) v - Mv H w (u i) v) :=
        Finset.sum_le_sum fun i _ => key _ _ (hu (Nat.le_succ i))
    _ = ∫⁻ v, ∑ i ∈ Finset.range n,
          ‖F v‖ₑ * ENNReal.ofReal (Mv H w (u (i + 1)) v - Mv H w (u i) v) :=
        (lintegral_finset_sum _ fun i _ => hmeas _ _).symm
    _ ≤ ∫⁻ v, ‖F v‖ₑ * ENNReal.ofReal ((2 + |deriv H (v / w)|) / (w * H (v / w))) := by
        refine lintegral_mono fun v => ?_
        rw [← Finset.mul_sum]
        gcongr
        have hnn : ∀ i ∈ Finset.range n, 0 ≤ Mv H w (u (i + 1)) v - Mv H w (u i) v := by
          intro i _
          have := Jv_sub_le hH hw v (hu (Nat.le_succ i))
          linarith [abs_nonneg (Jv H w (u (i + 1)) v - Jv H w (u i) v)]
        rw [← ENNReal.ofReal_sum_of_nonneg hnn,
          Finset.sum_range_sub (fun i => Mv H w (u i) v)]
        apply ENNReal.ofReal_le_ofReal
        linarith [Mv_le hH hw (u n) v, Mv_nonneg hH hw (u 0) v]

end KR

end
