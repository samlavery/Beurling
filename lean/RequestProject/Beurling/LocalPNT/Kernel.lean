module

public import RequestProject.Beurling.LocalPNT.Window

/-!
# §5.7: the window of Step 10 and the Perron kernel of Step 9 (Theorem 5.24)

* Bounds for `sinh z / z` and for `∫_{a'}^{b'} e^{sx} dx`.
* The Mellin transform of `φ(u) = ψ(log u)` is the Laplace transform of `ψ`.
* The window `lpWindow v η` of Step 10: `0 ≤ φ ≤ 1`, `φ = 1` on `[v, v(1+η)]`,
  `φ = 0` off `[v(1-w), v(1+η+w)]`, continuity on `(0, ∞)`.
* The Perron kernel `K = 19·1_{[-1/38, 1/38]} * β_{1/38}^{*18}`, shifted to `[-2, -1]`:
  nonnegative, of mass one, continuous, with Laplace transform
  `e^{-3w/2} (sinh(w/38)/(w/38))^{19}` and the bound `76^{19} e^{2|Re w|}/(1+|w|)^{19}`.
-/

@[expose] public section

open Set Real MeasureTheory Complex

open scoped Interval

namespace LocalPNT

/-! ## Bounds for `sinh z / z` and `∫ e^{sx}` -/

section Bounds

lemma norm_boxFactor_le {δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    ‖boxFactor δ s‖ ≤ Real.exp (|s.re| * δ) := by
  have h : ∀ u ∈ Ι (-δ) δ, ‖cexp (s * u)‖ ≤ Real.exp (|s.re| * δ) := by
    intro u hu
    rw [uIoc_of_le (by linarith)] at hu
    rw [Complex.norm_exp, re_mul_ofReal]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hu.1.le, hu.2⟩) (abs_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  have hn : ‖(1 / (2 * δ) : ℂ)‖ = 1 / (2 * δ) := by
    rw [show (1 / (2 * δ) : ℂ) = ((1 / (2 * δ) : ℝ) : ℂ) by push_cast; rfl, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [boxFactor, norm_mul, hn]
  rw [show δ - -δ = 2 * δ by ring, abs_of_pos (by positivity : (0 : ℝ) < 2 * δ)] at this
  calc 1 / (2 * δ) * ‖∫ u in (-δ)..δ, cexp (s * u)‖
      ≤ 1 / (2 * δ) * (Real.exp (|s.re| * δ) * (2 * δ)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.exp (|s.re| * δ) := by field_simp

theorem norm_sinh_div_le (z : ℂ) : ‖Complex.sinh z / z‖ ≤ Real.exp |z.re| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have := norm_boxFactor_le one_pos z
    rw [boxFactor_eq one_pos hz] at this
    simpa using this

lemma norm_sinh_le (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.sinh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have h1 : ‖cexp z‖ ≤ Real.exp |z.re| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (le_abs_self _)
  have h2 : ‖cexp (-z)‖ ≤ Real.exp |z.re| := by
    rw [Complex.norm_exp, neg_re]; exact Real.exp_le_exp.2 (neg_le_abs _)
  have := norm_sub_le (cexp z) (cexp (-z))
  linarith

theorem norm_sinh_div_le' (z : ℂ) :
    ‖Complex.sinh z / z‖ ≤ Real.exp |z.re| / ‖z‖ := by
  rw [norm_div]
  exact div_le_div_of_nonneg_right (norm_sinh_le z) (norm_nonneg _)

theorem norm_integral_cexp_le {a' b' : ℝ} (hab : a' ≤ b') {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∫ x in a'..b', cexp (s * x)‖ ≤ (b' - a') * Real.exp (s.re * b') := by
  have h : ∀ x ∈ Ι a' b', ‖cexp (s * x)‖ ≤ Real.exp (s.re * b') := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    rw [Complex.norm_exp, re_mul_ofReal]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx.2 hs)
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  rw [abs_of_nonneg (by linarith)] at this
  linarith

theorem norm_integral_cexp_le_im {a' b' : ℝ} (hab : a' ≤ b') {s : ℂ} (hs : 0 ≤ s.re)
    (him : s.im ≠ 0) :
    ‖∫ x in a'..b', cexp (s * x)‖ ≤ 2 * Real.exp (s.re * b') / |s.im| := by
  have hs0 : s ≠ 0 := fun h => him (by simp [h])
  rw [integral_exp_mul_complex hs0, norm_div]
  have h1 : ‖cexp (s * b')‖ ≤ Real.exp (s.re * b') := by
    rw [Complex.norm_exp, re_mul_ofReal]
  have h2 : ‖cexp (s * a')‖ ≤ Real.exp (s.re * b') := by
    rw [Complex.norm_exp, re_mul_ofReal]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hab hs)
  have h3 := norm_sub_le (cexp (s * b')) (cexp (s * a'))
  have him' : 0 < |s.im| := abs_pos.2 him
  calc ‖cexp (s * b') - cexp (s * a')‖ / ‖s‖ ≤ 2 * Real.exp (s.re * b') / ‖s‖ :=
        div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ 2 * Real.exp (s.re * b') / |s.im| :=
        div_le_div_of_nonneg_left (by positivity) him' (abs_im_le_norm s)

end Bounds

/-! ## The Mellin transform of `ψ ∘ log` -/

/-- `∫_0^∞ ψ(log u) u^{s-1} du = ∫ ψ(x) e^{sx} dx` (the substitution `u = e^x`). -/
theorem integral_Ioi_comp_log (ψ : ℝ → ℝ) (s : ℂ) :
    ∫ u in Ioi 0, ((if 0 < u then ψ (Real.log u) else 0 : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) =
      ∫ x, (ψ x : ℂ) * cexp (s * x) := by
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  congr 1
  funext x
  rw [if_pos (Real.exp_pos x), Real.log_exp, abs_of_pos (Real.exp_pos x), real_smul,
    cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'), ← ofReal_log (Real.exp_pos x).le,
    Real.log_exp, ofReal_exp]
  rw [mul_left_comm, ← Complex.exp_add]
  ring_nf

/-- The Mellin form of the window `φ(u) = ψ(log u)`. -/
theorem windowLog_mellin (a b ω : ℝ) (k : ℕ) (s : ℂ) :
    ∫ u in Ioi 0, ((if 0 < u then windowLog a b ω k (Real.log u) else 0 : ℝ) : ℂ) *
        (u : ℂ) ^ (s - 1) =
      ∫ x, (windowLog a b ω k x : ℂ) * cexp (s * x) :=
  integral_Ioi_comp_log _ s

/-! ## The window of Step 10 -/

section LpWindow

variable {v η : ℝ}

lemma lpW_pos (hv : 1 ≤ Real.log v) (hη : 0 < η) : 0 < lpW v η := by
  unfold lpW; positivity

lemma lpW_le (hv : 1 ≤ Real.log v) (hη : 0 < η) : lpW v η ≤ η := by
  unfold lpW
  exact div_le_self hη.le (one_le_pow₀ hv)

lemma one_le_lpK (hv : 1 ≤ Real.log v) (hη : 0 < η) (hη' : η ≤ 1 / 2) : 1 ≤ lpK v η := by
  unfold lpK
  have h1 : 0 < Real.log (1 / η) := Real.log_pos (one_lt_one_div hη (by linarith))
  have h2 : 0 ≤ Real.log (Real.log v) := Real.log_nonneg hv
  exact Nat.one_le_iff_ne_zero.2 fun h => by
    rw [Nat.ceil_eq_zero] at h; linarith

lemma lpWindow_props (hv1 : 1 < v) (hv : 1 ≤ Real.log v) (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    (∀ x, 0 ≤ windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η) x ∧
      windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η) x ≤ 1) ∧
    (∀ x ∈ Icc (Real.log v) (Real.log (v * (1 + η))),
      windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η) x = 1) ∧
    (∀ x, windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η) x ≠ 0 →
      x ∈ Icc (Real.log v - 2 * (lpW v η / 4)) (Real.log (v * (1 + η)) + 2 * (lpW v η / 4))) ∧
    Continuous (windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η)) :=
  windowLog_props (Real.log_le_log (by linarith) (by nlinarith))
    (by have := lpW_pos hv hη; positivity) (one_le_lpK hv hη hη')

theorem lpWindow_bounds (hv1 : 1 < v) (hv : 1 ≤ Real.log v) (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (u : ℝ) : 0 ≤ lpWindow v η u ∧ lpWindow v η u ≤ 1 := by
  unfold lpWindow
  split_ifs
  · exact (lpWindow_props hv1 hv hη hη').1 _
  · simp

theorem lpWindow_eq_one (hv1 : 1 < v) (hv : 1 ≤ Real.log v) (hη : 0 < η) (hη' : η ≤ 1 / 2)
    {u : ℝ} (hu : u ∈ Icc v (v * (1 + η))) : lpWindow v η u = 1 := by
  have hu0 : 0 < u := by linarith [hu.1]
  rw [lpWindow, if_pos ⟨hu0, by linarith⟩]
  exact (lpWindow_props hv1 hv hη hη').2.1 _
    ⟨Real.log_le_log (by linarith) hu.1, Real.log_le_log hu0 hu.2⟩

theorem lpWindow_support (hv1 : 1 < v) (hv : 1 ≤ Real.log v) (hη : 0 < η) (hη' : η ≤ 1 / 2)
    {u : ℝ} (hu : lpWindow v η u ≠ 0) :
    u ∈ Icc (v * (1 - lpW v η)) (v * (1 + η + lpW v η)) := by
  unfold lpWindow at hu
  split_ifs at hu with hu0
  · replace hu0 := hu0.1
    have hw := lpW_pos hv hη
    have hwη := lpW_le hv hη
    set w := lpW v η
    have h := (lpWindow_props hv1 hv hη hη').2.2.1 _ hu
    have hv0 : 0 < v := by linarith
    have hv' : 0 < v * (1 + η) := by positivity
    have hlo : Real.log v - w / 2 ≤ Real.log u := by linarith [h.1]
    have hhi : Real.log u ≤ Real.log (v * (1 + η)) + w / 2 := by linarith [h.2]
    constructor
    · have : v * Real.exp (-(w / 2)) ≤ u := by
        rw [← Real.exp_log hu0, ← Real.exp_log hv0, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      have he := Real.add_one_le_exp (-(w / 2))
      nlinarith
    · have : u ≤ v * (1 + η) * Real.exp (w / 2) := by
        rw [← Real.exp_log hu0, ← Real.exp_log hv', ← Real.exp_add]
        exact Real.exp_le_exp.2 hhi
      have he : Real.exp (w / 2) ≤ 1 + w / 2 + (w / 2) ^ 2 := by
        have := Real.abs_exp_sub_one_sub_id_le (x := w / 2)
          (by rw [abs_of_pos (by positivity)]; linarith)
        linarith [(abs_le.1 this).2]
      have : (1 + η) * Real.exp (w / 2) ≤ 1 + η + w := by
        calc (1 + η) * Real.exp (w / 2) ≤ (1 + η) * (1 + w / 2 + (w / 2) ^ 2) :=
              mul_le_mul_of_nonneg_left he (by linarith)
          _ ≤ 1 + η + w := by nlinarith
      calc u ≤ v * ((1 + η) * Real.exp (w / 2)) := by linarith
        _ ≤ v * (1 + η + w) := mul_le_mul_of_nonneg_left this hv0.le
  · exact absurd rfl hu

theorem continuousOn_lpWindow (hv1 : 1 < v) (hv : 1 ≤ Real.log v) (hη : 0 < η)
    (hη' : η ≤ 1 / 2) : ContinuousOn (lpWindow v η) (Ioi 0) := by
  have hc := (lpWindow_props hv1 hv hη hη').2.2.2
  refine ((hc.comp_continuousOn (Real.continuousOn_log.mono fun x hx => ?_))).congr
    fun u hu => ?_
  · exact (ne_of_gt (mem_Ioi.1 hx))
  · simp [lpWindow, mem_Ioi.1 hu, show 0 < v by linarith]

end LpWindow

/-! ## The Perron kernel of Step 9 -/

section Perron

/-- The kernel `19·1_{[-1/38, 1/38]} * β_{1/38}^{*18}` of Step 9, translated to `[-2, -1]`. -/
noncomputable def perronKernel (x : ℝ) : ℝ :=
  (boxAvg (1 / 38))^[18] ((Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => 19)) (x + 3 / 2)

/-- The unshifted kernel. -/
private noncomputable def perronBase : ℝ → ℝ :=
  (boxAvg (1 / 38))^[18] ((Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => 19))

private lemma perronInit_props :
    Measurable ((Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => (19 : ℝ))) ∧
      (∀ x, 0 ≤ (Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => (19 : ℝ)) x ∧
        (Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => (19 : ℝ)) x ≤ 19) ∧
      (∀ x, (Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => (19 : ℝ)) x ≠ 0 →
        x ∈ Icc (-(1 / 38 : ℝ)) (1 / 38)) := by
  refine ⟨measurable_const.indicator measurableSet_Icc, fun x => ?_, fun x hx => ?_⟩
  · simp only [indicator_apply]; split_ifs <;> norm_num
  · by_contra h; exact hx (indicator_of_notMem h _)

private lemma perronBase_props :
    (∀ x, 0 ≤ perronBase x ∧ perronBase x ≤ 19) ∧
      (∀ x, perronBase x ≠ 0 → x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧ Continuous perronBase := by
  obtain ⟨h1, h2, h3⟩ := perronInit_props
  obtain ⟨-, i2, i3⟩ := iterate_boxAvg_props (by norm_num : (0 : ℝ) < 1 / 38) h1 h2 h3 18
  refine ⟨i2, fun x hx => ?_, continuous_iterate_boxAvg (by norm_num) h1 h2 h3 (by norm_num)⟩
  have := i3 x hx
  norm_num at this ⊢
  exact this

private lemma perronBase_laplace (w : ℂ) :
    ∫ x, (perronBase x : ℂ) * cexp (w * x) = boxFactor (1 / 38) w ^ 19 := by
  obtain ⟨h1, h2, h3⟩ := perronInit_props
  rw [perronBase, laplace_iterate_boxAvg (by norm_num) h1 h2 h3, pow_succ]
  congr 1
  have : (fun x : ℝ => (((Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator (fun _ => (19 : ℝ)) x : ℝ) :
      ℂ) * cexp (w * x)) = (Icc (-(1 / 38 : ℝ)) (1 / 38)).indicator fun x => 19 * cexp (w * x) := by
    funext x
    simp only [indicator_apply]; split_ifs <;> simp
  rw [this, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    boxFactor]
  push_cast
  ring

theorem perronKernel_nonneg (x : ℝ) : 0 ≤ perronKernel x :=
  (perronBase_props.1 _).1

theorem perronKernel_support {x : ℝ} (hx : perronKernel x ≠ 0) : x ∈ Icc (-2 : ℝ) (-1) := by
  have := perronBase_props.2.1 _ hx
  simp only [mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem continuous_perronKernel : Continuous perronKernel :=
  perronBase_props.2.2.comp (continuous_add_const _)

/-- The Laplace transform of the Perron kernel in terms of `boxFactor`. -/
theorem perronKernel_laplace_boxFactor (w : ℂ) :
    ∫ x, (perronKernel x : ℂ) * cexp (w * x) =
      cexp (-(3 / 2) * w) * boxFactor (1 / 38) w ^ 19 := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => (perronBase y : ℂ) * cexp (w * y) * cexp (-(3 / 2) * w)) (3 / 2 : ℝ)
  have h' : (fun x : ℝ => (perronKernel x : ℂ) * cexp (w * x)) =
      fun x : ℝ => (perronBase (x + 3 / 2) : ℂ) * cexp (w * ↑(x + 3 / 2)) *
        cexp (-(3 / 2) * w) := by
    funext x
    rw [mul_assoc, ← Complex.exp_add]
    simp only [perronKernel, perronBase]
    congr 2
    push_cast
    ring
  rw [h', h, integral_mul_const, perronBase_laplace, mul_comm]

theorem integral_perronKernel : ∫ x, perronKernel x = 1 := by
  have := perronKernel_laplace_boxFactor 0
  simp only [zero_mul, Complex.exp_zero, mul_one, mul_zero, boxFactor_zero
    (by norm_num : (0 : ℝ) < 1 / 38), one_pow] at this
  rw [integral_complex_ofReal] at this
  exact_mod_cast this

theorem perronKernel_laplace {w : ℂ} (hw : w ≠ 0) :
    ∫ x, (perronKernel x : ℂ) * cexp (w * x) =
      cexp (-(3 / 2) * w) * (Complex.sinh (w / 38) / (w / 38)) ^ 19 := by
  rw [perronKernel_laplace_boxFactor, boxFactor_eq (by norm_num) hw]
  push_cast
  ring_nf

theorem perronKernel_laplace_zero :
    ∫ x, (perronKernel x : ℂ) * cexp (0 * x) = 1 := by
  rw [perronKernel_laplace_boxFactor, boxFactor_zero (by norm_num)]
  simp

lemma norm_boxFactor_perron_le (w : ℂ) :
    ‖boxFactor (1 / 38) w‖ ≤ Real.exp (|w.re| / 38) * (76 / (1 + ‖w‖)) := by
  have h1 := norm_boxFactor_le (by norm_num : (0 : ℝ) < 1 / 38) w
  rw [show |w.re| * (1 / 38) = |w.re| / 38 by ring] at h1
  have hE := Real.exp_pos (|w.re| / 38)
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · refine h1.trans (le_mul_of_one_le_right hE.le ?_)
    rw [le_div_iff₀ (by positivity)]; linarith
  · have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
    have h2 := norm_sinh_div_le' (w / 38)
    rw [← show boxFactor (1 / 38) w = Complex.sinh (w / 38) / (w / 38) by
      rw [boxFactor_eq (by norm_num) hw0]; push_cast; ring_nf] at h2
    rw [norm_div, show ‖(38 : ℂ)‖ = 38 by simp, show (w / 38).re = w.re / 38 by simp,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 38)] at h2
    refine h2.trans ?_
    rw [div_div_eq_mul_div]
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hE.le
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

theorem norm_perronKernel_laplace_le (w : ℂ) :
    ‖∫ x, (perronKernel x : ℂ) * cexp (w * x)‖ ≤
      76 ^ 19 * Real.exp (2 * |w.re|) / (1 + ‖w‖) ^ 19 := by
  rw [perronKernel_laplace_boxFactor, norm_mul, norm_pow, Complex.norm_exp]
  have h1 : (-(3 / 2) * w).re ≤ 3 / 2 * |w.re| := by
    simp only [neg_mul, neg_re, mul_re]
    norm_num
    linarith [neg_abs_le w.re]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_boxFactor_perron_le w) 19
  have hpos : 0 < 1 + ‖w‖ := by positivity
  calc Real.exp (-(3 / 2) * w).re * ‖boxFactor (1 / 38) w‖ ^ 19
      ≤ Real.exp (3 / 2 * |w.re|) * (Real.exp (|w.re| / 38) * (76 / (1 + ‖w‖))) ^ 19 :=
        mul_le_mul (Real.exp_le_exp.2 h1) h2 (by positivity) (by positivity)
    _ = 76 ^ 19 * Real.exp (2 * |w.re|) / (1 + ‖w‖) ^ 19 := by
        have : Real.exp (2 * |w.re|) =
            Real.exp (3 / 2 * |w.re|) * Real.exp (|w.re| / 38) ^ 19 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
        rw [this, mul_pow, div_pow]
        ring

theorem seventysix_pow_le_exp : (76 : ℝ) ^ 19 ≤ Real.exp 82.3 := by
  have he : (2.7182818283 : ℝ) ^ 82 ≤ Real.exp 1 ^ 82 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 82
  have h3 : 1 + 0.3 + (0.3 : ℝ) ^ 2 / 2 ≤ Real.exp 0.3 := Real.quadratic_le_exp_of_nonneg
    (by norm_num)
  rw [show (82.3 : ℝ) = ((82 : ℕ) : ℝ) * 1 + 0.3 by norm_num, Real.exp_add, Real.exp_nat_mul]
  calc (76 : ℝ) ^ 19 ≤ 2.7182818283 ^ 82 * (1 + 0.3 + 0.3 ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 1 ^ 82 * Real.exp 0.3 := mul_le_mul he h3 (by norm_num) (by positivity)

end Perron

end LocalPNT

end
