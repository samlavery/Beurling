module

public import Mathlib

/-!
# A mean square bound for Fourier integrals over a bounded interval

For a bounded measurable `G` on `[α, β]` (`L = β - α`) and `T > 0` with `L T ≥ 1`,

  `∫_{T₀}^{T₀+T} |∫_α^β G(u) e^{-itu} du|² dt ≤ (4 + 4 log(L T)) ∫_α^β |G(u)|² du`

(`fourier_mean_square`). This is a substitute, with a logarithmic loss, for the Plancherel
estimate used in the paper for the `ρ̄_A` part in the proof of Lemma 4.8(ii). The proof expands
the square, integrates in `t` first, bounds the kernel `|∫ e^{-it w} dt| ≤ min(T, 2/|w|)`, and
applies the Schur test.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace FourierMS

/-- The majorant of the kernel `|∫_{T₀}^{T₀+T} e^{-itw} dt|`. -/
noncomputable def kmaj (T w : ℝ) : ℝ := if |w| < 1 / T then T else 2 / |w|

lemma kmaj_nonneg {T : ℝ} (hT : 0 < T) (w : ℝ) : 0 ≤ kmaj T w := by
  unfold kmaj; split_ifs <;> positivity

lemma kmaj_le {T : ℝ} (hT : 0 < T) (w : ℝ) : kmaj T w ≤ 2 * T := by
  unfold kmaj
  split_ifs with h
  · linarith
  · push_neg at h
    have hw : 0 < |w| := lt_of_lt_of_le (by positivity) h
    rw [div_le_iff₀ hw]
    have := mul_le_mul_of_nonneg_left h (le_of_lt hT)
    rw [mul_one_div_cancel hT.ne'] at this
    linarith

lemma kmaj_neg (T w : ℝ) : kmaj T (-w) = kmaj T w := by
  simp [kmaj, abs_neg]

lemma measurable_kmaj (T : ℝ) : Measurable (kmaj T) := by
  unfold kmaj
  refine Measurable.ite ?_ measurable_const (measurable_const.div measurable_id.abs)
  exact measurableSet_lt measurable_id.abs measurable_const

/-- The kernel bound `|∫_{T₀}^{T₀+T} e^{-itw} dt| ≤ kmaj T w`. -/
lemma norm_kernel_le {T : ℝ} (hT : 0 < T) (T₀ w : ℝ) :
    ‖∫ t in T₀..T₀ + T, cexp (-(I * t * w))‖ ≤ kmaj T w := by
  have hnorm : ∀ t : ℝ, ‖cexp (-(I * t * w))‖ = 1 := by
    intro t
    rw [show -(I * (t : ℂ) * (w : ℂ)) = ((-(t * w) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  unfold kmaj
  split_ifs with h
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T₀) (b := T₀ + T)
      (C := 1) (f := fun t : ℝ => cexp (-(I * t * w))) (fun t _ => (hnorm t).le)
    rw [show T₀ + T - T₀ = T by ring, abs_of_pos hT, one_mul] at this
    exact this
  · push_neg at h
    have hw : 0 < |w| := lt_of_lt_of_le (by positivity) h
    have hw0 : w ≠ 0 := abs_pos.mp hw
    have hc : (-I * (w : ℂ)) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by exact_mod_cast hw0)
    have e : ∀ t : ℝ, cexp (-(I * t * w)) = cexp ((-I * w) * t) := fun t => by ring_nf
    simp only [e]
    rw [integral_exp_mul_complex hc, norm_div]
    have hden : ‖-I * (w : ℂ)‖ = |w| := by simp
    rw [hden, div_le_div_iff_of_pos_right hw]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ∀ t : ℝ, ‖cexp ((-I * w) * t)‖ = 1 := fun t => by rw [← e]; exact hnorm t
    rw [h1, h1]; norm_num

/-- The Schur bound: `∫_α^β kmaj T (u - v) dv ≤ 4 + 4 log (L T)` for `u ∈ [α, β]`. -/
lemma integral_kmaj_le {T α β : ℝ} (hT : 0 < T) (hαβ : α ≤ β) (hLT : 1 ≤ (β - α) * T)
    {u : ℝ} (hu : u ∈ Icc α β) :
    ∫ v in Icc α β, kmaj T (u - v) ≤ 4 + 4 * Real.log ((β - α) * T) := by
  set L := β - α
  have hL : 1 / T ≤ L := by rw [div_le_iff₀ hT]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hii : ∀ a b : ℝ, IntervalIntegrable (kmaj T) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := 2 * T)).mono_fun
      (measurable_kmaj T).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    show ‖kmaj T w‖ ≤ ‖2 * T‖
    rw [Real.norm_of_nonneg (kmaj_nonneg hT w), Real.norm_of_nonneg (by positivity)]
    exact kmaj_le hT w
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hαβ,
    intervalIntegral.integral_comp_sub_left (fun w => kmaj T w) u]
  have hnn : ∀ a b : ℝ, 0 ≤ᶠ[ae (volume.restrict (Ioc a b))] kmaj T :=
    fun a b => Filter.Eventually.of_forall fun w => kmaj_nonneg hT w
  have h1 : ∫ w in u - β..u - α, kmaj T w ≤ ∫ w in -L..L, kmaj T w :=
    intervalIntegral.integral_mono_interval (by linarith [hu.1]) (by linarith)
      (by linarith [hu.2]) (hnn _ _) (hii _ _)
  have hsplit : ∫ w in -L..L, kmaj T w = 2 * ∫ w in (0:ℝ)..L, kmaj T w := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-L) 0) (hii 0 L)]
    have : ∫ w in -L..0, kmaj T w = ∫ w in (0:ℝ)..L, kmaj T w := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := L) (fun w => kmaj T w)
      simp only [kmaj_neg, neg_zero] at this
      rw [this]
    rw [this]; ring
  have h2 : ∫ w in (0:ℝ)..L, kmaj T w ≤ 2 + 2 * Real.log (L * T) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (1 / T)) (hii (1 / T) L)]
    have ha : ∫ w in (0:ℝ)..1 / T, kmaj T w ≤ ∫ w in (0:ℝ)..1 / T, 2 * T :=
      intervalIntegral.integral_mono_on (by positivity) (hii _ _) intervalIntegrable_const
        (fun w _ => kmaj_le hT w)
    have hb : ∫ w in 1 / T..L, kmaj T w ≤ ∫ w in 1 / T..L, 2 * w⁻¹ := by
      apply intervalIntegral.integral_mono_on hL (hii _ _)
      · exact (intervalIntegral.intervalIntegrable_inv (fun w hw => by
          have := hw.1; rw [uIcc_of_le hL] at hw; have := hw.1
          exact (lt_of_lt_of_le (by positivity) this).ne') continuousOn_id).const_mul 2
      · intro w hw
        have hw1 : 1 / T ≤ w := hw.1
        have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw1
        unfold kmaj
        rw [if_neg (by rw [abs_of_pos hw0]; linarith), abs_of_pos hw0, div_eq_mul_inv]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by positivity) hL0] at *
    simp only [smul_eq_mul] at ha
    have e1 : (1 / T - 0) * (2 * T) = 2 := by field_simp; ring
    have e2 : L / (1 / T) = L * T := by field_simp
    rw [e1] at ha; rw [e2] at hb
    linarith
  rw [hsplit] at h1
  linarith

lemma norm_cexp_neg_I_mul (t u : ℝ) : ‖cexp (-(I * t * u))‖ = 1 := by
  rw [show -(I * (t : ℂ) * (u : ℂ)) = ((-(t * u) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma fourier_mean_square_aux {G : ℝ → ℂ} (hG : Measurable G) {α β M : ℝ} (hαβ : α ≤ β)
    (hM : ∀ u, ‖G u‖ ≤ M) {T : ℝ} (hT : 0 < T) (hLT : 1 ≤ (β - α) * T) (T₀ : ℝ) :
    ∫ t in Icc T₀ (T₀ + T), ‖∫ u in Icc α β, G u * cexp (-(I * t * u))‖ ^ 2 ≤
      (4 + 4 * Real.log ((β - α) * T)) * ∫ u in Icc α β, ‖G u‖ ^ 2 := by
  set μ : Measure ℝ := volume.restrict (Icc α β)
  set τ : Measure ℝ := volume.restrict (Icc T₀ (T₀ + T))
  set ν : Measure (ℝ × ℝ) := μ.prod μ
  set C := 4 + 4 * Real.log ((β - α) * T)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set H : ℝ → ℝ × ℝ → ℂ := fun t p => G p.1 * conj (G p.2) * cexp (-(I * t * (p.1 - p.2)))
  have hHm : Measurable (Function.uncurry H) := by
    have h1 : Measurable fun q : ℝ × (ℝ × ℝ) => G q.2.1 := hG.comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable fun q : ℝ × (ℝ × ℝ) => conj (G q.2.2) :=
      Complex.continuous_conj.measurable.comp (hG.comp (measurable_snd.comp measurable_snd))
    have h3 : Measurable fun q : ℝ × (ℝ × ℝ) => cexp (-(I * q.1 * (q.2.1 - q.2.2))) := by
      apply Continuous.measurable; fun_prop
    exact (h1.mul h2).mul h3
  have hHb : ∀ t p, ‖H t p‖ ≤ M * M := by
    intro t p
    simp only [H, norm_mul, Complex.norm_conj]
    rw [show ((p.1 : ℂ) - p.2) = ((p.1 - p.2 : ℝ) : ℂ) by push_cast; ring, norm_cexp_neg_I_mul,
      mul_one]
    exact mul_le_mul (hM _) (hM _) (norm_nonneg _) hM0
  -- step A: expanding the square
  have hA : ∀ t : ℝ, ((‖∫ u, G u * cexp (-(I * t * u)) ∂μ‖ ^ 2 : ℝ) : ℂ) = ∫ p, H t p ∂ν := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← integral_conj]
    rw [← integral_prod_mul (μ := μ) (ν := μ) (fun u => G u * cexp (-(I * t * u)))
      (fun v => conj (G v * cexp (-(I * t * v))))]
    congr 1; funext p
    simp only [H, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal]
    rw [show G p.1 * cexp (-(I * t * p.1)) * (conj (G p.2) * cexp (-(-I * t * p.2))) =
      G p.1 * conj (G p.2) * (cexp (-(I * t * p.1)) * cexp (-(-I * t * p.2))) by ring,
      ← Complex.exp_add]
    congr 2; ring
  -- step C: the kernel
  set K : ℝ → ℂ := fun w => ∫ t in Icc T₀ (T₀ + T), cexp (-(I * t * w))
  have hK : ∀ w, ‖K w‖ ≤ kmaj T w := by
    intro w
    simp only [K]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact norm_kernel_le hT T₀ w
  have hC : ∀ p : ℝ × ℝ, ∫ t, H t p ∂τ = G p.1 * conj (G p.2) * K (p.1 - p.2) := by
    intro p
    simp only [H, K]
    rw [integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by push_cast; rfl
  -- integrability
  haveI : IsFiniteMeasure μ := by
    simp only [μ]; exact isFiniteMeasure_restrict.mpr (measure_Icc_lt_top).ne
  haveI : IsFiniteMeasure τ := by
    simp only [τ]; exact isFiniteMeasure_restrict.mpr (measure_Icc_lt_top).ne
  have hInt : Integrable (Function.uncurry H) (τ.prod ν) :=
    Integrable.mono' (integrable_const (M * M)) hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hHb q.1 q.2)
  -- step B: Fubini
  have hB : ((∫ t, ‖∫ u, G u * cexp (-(I * t * u)) ∂μ‖ ^ 2 ∂τ : ℝ) : ℂ) =
      ∫ p, G p.1 * conj (G p.2) * K (p.1 - p.2) ∂ν := by
    rw [← integral_complex_ofReal]
    simp only [hA]
    rw [integral_integral_swap hInt]
    exact integral_congr_ae (Filter.Eventually.of_forall hC)
  -- step D: Schur
  set g : ℝ × ℝ → ℝ := fun p => (‖G p.1‖ ^ 2 + ‖G p.2‖ ^ 2) / 2 * kmaj T (p.1 - p.2)
  have hkm : Measurable fun p : ℝ × ℝ => kmaj T (p.1 - p.2) :=
    (measurable_kmaj T).comp (measurable_fst.sub measurable_snd)
  have hg1m : Measurable fun p : ℝ × ℝ => ‖G p.1‖ ^ 2 * kmaj T (p.1 - p.2) :=
    ((hG.comp measurable_fst).norm.pow_const 2).mul hkm
  have hg2m : Measurable fun p : ℝ × ℝ => ‖G p.2‖ ^ 2 * kmaj T (p.1 - p.2) :=
    ((hG.comp measurable_snd).norm.pow_const 2).mul hkm
  have hbd : ∀ (x : ℝ) (p : ℝ × ℝ), ‖‖G x‖ ^ 2 * kmaj T (p.1 - p.2)‖ ≤ M ^ 2 * (2 * T) := by
    intro x p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (kmaj_nonneg hT _))]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hM x) 2) (kmaj_le hT _)
      (kmaj_nonneg hT _) (sq_nonneg _)
  have hg1 : Integrable (fun p : ℝ × ℝ => ‖G p.1‖ ^ 2 * kmaj T (p.1 - p.2)) ν :=
    Integrable.mono' (integrable_const _) hg1m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hbd p.1 p)
  have hg2 : Integrable (fun p : ℝ × ℝ => ‖G p.2‖ ^ 2 * kmaj T (p.1 - p.2)) ν :=
    Integrable.mono' (integrable_const _) hg2m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hbd p.2 p)
  have hgint : Integrable g ν := by
    have := (hg1.add hg2).div_const 2
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [g, Pi.add_apply]; ring
  have hD1 : ‖∫ p, G p.1 * conj (G p.2) * K (p.1 - p.2) ∂ν‖ ≤ ∫ p, g p ∂ν := by
    refine norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall fun p => ?_)
    simp only [g, norm_mul, Complex.norm_conj]
    have h1 := hK (p.1 - p.2)
    have h2 : ‖G p.1‖ * ‖G p.2‖ ≤ (‖G p.1‖ ^ 2 + ‖G p.2‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖G p.1‖ - ‖G p.2‖)]
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
  have hSchur : ∀ u ∈ Icc α β, ∫ v, kmaj T (u - v) ∂μ ≤ C := fun u hu =>
    integral_kmaj_le hT hαβ hLT hu
  have hSchur' : ∀ v ∈ Icc α β, ∫ u, kmaj T (u - v) ∂μ ≤ C := by
    intro v hv
    have := integral_kmaj_le hT hαβ hLT hv
    refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)) this
    show kmaj T (u - v) = kmaj T (v - u)
    rw [← kmaj_neg, neg_sub]
  have hkint : ∀ x : ℝ, Integrable (fun y => kmaj T (x - y)) μ := fun x =>
    Integrable.mono' (integrable_const (2 * T))
      ((measurable_kmaj T).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (kmaj_nonneg hT _)]; exact kmaj_le hT _)
  have hkint' : ∀ y : ℝ, Integrable (fun x => kmaj T (x - y)) μ := fun y =>
    Integrable.mono' (integrable_const (2 * T))
      ((measurable_kmaj T).comp (measurable_id.sub measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (kmaj_nonneg hT _)]; exact kmaj_le hT _)
  have hGint : Integrable (fun u => ‖G u‖ ^ 2) μ :=
    Integrable.mono' (integrable_const (M ^ 2)) (hG.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hM u) 2)
  have hE1 : ∫ p, ‖G p.1‖ ^ 2 * kmaj T (p.1 - p.2) ∂ν ≤ C * ∫ u, ‖G u‖ ^ 2 ∂μ := by
    rw [integral_prod _ hg1, ← integral_const_mul]
    refine integral_mono_ae ?_ (hGint.const_mul C) ?_
    · exact hg1.integral_prod_left
    · refine (ae_restrict_mem measurableSet_Icc).mono fun u hu => ?_
      simp only
      rw [integral_const_mul]
      have := hSchur u hu
      have h0 : 0 ≤ ‖G u‖ ^ 2 := sq_nonneg _
      nlinarith
  have hE2 : ∫ p, ‖G p.2‖ ^ 2 * kmaj T (p.1 - p.2) ∂ν ≤ C * ∫ u, ‖G u‖ ^ 2 ∂μ := by
    rw [integral_prod_symm _ hg2, ← integral_const_mul]
    refine integral_mono_ae ?_ (hGint.const_mul C) ?_
    · exact hg2.integral_prod_right
    · refine (ae_restrict_mem measurableSet_Icc).mono fun v hv => ?_
      simp only
      rw [integral_const_mul]
      have := hSchur' v hv
      have h0 : 0 ≤ ‖G v‖ ^ 2 := sq_nonneg _
      nlinarith
  have hgsplit : ∫ p, g p ∂ν = (∫ p, ‖G p.1‖ ^ 2 * kmaj T (p.1 - p.2) ∂ν +
      ∫ p, ‖G p.2‖ ^ 2 * kmaj T (p.1 - p.2) ∂ν) / 2 := by
    rw [← integral_add hg1 hg2, ← integral_div]
    congr 1; funext p; simp only [g]; ring
  -- conclusion
  have key : ∫ t, ‖∫ u, G u * cexp (-(I * t * u)) ∂μ‖ ^ 2 ∂τ ≤
      ‖∫ p, G p.1 * conj (G p.2) * K (p.1 - p.2) ∂ν‖ := by
    rw [← hB, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  calc ∫ t, ‖∫ u, G u * cexp (-(I * t * u)) ∂μ‖ ^ 2 ∂τ ≤ ∫ p, g p ∂ν := key.trans hD1
    _ ≤ C * ∫ u, ‖G u‖ ^ 2 ∂μ := by rw [hgsplit]; linarith

/-- **Mean square bound for Fourier integrals over a bounded interval.** For a measurable `G`
bounded on `[α, β]`, `T > 0` with `(β - α) T ≥ 1`, and any `T₀`,
`∫_{T₀}^{T₀+T} |∫_α^β G(u) e^{-itu} du|² dt ≤ (4 + 4 log((β - α) T)) ∫_α^β |G(u)|² du`. -/
theorem fourier_mean_square {G : ℝ → ℂ} (hG : Measurable G) {α β M : ℝ} (hαβ : α ≤ β)
    (hM : ∀ u ∈ Icc α β, ‖G u‖ ≤ M) {T : ℝ} (hT : 0 < T) (hLT : 1 ≤ (β - α) * T) (T₀ : ℝ) :
    ∫ t in Icc T₀ (T₀ + T), ‖∫ u in Icc α β, G u * cexp (-(I * t * u))‖ ^ 2 ≤
      (4 + 4 * Real.log ((β - α) * T)) * ∫ u in Icc α β, ‖G u‖ ^ 2 := by
  set G' := (Icc α β).indicator G
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM α ⟨le_rfl, hαβ⟩)
  have hG' : Measurable G' := hG.indicator measurableSet_Icc
  have hM' : ∀ u, ‖G' u‖ ≤ M := by
    intro u
    by_cases hu : u ∈ Icc α β
    · simp only [G', indicator_of_mem hu]; exact hM u hu
    · simp only [G', indicator_of_notMem hu, norm_zero]; exact hM0
  have h := fourier_mean_square_aux hG' hαβ hM' hT hLT T₀
  have e1 : ∀ t : ℝ, ∫ u in Icc α β, G' u * cexp (-(I * t * u)) =
      ∫ u in Icc α β, G u * cexp (-(I * t * u)) := fun t =>
    setIntegral_congr_fun measurableSet_Icc fun u hu => by simp only [G', indicator_of_mem hu]
  have e2 : ∫ u in Icc α β, ‖G' u‖ ^ 2 = ∫ u in Icc α β, ‖G u‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_Icc fun u hu => by simp only [G', indicator_of_mem hu]
  simp only [e1, e2] at h
  exact h

end FourierMS

end
