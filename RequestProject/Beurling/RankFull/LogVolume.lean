module

public import RequestProject.Beurling.RankFull.PIL

/-!
# Log coordinates for the pivot integrals (Lemma A.2 in logarithmic form)

The integrals of Lemma A.5 are taken over the pivot values `q`. In logarithmic coordinates
`x = log q` the measure `dq/q` becomes Lebesgue measure, which is translation invariant; this is
what makes the substitution of Lemma A.6 (FAC) and the stage identity of Theorem A.10 exact.

* `RankFull.lintegral_log_subst` : `∫_{t>0} f(log t) dt/t = ∫ f(x) dx`;
* `RankFull.lintegral_exp_window` : `∫ e^u 1(d e^u ∈ J) du ≤ vol(J)/d`;
* `RankFull.lintegral_pi_prod` : `∫_{ℝ^k} ∏_i f_i(x_i) dx = ∏_i ∫ f_i`;
* `RankFull.final_volume` : **Lemma A.2 in log coordinates**: for an invertible real matrix `E`,
  `∫_{ℝ^K} ∏_y e^{(Ex)_y} 1(d_y e^{(Ex)_y} ∈ J) dx ≤ |det E|^{-1} ∏_y vol(J)/d_y`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace RankFull

/-- `∫_{t>0} f(log t) dt/t = ∫ f`. -/
theorem lintegral_log_subst (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹ * f (Real.log t)) t =
      ∫⁻ x, f x := by
  rw [lintegral_indicator measurableSet_Ioi]
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  rw [Measure.restrict_univ]
  refine lintegral_congr fun x => ?_
  simp only [Real.log_exp, abs_of_pos (Real.exp_pos x)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos x).le, mul_inv_cancel₀ (Real.exp_pos x).ne',
    ENNReal.ofReal_one, one_mul]

/-- `∫ e^u 1(d e^u ∈ J) du ≤ vol(J)/d`. -/
theorem lintegral_exp_window {d : ℝ} (hd : 0 < d) {J : Set ℝ} (hJ : MeasurableSet J) :
    ∫⁻ u, ENNReal.ofReal (Real.exp u) * J.indicator 1 (d * Real.exp u) ≤
      ENNReal.ofReal d⁻¹ * volume J := by
  have h := lintegral_log_subst
    (fun u => ENNReal.ofReal (Real.exp u) * J.indicator 1 (d * Real.exp u))
  rw [← h]
  have hpt : ∀ t, (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹ *
      (ENNReal.ofReal (Real.exp (Real.log t)) * J.indicator 1 (d * Real.exp (Real.log t)))) t ≤
      ((fun t => d * t) ⁻¹' J).indicator 1 t := by
    intro t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht]
      have ht' : (0 : ℝ) < t := ht
      rw [Real.exp_log ht', ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht'.le),
        inv_mul_cancel₀ ht'.ne', ENNReal.ofReal_one, one_mul]
      by_cases hJt : d * t ∈ J
      · rw [indicator_of_mem hJt, indicator_of_mem (show t ∈ (fun t => d * t) ⁻¹' J from hJt)]
        simp
      · rw [indicator_of_notMem hJt]; exact zero_le
    · rw [indicator_of_notMem ht]; exact zero_le
  refine (lintegral_mono hpt).trans ?_
  have hpre : (fun t => d * t) ⁻¹' J = d⁻¹ • J := by
    ext t
    simp only [mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hd.ne'), inv_inv,
      smul_eq_mul]
  have hmeas : MeasurableSet ((fun t => d * t) ⁻¹' J) := (measurable_const_mul d) hJ
  rw [lintegral_indicator_one hmeas, hpre, Measure.addHaar_smul]
  simp [abs_of_pos (inv_pos.mpr hd)]

/-- `∫_{ℝ^k} ∏_i f_i(x_i) dx = ∏_i ∫ f_i`. -/
theorem lintegral_pi_prod : ∀ {k : ℕ} (f : Fin k → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x : Fin k → ℝ, ∏ i, f i (x i) = ∏ i, ∫⁻ t, f i t
  | 0, f, _ => by rw [lintegral_fin_zero]; simp
  | k + 1, f, hf => by
    have hm : Measurable fun x : Fin (k + 1) → ℝ => ∏ i, f i (x i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lintegral_fin_succ _ hm, Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have ih := lintegral_pi_prod (fun i => f i.succ) (fun i => hf i.succ)
    have : ∀ t, ∫⁻ t' : Fin k → ℝ, f 0 t * ∏ i : Fin k, f i.succ (t' i) =
        f 0 t * ∏ i : Fin k, ∫⁻ s, f i.succ s := by
      intro t
      rw [lintegral_const_mul _ (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)), ih]
    simp_rw [this]
    rw [lintegral_mul_const _ (hf 0)]

/-- **Lemma A.2 in log coordinates**: for an invertible real matrix `E`, cofactors `d_y > 0` and a
measurable window `J`,
`∫_{ℝ^K} ∏_y e^{(Ex)_y} 1(d_y e^{(Ex)_y} ∈ J) dx ≤ |det E|^{-1} ∏_y vol(J)/d_y`. -/
theorem final_volume {K : ℕ} (E : Matrix (Fin K) (Fin K) ℝ) (hE : E.det ≠ 0) (d : Fin K → ℝ)
    (hd : ∀ y, 0 < d y) {J : Set ℝ} (hJ : MeasurableSet J) :
    ∫⁻ x : Fin K → ℝ, ∏ y, ENNReal.ofReal (Real.exp (∑ j, E y j * x j)) *
        J.indicator 1 (d y * Real.exp (∑ j, E y j * x j)) ≤
      ENNReal.ofReal |E.det⁻¹| * ∏ y, (ENNReal.ofReal (d y)⁻¹ * volume J) := by
  set g : (Fin K → ℝ) → ℝ≥0∞ := fun u => ∏ y, ENNReal.ofReal (Real.exp (u y)) *
    J.indicator 1 (d y * Real.exp (u y)) with hg
  have hgy : ∀ y, Measurable fun t : ℝ => ENNReal.ofReal (Real.exp t) *
      J.indicator (1 : ℝ → ℝ≥0∞) (d y * Real.exp t) := fun y =>
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hJ).comp (measurable_const.mul Real.measurable_exp))
  have hgm : Measurable g := Finset.measurable_prod _ fun y _ =>
    (hgy y).comp (measurable_pi_apply y)
  set f := Matrix.toLin' E with hf
  have hfdet : LinearMap.det f ≠ 0 := by rw [hf, LinearMap.det_toLin']; exact hE
  have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional f).measurable
  have hint : (fun x : Fin K → ℝ => ∏ y, ENNReal.ofReal (Real.exp (∑ j, E y j * x j)) *
      J.indicator 1 (d y * Real.exp (∑ j, E y j * x j))) = g ∘ f := by
    funext x
    simp only [hg, Function.comp_apply, hf, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [hint, show lintegral volume (g ∘ ⇑f) = ∫⁻ a, g (f a) from rfl,
    ← lintegral_map hgm hfm, Real.map_linearMap_volume_pi_eq_smul_volume_pi hfdet,
    lintegral_smul_measure, hf, LinearMap.det_toLin', smul_eq_mul]
  gcongr
  rw [hg, lintegral_pi_prod _ hgy]
  exact Finset.prod_le_prod' fun y _ => lintegral_exp_window (hd y) hJ

end RankFull
