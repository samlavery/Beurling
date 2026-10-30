module

public import RequestProject.Beurling.RankFull.MultiRun

/-!
# The cover version of the pending integrand (Proposition 6.19)

For a cover `C` of the rows (`Cd`), the pending integrand of the recursion carries the density
`∏_{y ∈ C} e^{⟨E_y, x⟩}` of the rows of `C` only (the caps are replaced by
`∏_i (q_i/τ_i)^{e_i}`, `e_i = s^C_i - 1`), while every row keeps its window indicator:
`L^C(x, c) = ∏_{y ∈ C} e^{⟨E_y,x⟩} · ∏_y 1(c_y e^{⟨E_y,x⟩} ∈ J)` (`LcoreC`).

* `RankFull.LcoreC_shift`, `RankFull.lintegral_LcoreC_shift` : (FAC) with the weight of the rows
  of `C`, `∏_g q_g^{-a^C_g}`, `a^C_g = ∑_{y ∈ C} w_{yg}`;
* `RankFull.lintegral_exp_window_z` : a row outside `C` contributes `∫ 1(d e^u ∈ J) du ≤ vol(J)/z`
  for a window `J ⊆ [z, ∞)`;
* `RankFull.final_volumeC` : the end of the recursion,
  `∫ L^C(x, d) dx ≤ |det E|^{-1} ∏_{y ∈ C} vol(J)/d_y · (vol(J)/z)^{|R|}`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal Pointwise

namespace RankFull

variable {K N : ℕ}

/-- The cover integrand `L^C(x, c)`. -/
noncomputable def LcoreC (E : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (Cd : Finset (Fin K))
    (cv : Fin K → ℝ) (x : Fin K → ℝ) : ℝ≥0∞ :=
  (∏ y ∈ Cd, ENNReal.ofReal (Real.exp (rowLog E x y))) *
    ∏ y, Jw.indicator 1 (cv y * Real.exp (rowLog E x y))

lemma measurable_LcoreC2 (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    (Cd : Finset (Fin K)) :
    Measurable fun p : (Fin K → ℝ) × (Fin K → ℝ) => LcoreC E Jw Cd p.1 p.2 := by
  unfold LcoreC
  have hr : ∀ y, Measurable fun p : (Fin K → ℝ) × (Fin K → ℝ) => rowLog E p.2 y := fun y =>
    Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)
  refine (Finset.measurable_prod _ fun y _ => ?_).mul (Finset.measurable_prod _ fun y _ => ?_)
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hr y))
  · exact (measurable_one.indicator hJw).comp
      (((measurable_pi_apply y).comp measurable_fst).mul (Real.measurable_exp.comp (hr y)))

lemma measurable_LcoreC (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    (Cd : Finset (Fin K)) (cv : Fin K → ℝ) : Measurable (LcoreC E Jw Cd cv) := by
  have h := (measurable_LcoreC2 E hJw Cd).comp (measurable_const.prodMk measurable_id
    (f := fun _ : Fin K → ℝ => cv))
  exact h

/-- **(FAC) for the cover integrand.** -/
theorem LcoreC_shift (E : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (Cd : Finset (Fin K))
    (S : Finset (Fin N)) (Q : Fin N → ℝ) (hQ : ∀ g ∈ S, 0 < Q g) (v : Fin N → Fin K → ℝ)
    (W : Fin K → Fin N → ℕ) (hv : ∀ g ∈ S, ∀ y, (W y g : ℝ) = ∑ j, (E y j : ℝ) * v g j)
    (cv' : Fin K → ℝ) (x : Fin K → ℝ) :
    LcoreC E Jw Cd (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g) (x - facShift S Q v) =
      ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y ∈ Cd, W y g)) * LcoreC E Jw Cd cv' x := by
  have hexp : ∀ y, Real.exp (rowLog E (x - facShift S Q v) y) =
      Real.exp (rowLog E x y) * ∏ g ∈ S, ((Q g)⁻¹) ^ W y g := by
    intro y
    rw [rowLog_sub_facShift E S Q v W hv, Real.exp_sub, Real.exp_sum, div_eq_mul_inv,
      ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun g hg => ?_
    rw [mul_comm, Real.exp_mul, Real.exp_log (hQ g hg), Real.rpow_natCast, inv_pow]
  have hcv : ∀ y, (cv' y * ∏ g ∈ S, Q g ^ W y g) * Real.exp (rowLog E (x - facShift S Q v) y) =
      cv' y * Real.exp (rowLog E x y) := by
    intro y
    rw [hexp y]
    have : (∏ g ∈ S, Q g ^ W y g) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun g hg => ?_
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (hQ g hg).ne')]
    calc (cv' y * ∏ g ∈ S, Q g ^ W y g) * (Real.exp (rowLog E x y) *
          ∏ g ∈ S, (Q g)⁻¹ ^ W y g)
        = cv' y * Real.exp (rowLog E x y) *
            ((∏ g ∈ S, Q g ^ W y g) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g) := by ring
      _ = _ := by rw [this, mul_one]
  have hnn : ∀ y, 0 ≤ ∏ g ∈ S, (Q g)⁻¹ ^ W y g := fun y =>
    Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (hQ g hg).le) _
  unfold LcoreC
  simp_rw [hcv, hexp]
  have hsplit : ∀ y, ENNReal.ofReal (Real.exp (rowLog E x y) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g) =
      ENNReal.ofReal (Real.exp (rowLog E x y)) *
        ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ W y g) := fun y =>
    ENNReal.ofReal_mul (Real.exp_pos _).le
  simp_rw [hsplit]
  have hprod : ∏ g ∈ S, (Q g)⁻¹ ^ (∑ y ∈ Cd, W y g) = ∏ y ∈ Cd, ∏ g ∈ S, (Q g)⁻¹ ^ W y g := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hprod, ENNReal.ofReal_prod_of_nonneg (fun y _ => hnn y), Finset.prod_mul_distrib]
  ring

/-- **(FAC) for the integral of the cover integrand over the processed pivots.** -/
theorem lintegral_LcoreC_shift (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) (Cd : Finset (Fin K)) {i : ℕ} (hi : i ≤ K) (u : Fin K → ℝ)
    (S : Finset (Fin N)) (Q : Fin N → ℝ) (hQ : ∀ g ∈ S, 0 < Q g) (v : Fin N → Fin K → ℝ)
    (W : Fin K → Fin N → ℕ) (hv : ∀ g ∈ S, ∀ y, (W y g : ℝ) = ∑ j, (E y j : ℝ) * v g j)
    (hsupp : ∀ g ∈ S, ∀ j : Fin K, (j : ℕ) < K - i → v g j = 0) (cv' : Fin K → ℝ) :
    ∫⁻ z : Fin i → ℝ, LcoreC E Jw Cd (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g) (mergeL i z u) =
      ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y ∈ Cd, W y g)) *
        ∫⁻ z : Fin i → ℝ, LcoreC E Jw Cd cv' (mergeL i z u) := by
  set ψ := facShift S Q v with hψ
  have hψ0 : ∀ j : Fin K, (j : ℕ) < K - i → ψ j = 0 := by
    intro j hj
    simp only [hψ, facShift]
    exact Finset.sum_eq_zero fun g hg => by rw [hsupp g hg j hj, mul_zero]
  set ψ' : Fin i → ℝ := fun a : Fin i => ψ ⟨K - i + (a : ℕ), by have := a.isLt; omega⟩
    with hψ'
  rw [← lintegral_sub_right_eq_self _ ψ']
  have : ∀ z : Fin i → ℝ, LcoreC E Jw Cd (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g)
      (mergeL i (z - ψ') u) = ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y ∈ Cd, W y g)) *
        LcoreC E Jw Cd cv' (mergeL i z u) := by
    intro z
    rw [← mergeL_sub hi z u ψ hψ0]
    exact LcoreC_shift E Jw Cd S Q hQ v W hv cv' _
  simp_rw [this]
  exact lintegral_const_mul _ ((measurable_LcoreC E hJw Cd cv').comp (measurable_mergeL i u))

/-- A row outside the cover: `∫ 1(d e^u ∈ J) du ≤ vol(J)/z` for `J ⊆ [z, ∞)`. -/
theorem lintegral_exp_window_z {d z : ℝ} (hd : 0 < d) (hz : 0 < z) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJz : J ⊆ Set.Ici z) :
    ∫⁻ u, J.indicator 1 (d * Real.exp u) ≤ ENNReal.ofReal z⁻¹ * volume J := by
  have h := lintegral_log_subst (fun u => J.indicator (1 : ℝ → ℝ≥0∞) (d * Real.exp u))
  rw [← h]
  have hpt : ∀ t, (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹ *
      J.indicator 1 (d * Real.exp (Real.log t))) t ≤
      ENNReal.ofReal (d / z) * ((fun t => d * t) ⁻¹' J).indicator 1 t := by
    intro t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht]
      have ht' : (0 : ℝ) < t := ht
      rw [Real.exp_log ht']
      by_cases hJt : d * t ∈ J
      · rw [indicator_of_mem hJt, indicator_of_mem (show t ∈ (fun t => d * t) ⁻¹' J from hJt)]
        simp only [Pi.one_apply, mul_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have hzt : z ≤ d * t := hJz hJt
        rw [le_div_iff₀ hz]
        calc t⁻¹ * z ≤ t⁻¹ * (d * t) := mul_le_mul_of_nonneg_left hzt (inv_nonneg.mpr ht'.le)
          _ = d := by field_simp
      · rw [indicator_of_notMem hJt]; simp
    · rw [indicator_of_notMem ht]; exact zero_le
  refine (lintegral_mono hpt).trans ?_
  have hmeas : MeasurableSet ((fun t => d * t) ⁻¹' J) := (measurable_const_mul d) hJ
  rw [lintegral_const_mul _ (measurable_one.indicator hmeas), lintegral_indicator_one hmeas]
  have hpre : (fun t => d * t) ⁻¹' J = d⁻¹ • J := by
    ext t
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hd.ne'),
      inv_inv, smul_eq_mul]
  rw [hpre, Measure.addHaar_smul]
  simp only [Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hd)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hd.le hz.le)]
  refine le_of_eq ?_
  congr 2
  field_simp

/-- **The end of the cover recursion** (Lemma A.2 in log coordinates, with the rows outside the
cover contributing `vol(J)/z` each). -/
theorem final_volumeC (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) (Cd : Finset (Fin K)) (d : Fin K → ℝ) (hd : ∀ y, 0 < d y) {z : ℝ}
    (hz : 0 < z) (hJz : Jw ⊆ Set.Ici z) :
    ∫⁻ x : Fin K → ℝ, LcoreC E Jw Cd d x ≤
      ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (if y ∈ Cd then ENNReal.ofReal (d y)⁻¹ * volume Jw
        else ENNReal.ofReal z⁻¹ * volume Jw) := by
  set f : Fin K → ℝ → ℝ≥0∞ := fun y t =>
    (if y ∈ Cd then ENNReal.ofReal (Real.exp t) else 1) * Jw.indicator 1 (d y * Real.exp t) with hf
  have hfm : ∀ y, Measurable (f y) := fun y => by
    simp only [hf]
    refine Measurable.mul ?_ ((measurable_one.indicator hJw).comp
      (measurable_const.mul Real.measurable_exp))
    split_ifs
    · exact ENNReal.measurable_ofReal.comp Real.measurable_exp
    · exact measurable_const
  set g : (Fin K → ℝ) → ℝ≥0∞ := fun u => ∏ y, f y (u y) with hg
  have hgm : Measurable g :=
    Finset.measurable_prod _ fun y _ => (hfm y).comp (measurable_pi_apply y)
  set F := Matrix.toLin' (Ereal E) with hF
  have hFdet : LinearMap.det F ≠ 0 := by rw [hF, LinearMap.det_toLin']; exact hE
  have hFm : Measurable F := (LinearMap.continuous_of_finiteDimensional F).measurable
  have hint : (fun x : Fin K → ℝ => LcoreC E Jw Cd d x) = g ∘ F := by
    funext x
    have hrow : ∀ y, rowLog E x y = (F x) y := by
      intro y
      simp [rowLog, hF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Ereal]
    simp only [LcoreC, hg, hf, Function.comp_apply, Finset.prod_mul_distrib, hrow]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hint, show lintegral volume (g ∘ ⇑F) = ∫⁻ a, g (F a) from rfl,
    ← lintegral_map hgm hFm, Real.map_linearMap_volume_pi_eq_smul_volume_pi hFdet,
    lintegral_smul_measure, hF, LinearMap.det_toLin', smul_eq_mul]
  gcongr
  rw [hg, lintegral_pi_prod _ hfm]
  refine Finset.prod_le_prod' fun y _ => ?_
  simp only [hf]
  split_ifs with hy
  · exact lintegral_exp_window (hd y) hJw
  · simp only [one_mul]
    exact lintegral_exp_window_z (hd y) hz hJw hJz

end RankFull
