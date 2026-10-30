module

public import Mathlib

/-!
# Mellin tails of monotone functions

Step 3 of the proof of Theorem 5.24: for `g` monotone on `[y, ∞)` with `|g(x)| ≤ C x`, the tail
`s ∫_y^∞ (g(x) - g(y)) x^{-s-1} dx = ∫_{[y,∞)} u^{-s} dg(u)` is bounded in modulus by its value at
`σ = Re s`, since `dg ≥ 0`.

Instead of the Stieltjes measure of `g` we use the layer-cake formula
`g(x) - g(y) = ∫_0^∞ 1_{t < g(x) - g(y)} dt`: each level set `{x > y : t < g(x) - g(y)}` is an upper
set, hence a.e. equal to a ray `(b, ∞)` with `b ≥ y`, on which `s ∫_b^∞ x^{-s-1} dx = b^{-s}`.

* `norm_mul_setIntegral_cpow_le` : the bound for the indicator of an upper set.
* `integral_smul_eq_layerCake` : Fubini for the layer-cake representation.
* `norm_tail_mellin_monotone_le` : the bound for `g`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter

namespace LocalPNT

/-- For an upper set `B ⊆ (y, ∞)`, `|s ∫_B x^{-s-1} dx| ≤ σ ∫_B x^{-σ-1} dx`. -/
theorem norm_mul_setIntegral_cpow_le {y : ℝ} (hy : 0 < y) {B : Set ℝ} (hB : IsUpperSet B)
    (hBy : B ⊆ Ioi y) {s : ℂ} (hs : 1 < s.re) :
    ‖s * ∫ x in B, (x : ℂ) ^ (-s - 1)‖ ≤ s.re * ∫ x in B, x ^ (-s.re - 1) := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simp
  have hbdd : BddBelow B := ⟨y, fun x hx => (hBy hx).le⟩
  set b := sInf B
  have hyb : y ≤ b := le_csInf hne fun x hx => (hBy hx).le
  have hb : 0 < b := hy.trans_le hyb
  have hsub : Ioi b ⊆ B := fun x hx => by
    obtain ⟨z, hz, hzx⟩ := exists_lt_of_csInf_lt hne hx
    exact hB hzx.le hz
  have hae : B =ᵐ[volume] Ioi b :=
    ((LE.le.eventuallySubset fun x hx => csInf_le hbdd hx).trans
      Ioi_ae_eq_Ici.symm.le).antisymm hsub.eventuallySubset
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae,
    integral_Ioi_cpow_of_lt (by simp; linarith) hb, integral_Ioi_rpow_of_lt (by linarith) hb]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hσ0 : s.re ≠ 0 := by linarith
  have e1 : s * (-(b : ℂ) ^ (-s - 1 + 1) / (-s - 1 + 1)) = (b : ℂ) ^ (-s) := by
    rw [sub_add_cancel]; field_simp
  have e2 : s.re * (-b ^ (-s.re - 1 + 1) / (-s.re - 1 + 1)) = b ^ (-s.re) := by
    rw [sub_add_cancel]; field_simp
  rw [e1, e2, norm_cpow_eq_rpow_re_of_pos hb]
  simp

/-- The layer-cake representation `∫_S h f = ∫_0^∞ ∫_S 1_{t < h} f dt`, together with the
integrability of the integrand on the product. -/
theorem integral_smul_eq_layerCake {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) {f : ℝ → E}
    {S : Set ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    (hi : Integrable (fun x => h x * ‖f x‖) (volume.restrict S)) :
    Integrable (fun p : ℝ × ℝ => {q : ℝ × ℝ | q.1 < h q.2}.indicator (fun q => f q.2) p)
      ((volume.restrict (Ioi 0)).prod (volume.restrict S)) ∧
    ∫ x in S, h x • f x = ∫ t in Ioi 0, ∫ x in S, {x | t < h x}.indicator f x := by
  set F := fun p : ℝ × ℝ => {q : ℝ × ℝ | q.1 < h q.2}.indicator (fun q => f q.2) p
  have hslice : ∀ x, (fun t => F (t, x)) = (Iio (h x)).indicator (fun _ => f x) := fun x => by
    ext t; simp [F, indicator]
  have hvol : ∀ x, (volume.restrict (Ioi (0 : ℝ))).real (Iio (h x)) = h x := fun x => by
    rw [measureReal_restrict_apply measurableSet_Iio, Iio_inter_Ioi,
      Real.volume_real_Ioo_of_le (h0 x), sub_zero]
  have hFm : AEStronglyMeasurable F ((volume.restrict (Ioi 0)).prod (volume.restrict S)) :=
    (hf.comp_snd (μ := volume.restrict (Ioi 0))).indicator
      (measurableSet_lt measurable_fst (hm.comp measurable_snd))
  have hF : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict S)) := by
    refine (integrable_prod_iff' hFm).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · rw [hslice, integrable_indicator_iff measurableSet_Iio]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi]
      exact measure_Ioo_lt_top.ne
    · refine hi.congr (Eventually.of_forall fun x => ?_)
      have : (fun t => ‖F (t, x)‖) = (Iio (h x)).indicator (fun _ => ‖f x‖) := by
        ext t; by_cases ht : t < h x <;> simp [F, indicator, ht]
      change _ = ∫ t in Ioi 0, (fun t => ‖F (t, x)‖) t
      rw [this, integral_indicator_const _ measurableSet_Iio, hvol, smul_eq_mul]
  refine ⟨hF, ?_⟩
  have hFt : ∀ t x, {x | t < h x}.indicator f x = F (t, x) := fun t x => by simp [F, indicator]
  simp_rw [hFt]
  rw [integral_integral_swap (f := fun t x => F (t, x)) hF]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [hslice, integral_indicator_const _ measurableSet_Iio, hvol]

/-- **Step 3 of Theorem 5.24.** If `g` is monotone on `[y, ∞)` with `|g(x)| ≤ C x`, then for
`Re s > 1` the Mellin tail `s ∫_y^∞ (g(x) - g(y)) x^{-s-1} dx` is bounded in modulus by its value
at `σ = Re s`. -/
theorem norm_tail_mellin_monotone_le {g : ℝ → ℝ} {y C : ℝ} (hy : 0 < y)
    (hg : MonotoneOn g (Ici y)) (hC : ∀ x ≥ y, |g x| ≤ C * x) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((g x - g y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi y) ∧
    IntegrableOn (fun x : ℝ => (g x - g y) * x ^ (-s.re - 1)) (Ioi y) ∧
    ‖s * ∫ x in Ioi y, ((g x - g y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤
      s.re * ∫ x in Ioi y, (g x - g y) * x ^ (-s.re - 1) := by
  set σ := s.re
  set H : ℝ → ℝ := fun x => g (max x y) - g y
  have hHmono : Monotone H := fun a b hab => by
    simp only [H]
    exact sub_le_sub_right (hg (le_max_right a y) (le_max_right b y) (max_le_max_right y hab)) _
  have hHm : Measurable H := hHmono.measurable
  have hH0 : ∀ x, 0 ≤ H x := fun x =>
    sub_nonneg.2 (hg self_mem_Ici (le_max_right x y) (le_max_right x y))
  have hHeq : EqOn H (fun x => g x - g y) (Ioi y) := fun x hx => by
    simp only [H, max_eq_left (mem_Ioi.1 hx).le]
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC y le_rfl)
    exact nonneg_of_mul_nonneg_left this hy
  have hHle : ∀ x ∈ Ioi y, H x ≤ 2 * C * x := fun x hx => by
    have hx : y < x := hx
    rw [hHeq hx]
    have h1 := hC x hx.le
    have h2 := hC y le_rfl
    have := le_abs_self (g x)
    have := neg_abs_le (g y)
    nlinarith
  have hfr : ∀ x ∈ Ioi y, ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-σ - 1) := fun x hx => by
    rw [norm_cpow_eq_rpow_re_of_pos (hy.trans hx)]; simp [σ]
  -- the real integrand
  have hRint : IntegrableOn (fun x => H x * x ^ (-σ - 1)) (Ioi y) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) hy).const_mul
      (2 * C)) ((hHm.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hy.trans hx
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_of_nonneg (mul_nonneg (hH0 x) hp)]
    calc H x * x ^ (-σ - 1) ≤ 2 * C * x * x ^ (-σ - 1) := by gcongr; exact hHle x hx
      _ = 2 * C * x ^ (-σ) := by
        rw [mul_assoc, ← Real.rpow_one_add' hx0.le (by linarith)]; ring_nf
  have hRi : Integrable (fun x => H x * ‖x ^ (-σ - 1)‖) (volume.restrict (Ioi y)) :=
    hRint.congr_fun (fun x hx => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hy.trans hx).le _)]) measurableSet_Ioi
  have hCi : Integrable (fun x => H x * ‖(x : ℂ) ^ (-s - 1)‖) (volume.restrict (Ioi y)) :=
    hRint.congr_fun (fun x hx => by rw [hfr x hx]) measurableSet_Ioi
  obtain ⟨hFR, hR⟩ := integral_smul_eq_layerCake (f := fun x : ℝ => x ^ (-σ - 1)) hHm hH0
    (measurable_id.pow_const (-σ - 1)).aestronglyMeasurable hRi
  obtain ⟨-, hCx⟩ := integral_smul_eq_layerCake hHm hH0
    ((Complex.measurable_ofReal.pow_const (-s - 1)).aestronglyMeasurable) hCi
  have hCint : IntegrableOn (fun x => (H x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi y) := by
    refine Integrable.mono' hRint ((Complex.measurable_ofReal.comp hHm).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, hfr x hx, Complex.norm_real, Real.norm_of_nonneg (hH0 x)]
  have eC : ∫ x in Ioi y, ((g x - g y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∫ x in Ioi y, H x • (x : ℂ) ^ (-s - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [Complex.real_smul, hHeq hx]
  have eR : ∫ x in Ioi y, (g x - g y) * x ^ (-σ - 1) = ∫ x in Ioi y, H x • x ^ (-σ - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [smul_eq_mul, hHeq hx]
  refine ⟨hCint.congr_fun (fun x hx => by simp only [hHeq hx]) measurableSet_Ioi,
    hRint.congr_fun (fun x hx => by simp only [hHeq hx]) measurableSet_Ioi, ?_⟩
  rw [eC, eR, hCx, hR, ← integral_const_mul, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFR.integral_prod_left.const_mul σ)
    (Eventually.of_forall fun t => ?_)
  have hmt : MeasurableSet {x | t < H x} := measurableSet_lt measurable_const hHm
  have hup : IsUpperSet (Ioi y ∩ {x | t < H x}) := (isUpperSet_Ioi y).inter fun a b hab ha =>
    lt_of_lt_of_le ha (hHmono hab)
  have := norm_mul_setIntegral_cpow_le hy hup inter_subset_left hs
  simp only [setIntegral_indicator hmt]
  exact this

end LocalPNT

end
