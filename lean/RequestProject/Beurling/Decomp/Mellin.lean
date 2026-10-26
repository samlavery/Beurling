module

public import RequestProject.Beurling.Remark12
public import RequestProject.Beurling.LateNoise

/-!
# Mellin transforms used for the decomposition (14)

Generic facts about the Mellin transform `s ↦ s ∫_1^∞ E(x) x^{-s-1} dx` (`s * tailMellin E s`):

* `integrable_tsum_of_lintegral` : a series of functions whose norms have summable integrals is
  integrable;
* `mellin_primitive` : the transform of a primitive, `s ∫_c^∞ (∫_c^x g) x^{-s-1} dx = ∫_c^∞ g(u) u^{-s} du`;
* `earlyNoise D a` : the early part `D̂_{<a}(s) = s ∫_1^a D(x) x^{-s-1} dx + D(a) a^{-s}` of the
  transform of `D`, which is entire for bounded measurable `D` (`differentiable_earlyNoise`);
* `mellin_split` : `s ∫_1^∞ D x^{-s-1} = D̂_{<a}(s) + D̂_{≥a}(s)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Remark12 DesignedZero

namespace Decomp

/-- A series of functions whose norms have summable integrals is integrable. -/
lemma integrable_tsum_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ ≠ ⊤) : Integrable (fun x => ∑' i, f i x) μ := by
  have hint : ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ ≠ ⊤ := by
    rwa [lintegral_tsum fun i => (hf i).enorm]
  have hsum : ∀ᵐ x ∂μ, Summable fun i => f i x := by
    have hae : ∀ᵐ x ∂μ, ∑' i, ‖f i x‖ₑ < ⊤ := by
      refine ae_lt_top' ?_ hint
      exact AEMeasurable.ennreal_tsum fun i => (hf i).enorm
    filter_upwards [hae] with x hx
    refine Summable.of_norm ?_
    have : ∑' i, (‖f i x‖₊ : ENNReal) ≠ ⊤ := by
      simpa [enorm_eq_nnnorm] using hx.ne
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mp this
    exact (NNReal.summable_coe.mpr h2).congr fun i => by simp
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => ∑ i ∈ Finset.range n, f i x)
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun i _ => hf i) ?_
    filter_upwards [hsum] with x hx
    exact hx.hasSum.tendsto_sum_nat
  · unfold HasFiniteIntegral
    calc ∫⁻ x, ‖∑' i, f i x‖ₑ ∂μ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ < ⊤ := lt_top_iff_ne_top.mpr hint

lemma integral_Ioi_ite_cpow {c u : ℝ} (hc : 0 < c) (hu : c < u) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi c, (if u ≤ x then (x : ℂ) ^ (-s - 1) else 0) = (u : ℂ) ^ (-s) / s := by
  have e : (fun x : ℝ => if u ≤ x then (x : ℂ) ^ (-s - 1) else 0) =
      (Ici u).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) := by
    funext x; simp [Set.indicator, mem_Ici]
  rw [e, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hu), integral_Ici_eq_integral_Ioi,
    integral_Ioi_cpow_of_lt (by simp; linarith) (by linarith)]
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [show -s - 1 + 1 = -s by ring]
  field_simp

lemma integral_Ioi_ite_rpow {c u : ℝ} (hc : 0 < c) (hu : c < u) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi c, (if u ≤ x then x ^ (-σ - 1) else 0) = u ^ (-σ) / σ := by
  have e : (fun x : ℝ => if u ≤ x then x ^ (-σ - 1) else 0) =
      (Ici u).indicator (fun x : ℝ => x ^ (-σ - 1)) := by
    funext x; simp [Set.indicator, mem_Ici]
  rw [e, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hu), integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
  rw [show -σ - 1 + 1 = -σ by ring]
  field_simp

lemma integrableOn_Ioi_ite_cpow {c u : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => if u ≤ x then (x : ℂ) ^ (-s - 1) else 0) (Ioi c) := by
  refine Integrable.mono' (g := fun x : ℝ => x ^ (-s.re - 1))
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc) ?_ ?_
  · exact (Measurable.ite measurableSet_Ici (by fun_prop) measurable_const).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_trans hc hx
    split_ifs
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
    · simp only [norm_zero]; exact Real.rpow_nonneg hx0.le _

/-- **The transform of a primitive.** For `c > 0`, `Re s > 0` and `g` with
`∫_c^∞ |g(u)| u^{-σ} du < ∞` (and locally integrable on `[c, ∞)`):
`s ∫_c^∞ (∫_c^x g) x^{-s-1} dx = ∫_c^∞ g(u) u^{-s} du`. The left integrand is integrable. -/
lemma mellin_primitive {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {s : ℂ} (hs : 0 < s.re)
    (hg : IntegrableOn (fun u => g u * u ^ (-s.re)) (Ioi c)) :
    IntegrableOn (fun x : ℝ => ((∫ u in c..x, g u : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi c) ∧
      s * ∫ x in Ioi c, ((∫ u in c..x, g u : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
        ∫ u in Ioi c, (g u : ℂ) * (u : ℂ) ^ (-s) := by
  set μ := volume.restrict (Ioi c)
  set f : ℝ × ℝ → ℂ := fun p =>
    (g p.2 : ℂ) * (if p.2 ≤ p.1 then (p.1 : ℂ) ^ (-s - 1) else 0) with hf
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hgae : AEStronglyMeasurable g μ := by
    have h1 : AEStronglyMeasurable (fun u : ℝ => g u * u ^ (-s.re) * u ^ s.re) μ :=
      hg.1.mul (Measurable.pow_const measurable_id _).aestronglyMeasurable
    refine h1.congr ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := lt_trans hc hu
    simp only
    rw [mul_assoc, ← Real.rpow_add hu0, neg_add_cancel, Real.rpow_zero, mul_one]
  have hfm : AEStronglyMeasurable f (μ.prod μ) := by
    refine AEStronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hgae).comp_snd) ?_
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
    exact (Complex.measurable_ofReal.comp measurable_fst).pow_const _
  -- the sections and their norms
  have hsec : ∀ u ∈ Ioi c, ∫ x, f (x, u) ∂μ = (g u : ℂ) * ((u : ℂ) ^ (-s) / s) := by
    intro u hu
    simp only [hf]
    rw [integral_const_mul, integral_Ioi_ite_cpow hc hu hs]
  have hsecn : ∀ u ∈ Ioi c, ∫ x, ‖f (x, u)‖ ∂μ = |g u| * (u ^ (-s.re) / s.re) := by
    intro u hu
    have e : ∀ x ∈ Ioi c, ‖f (x, u)‖ = |g u| * (if u ≤ x then x ^ (-s.re - 1) else 0) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := lt_trans hc hx
      simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      split_ifs
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
      · simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_Ioi_ite_rpow hc hu hs]
  have hsecint : ∀ u, Integrable (fun x => f (x, u)) μ := fun u =>
    (integrableOn_Ioi_ite_cpow (u := u) hc hs).const_mul (g u : ℂ)
  have hFint : Integrable f (μ.prod μ) := by
    rw [integrable_prod_iff' hfm]
    refine ⟨ae_of_all _ hsecint, ?_⟩
    have : Integrable (fun u => |g u| * (u ^ (-s.re) / s.re)) μ := by
      have h1 := (hg.norm.div_const s.re)
      refine h1.congr ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_)
      have hu0 : (0 : ℝ) < u := lt_trans hc hu
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      ring
    exact this.congr ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => (hsecn u hu).symm)
  -- the primitive as an integral over the second variable
  have hprim : ∀ x ∈ Ioi c, ((∫ u in c..x, g u : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∫ u, f (x, u) ∂μ := by
    intro x hx
    have hcx : c ≤ x := le_of_lt hx
    have e : (fun u : ℝ => f (x, u)) =
        (Ioc c x ∪ Iic c).indicator (fun u => (g u : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      funext u
      simp only [hf, Set.indicator, mem_union, mem_Ioc, mem_Iic]
      by_cases hux : u ≤ x
      · by_cases huc : c < u
        · simp [hux, huc]
        · push_neg at huc; simp [hux, huc]
      · push_neg at hux
        have : ¬ (u ≤ c) := by intro h; linarith
        simp [not_le.mpr hux, this]
    rw [e, integral_indicator (measurableSet_Ioc.union measurableSet_Iic),
      Measure.restrict_restrict (measurableSet_Ioc.union measurableSet_Iic)]
    have hset : (Ioc c x ∪ Iic c) ∩ Ioi c = Ioc c x := by
      ext u; simp only [mem_inter_iff, mem_union, mem_Ioc, mem_Iic, mem_Ioi]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 (not_le.mpr h2)
      · intro h; exact ⟨Or.inl h, h.1⟩
    rw [hset, integral_mul_const, intervalIntegral.integral_of_le hcx]
    congr 1
    exact integral_complex_ofReal.symm
  refine ⟨?_, ?_⟩
  · exact hFint.integral_prod_left.congr
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => (hprim x hx).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi hprim]
    have hswap := integral_integral_swap (μ := μ) (ν := μ)
      (f := fun x u => f (x, u)) hFint
    change s * ∫ x, ∫ u, f (x, u) ∂μ ∂μ = _
    rw [hswap, setIntegral_congr_fun measurableSet_Ioi hsec, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    field_simp

/-- The early part of the transform of `D`:
`D̂_{<a}(s) = s ∫_1^a D(x) x^{-s-1} dx + D(a) a^{-s}` (`= ∫_{[1,a)} x^{-s} dD` by parts). -/
noncomputable def earlyNoise (D : ℝ → ℝ) (a : ℝ) (s : ℂ) : ℂ :=
  s * (∫ x in Ioc 1 a, (D x : ℂ) * (x : ℂ) ^ (-s - 1)) + (D a : ℂ) * (a : ℂ) ^ (-s)

/-- **The split of the transform of `D` at `a`**: `s ∫_1^∞ D x^{-s-1} = D̂_{<a}(s) + D̂_{≥a}(s)`. -/
lemma mellin_split {D : ℝ → ℝ} {s : ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hint : IntegrableOn (fun x : ℝ => (D x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)) :
    s * tailMellin D s = earlyNoise D a s + lateNoise D a s := by
  unfold tailMellin earlyNoise lateNoise
  rw [← Ioc_union_Ioi_eq_Ioi ha, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self)
    (hint.mono_set (Ioi_subset_Ioi ha))]
  ring

/-- **`D̂_{<a}` is entire** for `D` integrable and bounded on `(1, a]`. -/
lemma differentiable_earlyNoise_of_integrableOn {D : ℝ → ℝ} {a M : ℝ} (ha : 1 ≤ a)
    (hEint : IntegrableOn D (Ioc 1 a))
    (hDb : ∀ x ∈ Ioc 1 a, |D x| ≤ M) : Differentiable ℂ (earlyNoise D a) := by
  set E : ℝ → ℝ := (Ioc 1 a).indicator D with hE
  have hEloc : LocallyIntegrable E :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr hEint).locallyIntegrable
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hdiff : ∀ γ ≤ 0, DifferentiableOn ℂ (tailMellin E) {s : ℂ | γ < s.re} := by
    intro γ hγ
    refine tailMellin_differentiableOn hEloc (C := max M 0 * a ^ (-γ)) (fun x hx => ?_)
    by_cases hxI : x ∈ Ioc 1 a
    · rw [hE, indicator_of_mem hxI]
      have h1 : 1 ≤ a ^ (-γ) * x ^ γ := by
        have hx0 : 0 < x := by linarith [hxI.1]
        have : a ^ γ ≤ x ^ γ := Real.rpow_le_rpow_of_nonpos hx0 hxI.2 hγ
        rw [Real.rpow_neg (by linarith)]
        rw [le_inv_mul_iff₀ (Real.rpow_pos_of_pos (by linarith) _)]
        linarith
      calc |D x| ≤ max M 0 := (hDb x hxI).trans (le_max_left _ _)
        _ = max M 0 * 1 := by ring
        _ ≤ max M 0 * (a ^ (-γ) * x ^ γ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = max M 0 * a ^ (-γ) * x ^ γ := by ring
    · rw [hE, indicator_of_notMem hxI, abs_zero]
      exact mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (by linarith) _)
  have heq : earlyNoise D a = fun s => s * tailMellin E s + (D a : ℂ) * (a : ℂ) ^ (-s) := by
    funext s
    unfold earlyNoise tailMellin
    congr 2
    have : (fun x : ℝ => ((E x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
        (Ioc 1 a).indicator (fun x : ℝ => (D x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      funext x
      by_cases hx : x ∈ Ioc 1 a
      · simp [hE, indicator_of_mem hx]
      · simp [hE, indicator_of_notMem hx]
    rw [this, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self]
  rw [heq]
  intro s
  have hγ : min 0 (s.re - 1) ≤ 0 := min_le_left _ _
  have hmem : s ∈ {s : ℂ | min 0 (s.re - 1) < s.re} := by
    simp only [mem_setOf_eq]; have := min_le_right 0 (s.re - 1); linarith
  have hopen : IsOpen {z : ℂ | min 0 (s.re - 1) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : DifferentiableAt ℂ (tailMellin E) s :=
    (hdiff _ hγ).differentiableAt (hopen.mem_nhds hmem)
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by linarith)
  exact (differentiableAt_id.mul h1).add
    ((differentiableAt_id.neg.const_cpow (Or.inl ha0)).const_mul _)

/-- **`D̂_{<a}` is entire** for `D` measurable and bounded on `(1, a]`. -/
lemma differentiable_earlyNoise {D : ℝ → ℝ} {a M : ℝ} (ha : 1 ≤ a) (hDm : Measurable D)
    (hDb : ∀ x ∈ Ioc 1 a, |D x| ≤ M) : Differentiable ℂ (earlyNoise D a) :=
  differentiable_earlyNoise_of_integrableOn ha
    (Measure.integrableOn_of_bounded (M := M) (by simp) hDm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact hDb x hx)) hDb

end Decomp

end
