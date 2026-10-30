module

public import RequestProject.Beurling.Model.Land

/-!
# Conditional means under the box-uniform law (F2), pathwise

For an abstract jitter law `J` (`RankFull.JitterLaw`), a count `f ≥ 0` bounded by `C` and
dominated by `Φ(ω, q_n(ω))` on `A_n`, with `Φ` jointly `ℱ_n`-measurable:

* `condExp_le_boxMean` : `E[f | ℱ_n] ≤ min(C, G_n)` a.s., where
  `G_n(ω) = 1_{A_n} H_n⁻¹ ∫_{box_n} Φ(ω, t) dt` is the (F2) bound;
* `sum_boxMean_le` : pathwise, `∑_n G_n(ω) ≤ θ ∫ Φ̄(ω, t) dt` when `Φ_n ≤ Φ̄` for every `n`
  ((F1), `J.slots`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory RankFull
open scoped ENNReal

namespace BModel

section Gen

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {θE : ℝ≥0∞} (J : JitterLaw Ω P θE)

/-- The (F2) bound `G_n(ω) = 1_{A_n} H_n⁻¹ ∫_{box_n} Φ(ω, t) dt`. -/
noncomputable def boxMean (n : ℕ) (Φ : Ω × ℝ → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
    ∫⁻ t in box (J.c n ω) (J.H n ω), Φ (ω, t)) ω

lemma boxMean_meas (n : ℕ) {Φ : Ω × ℝ → ℝ≥0∞} (hΦ : JMeas (J.F n) Φ) :
    Measurable[J.F n] (boxMean J n Φ) := by
  letI mP : MeasurableSpace (Ω × ℝ) := @Prod.instMeasurableSpace Ω ℝ (J.F n) _
  have hfst : @Measurable _ _ mP (J.F n) Prod.fst := @measurable_fst _ _ (J.F n) _
  have hsnd : @Measurable _ _ mP _ Prod.snd := @measurable_snd _ _ (J.F n) _
  have hc : @Measurable _ ℝ mP _ fun x : Ω × ℝ => J.c n x.1 := (J.c_meas n).comp hfst
  have hH : @Measurable _ ℝ mP _ fun x : Ω × ℝ => J.H n x.1 := (J.H_meas n).comp hfst
  have hbox : @MeasurableSet _ mP {x : Ω × ℝ | x.2 ∈ box (J.c n x.1) (J.H n x.1)} := by
    simp only [box, mem_Ico, setOf_and]
    exact (measurableSet_le (hc.sub (hH.div_const 2)) hsnd).inter
      (measurableSet_lt hsnd (hc.add (hH.div_const 2)))
  have hind : @Measurable _ ℝ≥0∞ mP _ fun x : Ω × ℝ =>
      {x : Ω × ℝ | x.2 ∈ box (J.c n x.1) (J.H n x.1)}.indicator 1 x * Φ x :=
    (measurable_one.indicator hbox).mul hΦ
  have hint : Measurable[J.F n] fun ω => ∫⁻ t, {x : Ω × ℝ | x.2 ∈ box (J.c n x.1)
      (J.H n x.1)}.indicator 1 (ω, t) * Φ (ω, t) :=
    @Measurable.lintegral_prod_right' Ω ℝ (J.F n) _ volume _ _ hind
  have e : ∀ ω, ∫⁻ t in box (J.c n ω) (J.H n ω), Φ (ω, t) = ∫⁻ t, {x : Ω × ℝ | x.2 ∈ box
      (J.c n x.1) (J.H n x.1)}.indicator 1 (ω, t) * Φ (ω, t) := by
    intro ω
    rw [← lintegral_indicator (show MeasurableSet (box (J.c n ω) (J.H n ω)) from
      measurableSet_Ico)]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ box (J.c n ω) (J.H n ω)
    · rw [indicator_of_mem ht, indicator_of_mem (show (ω, t) ∈ {x : Ω × ℝ | x.2 ∈
        box (J.c n x.1) (J.H n x.1)} from ht)]
      simp
    · rw [indicator_of_notMem ht, indicator_of_notMem (show (ω, t) ∉ {x : Ω × ℝ | x.2 ∈
        box (J.c n x.1) (J.H n x.1)} from ht)]
      simp
  unfold boxMean
  simp_rw [e]
  exact (ENNReal.measurable_ofReal.comp (J.H_meas n).inv).mul hint |>.indicator (J.A_meas n)

/-- **The conditional mean under (F2)**: for `0 ≤ f ≤ C` dominated by `Φ(ω, q_n)` on `A_n`
(a.s.), with `Φ` restricted to `ℱ_n`-sets jointly measurable, `E[f | ℱ_n] ≤ min(C, G_n)`. -/
theorem condExp_le_boxMean (n : ℕ) {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfC : ∀ ω, f ω ≤ C) (hfm : Measurable f) {Φ : Ω × ℝ → ℝ≥0∞}
    (hΦ : ∀ S, MeasurableSet[J.F n] S → JMeas (J.F n) fun p => S.indicator 1 p.1 * Φ p)
    (hfΦ : ∀ᵐ ω ∂P, ENNReal.ofReal (f ω) ≤ (J.A n).indicator (fun ω => Φ (ω, J.q n ω)) ω)
    (hfin : ∀ ω, boxMean J n Φ ω ≠ ∞) :
    P[f | J.F n] ≤ᵐ[P] fun ω => min C (boxMean J n Φ ω).toReal := by
  have hFle := J.F_le n
  have hΦ1 : JMeas (J.F n) Φ := by
    have := hΦ univ MeasurableSet.univ
    simpa using this
  have hGm := boxMean_meas J n hΦ1
  set g : Ω → ℝ := fun ω => min C (boxMean J n Φ ω).toReal with hg
  have hgm : StronglyMeasurable[J.F n] g :=
    (measurable_const.min (ENNReal.measurable_toReal.comp hGm)).stronglyMeasurable
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => le_min hC ENNReal.toReal_nonneg
  have hgC : ∀ ω, g ω ≤ C := fun ω => min_le_left _ _
  have hfi : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hfC ω)
  have hgi : Integrable g P :=
    Integrable.of_bound (hgm.mono hFle).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]; exact hgC ω)
  refine condExp_ae_le_of_setIntegral hFle hfi hgm hgi fun S hS => ?_
  set B : Set Ω := {ω | (boxMean J n Φ ω).toReal ≤ C}
  have hB : MeasurableSet[J.F n] B :=
    measurableSet_le (ENNReal.measurable_toReal.comp hGm) measurable_const
  have hS1 : MeasurableSet[J.F n] (S ∩ B) := hS.inter hB
  have hS2 : MeasurableSet[J.F n] (S ∩ Bᶜ) := hS.inter hB.compl
  have hSm : MeasurableSet S := hFle _ hS
  have hS1m : MeasurableSet (S ∩ B) := hFle _ hS1
  have hS2m : MeasurableSet (S ∩ Bᶜ) := hFle _ hS2
  have hsplit : ∀ h : Ω → ℝ, Integrable h P → ∫ x in S, h x ∂P =
      ∫ x in S ∩ B, h x ∂P + ∫ x in S ∩ Bᶜ, h x ∂P := by
    intro h hh
    rw [← setIntegral_union (disjoint_left.mpr fun x h1 h2 => h2.2 h1.2) hS2m
      hh.integrableOn hh.integrableOn, Set.inter_union_compl]
  rw [hsplit f hfi, hsplit g hgi]
  refine add_le_add ?_ ?_
  · -- on `B`: `∫ f ≤ ∫ G`
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
        hfi.aestronglyMeasurable.restrict,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
        hgi.aestronglyMeasurable.restrict]
    refine ENNReal.toReal_mono ?_ ?_
    · refine ne_top_of_le_ne_top (b := ∫⁻ _ in S ∩ B, ENNReal.ofReal C ∂P) ?_
        (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hgC ω))
      rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)
    have hdens := J.dens n _ (hΦ _ hS1)
    calc ∫⁻ ω in S ∩ B, ENNReal.ofReal (f ω) ∂P
        = ∫⁻ ω, (S ∩ B).indicator (fun ω => ENNReal.ofReal (f ω)) ω ∂P :=
          (lintegral_indicator hS1m _).symm
      _ ≤ ∫⁻ ω, (J.A n).indicator (fun ω => (S ∩ B).indicator 1 ω * Φ (ω, J.q n ω)) ω ∂P := by
          refine lintegral_mono_ae (hfΦ.mono fun ω hω => ?_)
          by_cases h1 : ω ∈ S ∩ B
          · rw [indicator_of_mem h1]
            by_cases hA : ω ∈ J.A n
            · rw [indicator_of_mem hA, indicator_of_mem h1, Pi.one_apply, one_mul]
              rwa [indicator_of_mem hA] at hω
            · rw [indicator_of_notMem hA] at hω ⊢; exact hω
          · rw [indicator_of_notMem h1]; exact zero_le
      _ ≤ ∫⁻ ω, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
            ∫⁻ t in box (J.c n ω) (J.H n ω), (S ∩ B).indicator 1 ω * Φ (ω, t)) ω ∂P := hdens
      _ = ∫⁻ ω, (S ∩ B).indicator (boxMean J n Φ) ω ∂P := by
          refine lintegral_congr fun ω => ?_
          unfold boxMean
          by_cases h1 : ω ∈ S ∩ B <;> by_cases hA : ω ∈ J.A n <;>
            simp [indicator_of_mem, indicator_of_notMem, h1, hA]
      _ = ∫⁻ ω in S ∩ B, ENNReal.ofReal (g ω) ∂P := by
          rw [← lintegral_indicator hS1m]
          refine lintegral_congr fun ω => ?_
          by_cases h1 : ω ∈ S ∩ B
          · rw [indicator_of_mem h1, indicator_of_mem h1]
            have hB1 : (boxMean J n Φ ω).toReal ≤ C := h1.2
            simp only [hg, min_eq_right hB1, ENNReal.ofReal_toReal (hfin ω)]
          · rw [indicator_of_notMem h1, indicator_of_notMem h1]
  · -- off `B`: `f ≤ C = g`
    refine setIntegral_mono_on hfi.integrableOn hgi.integrableOn hS2m fun ω hω => ?_
    have h1 : C < (boxMean J n Φ ω).toReal := lt_of_not_ge hω.2
    simp only [hg, min_eq_left h1.le]
    exact hfC ω

/-- **Pathwise (F1)**: if `Φ_n ≤ Φ̄` for every `n`, then
`∑_n G_n(ω) ≤ θ ∫ Φ̄(ω, t) dt` (`J.slots`). -/
theorem sum_boxMean_le (Φ : ℕ → Ω × ℝ → ℝ≥0∞) (Φbar : Ω × ℝ → ℝ≥0∞) (ω : Ω)
    (hbar : Measurable fun t => Φbar (ω, t)) (hdom : ∀ n t, Φ n (ω, t) ≤ Φbar (ω, t)) :
    ∑' n, boxMean J n (Φ n) ω ≤ θE * ∫⁻ t, Φbar (ω, t) := by
  have hm : ∀ n, Measurable fun t => (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
      (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) := by
    intro n
    refine Measurable.mul ?_ hbar
    by_cases hω : ω ∈ J.A n
    · simp only [Set.indicator_of_mem hω]
      exact measurable_const.mul (measurable_one.indicator measurableSet_Ico)
    · simp only [Set.indicator_of_notMem hω]; exact measurable_const
  calc ∑' n, boxMean J n (Φ n) ω
      ≤ ∑' n, ∫⁻ t, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
          (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        unfold boxMean
        by_cases hω : ω ∈ J.A n
        · simp only [Set.indicator_of_mem hω]
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_indicator (show MeasurableSet (box (J.c n ω) (J.H n ω)) from
              measurableSet_Ico)]
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ box (J.c n ω) (J.H n ω)
          · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]
            exact mul_le_mul_right (hdom n t) _
          · simp [indicator_of_notMem ht]
        · simp [Set.indicator_of_notMem hω]
    _ = ∫⁻ t, ∑' n, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
          (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) :=
        (lintegral_tsum fun n => (hm n).aemeasurable).symm
    _ = ∫⁻ t, (∑' n, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
          (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω) * Φbar (ω, t) := by
        refine lintegral_congr fun t => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ t, θE * Φbar (ω, t) :=
        lintegral_mono fun t => mul_le_mul_left (J.slots ω t) _
    _ = θE * ∫⁻ t, Φbar (ω, t) := lintegral_const_mul _ hbar

end Gen

end BModel
