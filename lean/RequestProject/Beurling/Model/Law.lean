module

public import RequestProject.Beurling.Construction.JitterRegular
public import RequestProject.Beurling.RankFull.PIL

/-!
# The conditional box-uniform law of a jitter given the past (§3.4, standing fact (F2))

On the jitter space, `U_{k+1}` is independent of the past `F_k` (`jitter_indep_past`). Here:

* `measurable_filtration_of_congr` : a measurable function that only reads the coordinates `≤ k`
  is `F_k`-measurable;
* `lintegral_jitter_succ` : for `Φ` measurable for `F_k ⊗ Borel`,
  `E[Φ(·, U_{k+1})] = E[∫_0^1 Φ(·, u) du]` (the joint law of the past and `U_{k+1}` is the
  product law; uniqueness of measures on the rectangles);
* `lintegral_landing` : **(F2)** for `F_k`-measurable `c`, `H > 0`, an event `A ∈ F_k` and the
  landing point `q = c + H (U_{k+1} - 1/2)` (box-centred jitter):
  `E[1_A Φ(·, q)] = E[1_A H⁻¹ ∫_{box} Φ(·, t) dt]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull
open scoped ENNReal

namespace BModel

/-- The extension of a finite segment of jitters by zeros. -/
noncomputable def extendLe (k : ℕ) (x : Iic k → ℝ) : JitterΩ :=
  fun j => if h : j ≤ k then x ⟨j, mem_Iic.mpr h⟩ else 0

lemma measurable_extendLe (k : ℕ) : Measurable (extendLe k) := by
  refine measurable_pi_lambda _ fun j => ?_
  unfold extendLe
  by_cases h : j ≤ k
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

/-- **A measurable function of the jitters `≤ k` is `F_k`-measurable.** -/
theorem measurable_filtration_of_congr {β : Type*} [MeasurableSpace β] {f : JitterΩ → β}
    (hf : Measurable f) (k : ℕ) (hc : ∀ ω ω' : JitterΩ, (∀ j ≤ k, ω j = ω' j) → f ω = f ω') :
    Measurable[jitterFiltration k] f := by
  have he : f = (f ∘ extendLe k) ∘ Preorder.restrictLe k := by
    funext ω
    simp only [Function.comp]
    refine hc _ _ fun j hj => ?_
    simp [extendLe, hj, Preorder.restrictLe]
  rw [he]
  exact (hf.comp (measurable_extendLe k)).comp (comap_measurable _)

/-- The jitter measure is a probability measure. -/
instance : IsProbabilityMeasure jitterMeasure := by
  unfold jitterMeasure; infer_instance

/-- **Integration against an independent coordinate.** If `U` is independent of `m` with law `ρ`,
then for `Φ` measurable for `m ⊗ Borel`, `E[Φ(·, U)] = E[∫ Φ(·, u) dρ(u)]`. -/
theorem lintegral_pair_eq {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ m0) {U : Ω → ℝ} (hU : Measurable U)
    (hind : Indep (MeasurableSpace.comap U inferInstance) m μ) {ρ : Measure ℝ}
    [IsFiniteMeasure ρ] (hρ : μ.map U = ρ) (Φ : Ω × ℝ → ℝ≥0∞)
    (hΦ : @Measurable (Ω × ℝ) ℝ≥0∞ (@Prod.instMeasurableSpace Ω ℝ m _) _ Φ) :
    ∫⁻ ω, Φ (ω, U ω) ∂μ = ∫⁻ ω, ∫⁻ u, Φ (ω, u) ∂ρ ∂μ := by
  let ν : @Measure Ω m := μ.trim hm
  haveI : @IsFiniteMeasure Ω m ν := isFiniteMeasure_trim hm
  letI mP : MeasurableSpace (Ω × ℝ) := @Prod.instMeasurableSpace Ω ℝ m _
  have hψ : @Measurable Ω (Ω × ℝ) m0 mP (fun ω => (ω, U ω)) :=
    @Measurable.prodMk Ω m0 Ω ℝ m _ id U (measurable_id.mono le_rfl hm) hU
  have hprod : @Measure.prod Ω ℝ m _ ν ρ = @Measure.map Ω (Ω × ℝ) m0 mP
      (fun ω => (ω, U ω)) μ := by
    refine @Measure.prod_eq Ω ℝ m _ ν _ ρ _ _ fun s t hs ht => ?_
    rw [@Measure.map_apply _ _ m0 mP _ _ hψ _ (@MeasurableSet.prod Ω ℝ m _ _ _ hs ht)]
    have he : (fun ω : Ω => (ω, U ω)) ⁻¹' (s ×ˢ t) = (U ⁻¹' t) ∩ s := by
      ext ω; simp [and_comm]
    rw [he, (Indep_iff _ _ _).mp hind _ _ ⟨t, ht, rfl⟩ hs, trim_measurableSet_eq hm hs,
      ← hρ, Measure.map_apply hU ht, mul_comm]
  have h1 : ∫⁻ ω, Φ (ω, U ω) ∂μ = @lintegral (Ω × ℝ) mP
      (@Measure.map Ω (Ω × ℝ) m0 mP (fun ω => (ω, U ω)) μ) Φ :=
    (@lintegral_map Ω (Ω × ℝ) m0 mP μ Φ _ hΦ hψ).symm
  rw [h1, ← hprod, @lintegral_prod Ω ℝ m _ ν ρ _ Φ hΦ.aemeasurable]
  exact lintegral_trim hm (@Measurable.lintegral_prod_right' Ω ℝ m _ ρ _ Φ hΦ)

/-- **The joint law of the past and the next jitter is the product law.** -/
theorem lintegral_jitter_succ (k : ℕ) {Φ : JitterΩ × ℝ → ℝ≥0∞}
    (hΦ : JMeas (jitterFiltration k) Φ) :
    ∫⁻ ω, Φ (ω, ω (k + 1)) ∂jitterMeasure =
      ∫⁻ ω, ∫⁻ u, Φ (ω, u) ∂unif01 ∂jitterMeasure :=
  lintegral_pair_eq (jitterFiltration.le k) (measurable_jitter (k + 1)) (jitter_indep_past k)
    (jitter_map (k + 1)) Φ hΦ

/-- The clamp of a jitter to `[0, 1]`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min 1 u)

lemma clamp01_mem (u : ℝ) : clamp01 u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp01_eq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : clamp01 u = u := by
  unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]

lemma measurable_clamp01 : Measurable clamp01 :=
  measurable_const.max (measurable_const.min measurable_id)

/-- The law of the landing point: `ρ ∘ landing⁻¹ = H⁻¹ λ|_{[s - H/2, s + H/2]}`. -/
lemma map_landing {s H : ℝ} (hH : 0 < H) :
    unif01.map (landing s H) =
      ENNReal.ofReal H⁻¹ • volume.restrict (Icc (s - H / 2) (s + H / 2)) := by
  have hmeas : Measurable (landing s H) := by
    unfold landing; fun_prop
  ext B hB
  rw [Measure.map_apply hmeas hB, landing_law hH B, Measure.smul_apply,
    Measure.restrict_apply hB, smul_eq_mul, ENNReal.div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos hH]

/-- **(F2): the box-uniform landing law given the past.** For `F_k`-measurable `c`, `H > 0`, an
event `A ∈ F_k` and `Φ` measurable for `F_k ⊗ Borel`, with the landing point
`q = c + H (U_{k+1} - 1/2)`:
`E[1_A Φ(·, q)] = E[1_A H⁻¹ ∫_{[c - H/2, c + H/2)} Φ(·, t) dt]`. -/
theorem lintegral_landing (k : ℕ) {c H : JitterΩ → ℝ} (hc : Measurable[jitterFiltration k] c)
    (hHm : Measurable[jitterFiltration k] H) (hH : ∀ ω, 0 < H ω) {A : Set JitterΩ}
    (hA : MeasurableSet[jitterFiltration k] A) {Φ : JitterΩ × ℝ → ℝ≥0∞}
    (hΦ : JMeas (jitterFiltration k) Φ) :
    ∫⁻ ω, A.indicator (fun ω => Φ (ω, landing (c ω) (H ω) (clamp01 (ω (k + 1))))) ω
        ∂jitterMeasure =
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (H ω)⁻¹ *
        ∫⁻ t in box (c ω) (H ω), Φ (ω, t)) ω ∂jitterMeasure := by
  set m : MeasurableSpace JitterΩ := jitterFiltration k
  letI mP : MeasurableSpace (JitterΩ × ℝ) := @Prod.instMeasurableSpace JitterΩ ℝ m _
  set Ψ : JitterΩ × ℝ → ℝ≥0∞ := fun p =>
    A.indicator (fun ω => Φ (ω, landing (c ω) (H ω) (clamp01 p.2))) p.1 with hΨ
  have hΨm : JMeas m Ψ := by
    unfold JMeas
    have hg : @Measurable (JitterΩ × ℝ) (JitterΩ × ℝ) mP mP
        (fun p => (p.1, landing (c p.1) (H p.1) (clamp01 p.2))) := by
      refine @Measurable.prodMk _ mP _ _ m _ _ _ (@measurable_fst _ _ m _) ?_
      unfold landing
      refine (hc.comp (@measurable_fst _ _ m _)).add
        ((hHm.comp (@measurable_fst _ _ m _)).mul
          ((measurable_clamp01.comp (@measurable_snd _ _ m _)).sub_const _))
    have h1 : @Measurable (JitterΩ × ℝ) ℝ≥0∞ mP _
        (fun p => Φ (p.1, landing (c p.1) (H p.1) (clamp01 p.2))) := hΦ.comp hg
    have h2 : Ψ = (A ×ˢ (univ : Set ℝ)).indicator
        (fun p => Φ (p.1, landing (c p.1) (H p.1) (clamp01 p.2))) := by
      funext p
      by_cases hp : p.1 ∈ A <;> simp [hΨ, Set.indicator, Set.mem_prod, hp]
    rw [h2]
    exact h1.indicator (@MeasurableSet.prod _ _ m _ _ _ hA MeasurableSet.univ)
  have h := lintegral_jitter_succ k hΨm
  have hl : ∫⁻ ω, A.indicator (fun ω => Φ (ω, landing (c ω) (H ω) (clamp01 (ω (k + 1))))) ω
      ∂jitterMeasure = ∫⁻ ω, Ψ (ω, ω (k + 1)) ∂jitterMeasure := by
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A <;> simp [hΨ, Set.indicator, hω]
  rw [hl, h]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω]
    have hΨω : (fun u => Ψ (ω, u)) = fun u => Φ (ω, landing (c ω) (H ω) (clamp01 u)) := by
      funext u; simp [hΨ, Set.indicator_of_mem hω]
    rw [hΨω]
    have hae : ∀ᵐ u ∂unif01, Φ (ω, landing (c ω) (H ω) (clamp01 u)) =
        Φ (ω, landing (c ω) (H ω) u) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [clamp01_eq hu]
    rw [lintegral_congr_ae hae]
    have hl : Measurable (landing (c ω) (H ω)) := by unfold landing; fun_prop
    have hΦω : Measurable fun t => Φ (ω, t) :=
      hΦ.comp (@Measurable.prodMk _ _ _ _ m _ _ _ measurable_const measurable_id)
    rw [← lintegral_map hΦω hl, map_landing (hH ω), lintegral_smul_measure]
    congr 1
    unfold box
    exact setLIntegral_congr Ico_ae_eq_Icc |>.symm
  · simp [hΨ, Set.indicator_of_notMem hω]

end BModel

end
