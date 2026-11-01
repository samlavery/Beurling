module

public import RequestProject.Beurling.Model.CondBox
public import RequestProject.Beurling.Model.MarginObjects

/-!
# The conditional landing law as an equality (§6.1, (F2) for the uniform jitter)

The jitter `U_{k+1}` is uniform on `[0, 1]` and independent of `𝓕_k`, so given `𝓕_k` the landing
point `q_k = s + H (U - 1/2)` is uniform on the box `[s - H/2, s + H/2)`: `lintegral_landing` is an
equality of integrals over `𝓕_k`-sets. Hence, for `0 ≤ f ≤ C` with `f = 1_{A_k} Φ(·, q_k)`
(`Φ` jointly `𝓕_k`-measurable),

* `condExp_eq_boxMean` : `E[f | 𝓕_k] = 1_{A_k} H_k⁻¹ ∫_{box_k} Φ` almost surely

(the equality form of `condExp_le_boxMean`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction RankFull CaplLink
open scoped ENNReal

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc

/-- `∫⁻_S 1_{A_k} Φ(·, q_k) = ∫⁻_S G_k` for `𝓕_k`-sets `S` (`lintegral_landing`). -/
lemma setLIntegral_landing (k : ℕ) {Φ : JitterΩ × ℝ → ℝ≥0∞}
    (hΦ : ∀ S, MeasurableSet[jitterFiltration k] S →
      JMeas (jitterFiltration k) fun p => S.indicator 1 p.1 * Φ p)
    {S : Set JitterΩ} (hS : MeasurableSet[jitterFiltration k] S) :
    ∫⁻ ω in S, (lawA θ X₀ k).indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω ∂jitterMeasure =
      ∫⁻ ω in S, (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
        ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)) ω ∂jitterMeasure := by
  have hSm : MeasurableSet S := jitterFiltration.le k _ hS
  have h := lintegral_landing k (slotF_adapted hc (stageMeas hc) k)
    (HF_adapted hc (stageMeas hc) k) (HF_pos hc k) (lawA_adapted hc k) (hΦ S hS)
  rw [← lintegral_indicator hSm, ← lintegral_indicator hSm]
  have e1 : (S.indicator fun ω => (lawA θ X₀ k).indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω) =
      fun ω => (lawA θ X₀ k).indicator (fun ω => S.indicator 1 ω * Φ (ω,
        landing (slotF θ X₀ k ω) (HF θ X₀ k ω) (clamp01 (ω (k + 1))))) ω := by
    funext ω
    by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ lawA θ X₀ k <;>
      simp [Set.indicator, h1, h2, valF_eq]
  have e2 : (S.indicator fun ω => (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal
      (HF θ X₀ k ω)⁻¹ * ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)) ω) =
      fun ω => (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
        ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), S.indicator 1 ω * Φ (ω, t)) ω := by
    funext ω
    by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ lawA θ X₀ k <;>
      simp [Set.indicator, h1, h2]
  rw [e1, e2]
  exact h

include hev in
/-- **The conditional mean under the uniform jitter**: for measurable `0 ≤ f ≤ C` with
`f = 1_{A_k} Φ(·, q_k)` a.s., `E[f | 𝓕_k] = G_k` a.s., `G_k = 1_{A_k} H_k⁻¹ ∫_{box_k} Φ`. -/
theorem condExp_eq_boxMean (k : ℕ) {f : JitterΩ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfC : ∀ ω, f ω ≤ C) (hfm : Measurable f) {Φ : JitterΩ × ℝ → ℝ≥0∞}
    (hΦ : ∀ S, MeasurableSet[jitterFiltration k] S →
      JMeas (jitterFiltration k) fun p => S.indicator 1 p.1 * Φ p)
    (hfΦ : ∀ᵐ ω ∂jitterMeasure,
      ENNReal.ofReal (f ω) = (lawA θ X₀ k).indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω)
    (hfin : ∀ ω, boxMean (constructionLaw hc hev) k Φ ω ≠ ∞) :
    jitterMeasure[f | jitterFiltration k] =ᵐ[jitterMeasure]
      fun ω => (boxMean (constructionLaw hc hev) k Φ ω).toReal := by
  set J := constructionLaw hc hev
  have hFle := jitterFiltration.le k
  have hΦ1 : JMeas (jitterFiltration k) Φ := by
    have := hΦ univ MeasurableSet.univ
    simpa using this
  have hGm : Measurable[jitterFiltration k] (boxMean J k Φ) := boxMean_meas J k hΦ1
  set g : JitterΩ → ℝ := fun ω => (boxMean J k Φ ω).toReal with hg
  have hgm : StronglyMeasurable[jitterFiltration k] g :=
    (ENNReal.measurable_toReal.comp hGm).stronglyMeasurable
  have hfi : Integrable f jitterMeasure :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hfC ω)
  -- the lintegral identity on `𝓕_k`-sets
  have hlin : ∀ S, MeasurableSet[jitterFiltration k] S →
      ∫⁻ ω in S, ENNReal.ofReal (f ω) ∂jitterMeasure =
        ∫⁻ ω in S, boxMean J k Φ ω ∂jitterMeasure := by
    intro S hS
    have hSm : MeasurableSet S := hFle _ hS
    rw [setLIntegral_congr_fun_ae hSm (hfΦ.mono fun ω h _ => h)]
    exact setLIntegral_landing hc k hΦ hS
  have hG_fin : ∫⁻ ω, boxMean J k Φ ω ∂jitterMeasure ≠ ∞ := by
    have h := hlin univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal C ∂jitterMeasure) ?_
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hfC ω))
    rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hgi : Integrable g jitterMeasure := by
    refine ⟨(hgm.mono hFle).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)]
    exact (ne_top_of_le_ne_top hG_fin
      (lintegral_mono fun ω => ENNReal.ofReal_toReal_le)).lt_top
  refine (ae_eq_condExp_of_forall_setIntegral_eq hFle hfi (fun s _ _ => hgi.integrableOn)
    (fun S hS _ => ?_) (hgm.aestronglyMeasurable)).symm
  have hSm : MeasurableSet S := hFle _ hS
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hgi.aestronglyMeasurable.restrict,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hfi.aestronglyMeasurable.restrict, hlin S hS]
  congr 1
  refine setLIntegral_congr_fun_ae hSm (Filter.Eventually.of_forall fun ω _ => ?_)
  have hne : boxMean J k Φ ω ≠ ∞ := hfin ω
  simp only [ENNReal.ofReal_toReal hne]

end Queue6

end
