module

public import RequestProject.Beurling.Zeros48.Realised48

/-!
# Theorem 2.1 without the conjunct `Theorem410RestM` (Lemma 4.8(ii) is proved)

`Theorem410RestM` (the pieces of `D̂_{<a_k}` in the proof of Lemma 4.8(ii), `Lemma48PiecesCount`)
was a conjunct of `Theorem21InputsP`. It follows from the other conjuncts for the same `ω`
(`theorem410RestM_of_inputs`): they give the realised system, the target formula (6) and, through
the landing data and the queue data, the lag bound (13) (`lag_of_slotData`), from which
`lemma48PiecesCount_realised` gives `Lemma48PiecesCount` at every scale. `Theorem21InputsR` is
`Theorem21InputsP` without that conjunct; it implies Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Set MeasureTheory Construction Target Absorbed Decomp Oscillation CaplLink QueueMono
  SlotModel

namespace Zeros48

/-- **`Theorem410RestM` from the other conjuncts of `Theorem21InputsP`.** For
`θ ∈ [1/20, 1/2 - 10⁻⁴]`, `X₀` even with `X₀ ≥ e^{10⁸}`, jitters in `[0, 1]`, the arrival link,
the slot facts and the Part I data (target formula (6), queue window data) give the pieces of
Lemma 4.8(ii) at every scale. -/
theorem theorem410RestM_of_inputs {θ : ℝ} (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000))
    {X₀ : ℕ} (hev : Even X₀) (h1 : Real.exp (10 ^ 8) ≤ X₀) {M : SlotModel X₀} {ω : ℕ → ℝ}
    (hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1) (hlink : ArrivalsLinked M (capH X₀) ω) (hS : SlotFacts M ω)
    (hI : PartIRestO θ X₀ (realisedSystem M (capH X₀) ω) (realisedA M (capH X₀) ω)
      (fun n => solveU (thetaB θ) n) (constructionScale X₀) M) :
    Theorem410RestM θ X₀ (realisedSystem M (capH X₀) ω) (realisedA M (capH X₀) ω)
      (fun n => solveU (thetaB θ) n) := by
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  obtain ⟨hT, hq⟩ := hI
  have hreg := jitterWidthRegular hlog
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) := ⟨hθ, hlog, hω, hT, hlink⟩
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hinf : {k | placedAt M k}.Infinite :=
    placed_infinite_of_growth hω hlog hTlow (fun x hx => T_ge_of_formula hθ hlog hT hx) hlink
  have hok := realisedOK_of M hω hlog hTlow hinf
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hlag := lag_of_slotData hθ.1 hθ.2 hlog M (realisedSystem M (capH X₀) ω).N hq Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith [one_lt_of_logX hX0 hlog]), le_rfl⟩)
    (fun x hx _ => landing_of_linked L hS hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L hS hreg hok hx hearly)
  have h4 : 4 ≤ X₀ := by
    have := two_pow_le_of_logX hX0 hlog
    have : (4 : ℝ) ≤ X₀ := le_trans (by norm_num) this
    exact_mod_cast this
  have hXs := even_mem_smoothNumbers hev h4
  exact fun k => lemma48PiecesCount_realised hθ hlog hXs hω hok hT hlag k

end Zeros48

namespace Construction

/-- **Theorem 2.1, hypothesis on the concrete construction**: `Theorem21InputsP` without the
conjunct `Theorem410RestM` (Lemma 4.8(ii), now derived: `Zeros48.theorem410RestM_of_inputs`). -/
def Theorem21InputsR : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) →
        ArrivalsLinked (M ω) (capH X₀) ω ∧ SlotFacts (M ω) ω ∧
        PartIRestO θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) (constructionScale X₀) (M ω) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsR` implies `Theorem21InputsP`. -/
theorem theorem21InputsP_of_R (h : Theorem21InputsR) : Theorem21InputsP := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hlink, hS, hI, hcl⟩ := hP ω hG hω
  exact ⟨hlink, hS, hI, Zeros48.theorem410RestM_of_inputs hθ hev h1 hω hlink hS hI, hcl⟩

/-- Theorem 2.1 from `Theorem21InputsR`. -/
theorem theorem21_of_R (h : Theorem21InputsR) : Theorem21 :=
  theorem21_of_P (theorem21InputsP_of_R h)

/-- **Corollary 2.2** from `Theorem21InputsR`. -/
theorem corollary_2_2_of_R (h : Theorem21InputsR) : ¬ QuestionQ :=
  corollary_2_2_of_P (theorem21InputsP_of_R h)

end Construction

end
