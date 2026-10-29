module

public import RequestProject.Beurling.Queue6.TopX
public import RequestProject.Beurling.Noise.MarginR1

/-!
# Theorem 2.1 / Corollary 2.2 with Corollary 5.40 plugged in

Corollary 5.40 is proved by §5 (`Margin.r1Field_of`, `Margin.comp2Field_of`) in the form of the
fields `R1`, `comp2`, from the identification statements of §5.3 (`Margin.R1Ident`,
`Margin.Comp2Ident`). `QueueInputsY θ X₀` asks for

* the two variance inputs of the proof of Lemma 5.22 (`E3CompBound`, `E3S2Bound`);
* `R1Ident` a.s. on `Good(< b)` for every window of `𝓘_u`: the pointwise margin density `m_ω`
  with Proposition 5.38 (`PointwiseMargin`), the bookkeeping identity of §5.3
  `ℓ_jit(I) - Comp(I) = ∫_I m ± 2`, and "`Comp` is the compensator `Comp_jit`" (the partial
  compensators of the truncated counts are at most `Comp(I)`);
* `Comp2Ident` a.s. on `Good(< b)`: `Comp⁽²⁾(I) ≤ s₂|I| ≤ 1` with the compensators of
  `1[X⁽²⁾_q(I) ≥ 1]` at most `Comp⁽²⁾(I)`.

`R1Ident` is read through the conditional means of the **truncated** counts `X̃_q(I)` only (an
upper bound by `Comp(I)`), so no statement about the untruncated martingale ("truncation
inactive on `Good`") is needed here.

* `Theorem21InputsY`, `theorem21InputsX_of_Y`, `corollary_2_2_of_Y`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs**: the variance inputs of Lemma 5.22 and the §5.3 identifications
behind Corollary 5.40. -/
structure QueueInputsY where
  compE3 : E3CompBound θ X₀
  s2E3 : E3S2Bound θ X₀
  r1Ident : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
    ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Margin.R1Ident θ X₀ m a b ω
  comp2Ident : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
    ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Margin.Comp2Ident θ X₀ a b ω

variable {θ X₀}

/-- **`QueueInputsY` gives `QueueInputsX`**: `R1`, `comp2` by Corollary 5.40. -/
noncomputable def queueInputsX_of_Y (hX : 1 < (X₀ : ℝ)) (Q : QueueInputsY θ X₀) :
    QueueInputsX θ X₀ where
  compE3 := Q.compE3
  s2E3 := Q.s2E3
  R1 := Margin.r1Field_of θ X₀ (e3Family θ X₀) hX Q.r1Ident
  comp2 := Margin.comp2Field_of θ X₀ (e3Family θ X₀) Q.comp2Ident

/-- **Theorem 2.1, hypothesis with §6 formalized and Corollary 5.40 plugged in.** -/
def Theorem21InputsY : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsY θ X₀)

/-- `Theorem21InputsY` implies `Theorem21InputsX`. -/
theorem theorem21InputsX_of_Y (h : Theorem21InputsY) : Theorem21InputsX := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Q⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨queueInputsX_of_Y (QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hlog) Q⟩

/-- **Corollary 2.2** from `Theorem21InputsY` and (84). -/
theorem corollary_2_2_of_Y (hHB : ShortIntervalPNT) (h : Theorem21InputsY) : ¬ QuestionQ :=
  corollary_2_2_of_X hHB (theorem21InputsX_of_Y h)

end Queue6

end
