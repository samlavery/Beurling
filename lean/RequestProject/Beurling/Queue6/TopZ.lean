module

public import RequestProject.Beurling.Queue6.TopY
public import RequestProject.Beurling.Queue6.S2E2

/-!
# Theorem 2.1 / Corollary 2.2 with `Comp2Ident` reduced to (s2) for the windows of `𝓘_u`

`Margin.Comp2Ident` is proved from the named input `E2S2Bound` (eq. (s2) for the windows of
`𝓘_u`, read through the compensators of `1[X⁽²⁾_q(I) ≥ 1]`) and `s₂|I| ≤ 1` (`s2I_mul_le`, with
`log M₁ ≤ √L + log 2` from Theorem 6.23 Step 6, `logc_le_sqrt`). `QueueInputsZ θ X₀` asks for

* the variance inputs of Lemma 5.22 (`E3CompBound`, `E3S2Bound`);
* `R1Ident` a.s. on `Good(< b)` (Proposition 5.38 and the §5.3 bookkeeping);
* `E2S2Bound`.

* `Theorem21InputsZ`, `theorem21InputsY_of_Z`, `corollary_2_2_of_Z`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- **The remaining inputs**: Lemma 5.22 variance inputs, `R1Ident`, and (s2) on `𝓘_u`. -/
structure QueueInputsZ where
  compE3 : E3CompBound θ X₀
  s2E3 : E3S2Bound θ X₀
  r1Ident : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
    ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Margin.R1Ident θ X₀ m a b ω
  s2E2 : E2S2Bound θ X₀

variable {θ X₀}

/-- **`QueueInputsZ` gives `QueueInputsY`** (for `log X₀ ≥ 10⁸`): `Comp2Ident` by
`comp2Ident_of`. -/
noncomputable def queueInputsY_of_Z (hX : 10 ^ 8 ≤ Real.log X₀) (Q : QueueInputsZ θ X₀) :
    QueueInputsY θ X₀ where
  compE3 := Q.compE3
  s2E3 := Q.s2E3
  r1Ident := Q.r1Ident
  comp2Ident := comp2Ident_of hX Q.s2E2

/-- **Theorem 2.1, hypothesis**: Lemma 5.22 variance inputs, `R1Ident`, (s2) on `𝓘_u`. -/
def Theorem21InputsZ : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → Nonempty (QueueInputsZ θ X₀)

/-- `Theorem21InputsZ` implies `Theorem21InputsY`. -/
theorem theorem21InputsY_of_Z (h : Theorem21InputsZ) : Theorem21InputsY := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Q⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨queueInputsY_of_Z hlog Q⟩

/-- **Corollary 2.2** from `Theorem21InputsZ` and (84). -/
theorem corollary_2_2_of_Z (hHB : ShortIntervalPNT) (h : Theorem21InputsZ) : ¬ QuestionQ :=
  corollary_2_2_of_Y hHB (theorem21InputsY_of_Z h)

end Queue6

end
