module

public import RequestProject.Beurling.Model.S2Second
public import RequestProject.Beurling.Model.S2Block
public import RequestProject.Beurling.Model.TopM

/-!
# Eq. (s2) of Lemma 5.22, both bounds, and Theorem 2.1 / Corollary 2.2 up to Proposition 5.38

* `blockBound` : `BlockBound X₀` (from `BeurlingSystem.block_le`, `S2Block.lean`);
* `s2SecondBranch` : the second bound of (s2) (04d-noise.tex, "Second bound, for
  `σ > log X₀⁻`"), `S2SecondBranch θ X₀`;
* `s2Core` : eq. (s2) for every window `v/4 ≤ a < b ≤ 2v` (both bounds);
* `Theorem21InputsP` : the remaining input of Theorem 2.1, Proposition 5.38 (`PointwiseMargin`
  for the margin density `marginM`) a.s. on `Good(< b)`; `corollary_2_2_of_P`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink Queue6

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **The block bound** (04d-noise.tex l.58–80) holds. -/
theorem blockBound : BlockBound X₀ := by
  intro P Z h hℓ v hv hσ hZ c hc Y hY0 hYv
  exact P.block_le h hℓ hv hσ hZ hc hY0 hYv

/-- **The second bound of (s2)** (04d-noise.tex, "Second bound, for `σ > log X₀⁻`"). -/
theorem s2SecondBranch (hc : Cond θ X₀) (hev : Even X₀) : S2SecondBranch θ X₀ :=
  s2_second_of_block hc hev blockBound

/-- **Eq. (s2) of Lemma 5.22** for every window `v/4 ≤ a < b ≤ 2v`. -/
theorem s2Core (hc : Cond θ X₀) (hev : Even X₀) : S2Core θ X₀ :=
  s2Core_of hc hev (s2SecondBranch hc hev)

/-- **Theorem 2.1, hypothesis**: Proposition 5.38 for the margin density of the construction,
a.s. on `Good(< t(E2))`. -/
def Theorem21InputsP : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
      ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
        ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Margin.PointwiseMargin (marginM θ X₀ ω) X₀

/-- `Theorem21InputsP` implies `Theorem21InputsZ`, given (84): eq. (s2) is proved
(`s2Core`). -/
theorem theorem21InputsZ_of_P (hHB : ShortIntervalPNT) (h : Theorem21InputsP) :
    Theorem21InputsZ := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  have hPM := hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono ((le_max_right _ _).trans h2)⟩
  have hcore := s2Core hc hev
  exact ⟨{ compE3 := e3CompBound hc hev
           s2E3 := e3S2Bound_of hc hev hcore
           r1Ident := r1Ident_of_margin hc hev (e3Family θ X₀) hPM
           s2E2 := e2S2Bound_of hc hev hcore }⟩

/-- **Corollary 2.2** from `Theorem21InputsP` (Proposition 5.38 for the margin density) and
(84). -/
theorem corollary_2_2_of_P (hHB : ShortIntervalPNT) (h : Theorem21InputsP) : ¬ QuestionQ :=
  corollary_2_2_of_Z hHB (theorem21InputsZ_of_P hHB h)

end BModel
