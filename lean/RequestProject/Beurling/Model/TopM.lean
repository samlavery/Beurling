module

public import RequestProject.Beurling.Model.MarginObjects
public import RequestProject.Beurling.Model.E3S2
public import RequestProject.Beurling.Queue6.TopZ

/-!
# Theorem 2.1 / Corollary 2.2 with the inputs of `Queue6.QueueInputsZ` proved, up to the
second branch of (s2) and Proposition 5.38

`Queue6.QueueInputsZ θ X₀` is built from

* `e3CompBound` (Lemma 5.22, the variance bound, proved);
* `e3S2Bound_of`, `e2S2Bound_of` (eq. (s2), from the core statement `S2Core`, proved in the first
  branch and from the named second branch `S2SecondBranch`);
* `r1Ident_of_margin` (`R1Ident` from the §5.3 bookkeeping and compensator identification,
  proved, and `PointwiseMargin` for the margin density `marginM` — Proposition 5.38, the §5
  front).

`Theorem21InputsM` asks only for `S2SecondBranch` (the "Second bound, for `σ > log X₀⁻`" of
Lemma 5.22's (s2)) and `PointwiseMargin (marginM θ X₀ ω) X₀` (Proposition 5.38) a.s. on
`Good(< b)`; `corollary_2_2_of_M` derives Corollary 2.2.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink Queue6

namespace BModel

/-- **Theorem 2.1, hypothesis**: the second branch of (s2) and Proposition 5.38 for the margin
density of the construction. -/
def Theorem21InputsM : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
      S2SecondBranch θ X₀ ∧
      ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
        ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Margin.PointwiseMargin (marginM θ X₀ ω) X₀

/-- `Theorem21InputsM` implies `Theorem21InputsZ`, given (84). -/
theorem theorem21InputsZ_of_M (hHB : ShortIntervalPNT) (h : Theorem21InputsM) :
    Theorem21InputsZ := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨hS, hPM⟩ := hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono ((le_max_right _ _).trans h2)⟩
  have hcore := s2Core_of hc hev hS
  exact ⟨{ compE3 := e3CompBound hc hev
           s2E3 := e3S2Bound_of hc hev hcore
           r1Ident := r1Ident_of_margin hc hev (e3Family θ X₀) hPM
           s2E2 := e2S2Bound_of hc hev hcore }⟩

/-- **Corollary 2.2** from `Theorem21InputsM` and (84). -/
theorem corollary_2_2_of_M (hHB : ShortIntervalPNT) (h : Theorem21InputsM) : ¬ QuestionQ :=
  corollary_2_2_of_Z hHB (theorem21InputsZ_of_M hHB h)

end BModel
