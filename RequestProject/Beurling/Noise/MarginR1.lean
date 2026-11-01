module

public import RequestProject.Beurling.Noise.MarginCor
public import RequestProject.Beurling.Queue6.Family

/-!
# Corollary 5.40 in the form consumed by the queue front (`Queue6.QueueInputs.R1`, `.comp2`)

`Queue6.QueueInputs` (Theorem 6.6) takes Corollary 5.40 as two fields:

* `R1` : for every admissible window `[a, b)` at scale `m`, a.s. on `Good(< b)`, for every `n`,
  `0.399 (b - max(a, X₀))/log b - 2 ≤ ℓ_jit([a,b)) - ∑_{k<n} E[X_k | 𝓕_k]`;
* `comp2` : the same windows, `∑_{k<n} E[1[X⁽²⁾_k ≥ 1] | 𝓕_k] ≤ 1`.

Here we derive both fields (`r1Field_of`, `comp2Field_of`) from Corollary 5.40
(`Margin.cor_5_40`) and the following **identification hypotheses**, which link the objects of
§5 to those of the construction and are stated window by window, a.s. on `Good(< b)`:

* `R1Ident` : there are a margin density `m_ω` satisfying Proposition 5.38 in the form of
  Corollary 5.40 (`Margin.PointwiseMargin m_ω X₀`, interval-integrable on `[a, b]`) and a real
  `Comp` (the compensator `Comp(I)` of §5.3) such that
  - the bookkeeping identity `ℓ_jit(I) - Comp(I) = ∫_I m_ω ± 2` holds, and
  - every partial sum of the conditional means of the truncated counts `X_k` is at most
    `Comp(I)` (the paper: `Comp` is the compensator `Comp_jit` of §6, latest prime dividing
    once; the truncation only lowers it);
* `Comp2Ident` : every partial sum of the conditional means of `1[X⁽²⁾_k ≥ 1]` is at most
  `Comp⁽²⁾(I)`, Corollary 5.40's `Comp⁽²⁾(I) ≤ s₂|I|`, and `s₂|I| ≤ 1` (proof of
  Theorem 6.6(i): `s₂|I| ≤ e^{-√L}`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction Queue6

namespace Margin

variable (θ : ℝ) (X₀ : ℕ) (D : Sec5Family)

/-- **Identification for Corollary 5.40, first inequality** (see the module docstring), for the
window `[a, b)` at scale `m` and the sample `ω`. -/
def R1Ident (m : ℕ) (a b : ℤ) (ω : JitterΩ) : Prop :=
  ∃ (mω : ℝ → ℝ) (comp : ℝ), PointwiseMargin mω X₀ ∧
    IntervalIntegrable mω volume (a : ℝ) (b : ℝ) ∧
    |(ellIo θ X₀ a b ω : ℝ) - comp - ∫ t in (a : ℝ)..(b : ℝ), mω t| ≤ 2 ∧
    ∀ n, ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω ≤ comp

/-- **Identification for Corollary 5.40, `Comp⁽²⁾(I) ≤ s₂|I|`**, with `s₂|I| ≤ 1`. -/
def Comp2Ident (a b : ℤ) (ω : JitterΩ) : Prop :=
  ∃ comp2 s2 : ℝ, comp2 ≤ s2 * ((b : ℝ) - a) ∧ s2 * ((b : ℝ) - a) ≤ 1 ∧
    ∀ n, ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ comp2

/-- The type of the field `Queue6.QueueInputs.R1`. -/
def R1Field : Prop :=
  ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) → ∀ n,
    0.399 * ((b : ℝ) - max (a : ℝ) X₀) / Real.log b - 2 ≤
      (ellIo θ X₀ a b ω : ℝ) -
        ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω

/-- The type of the field `Queue6.QueueInputs.comp2`. -/
def Comp2Field : Prop :=
  ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ 1

/-- **Corollary 5.40 ⟹ the field `R1` of `Queue6.QueueInputs`**, given the identification
`R1Ident` a.s. on `Good(< b)` for every admissible window. -/
theorem r1Field_of (hX : 1 < (X₀ : ℝ))
    (hI : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      R1Ident θ X₀ m a b ω) :
    R1Field θ X₀ D := by
  intro m a b hadm
  filter_upwards [hI m a b hadm] with ω hω hG n
  obtain ⟨mω, comp, hpm, hint, hbook, hsum⟩ := hω hG
  obtain ⟨hub, -, hab, -⟩ := hadm
  have hu : (X₀ : ℝ) ≤ uS X₀ m := by
    unfold uS
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hb : (X₀ : ℝ) ≤ b := hu.trans hub
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hc := cor_5_40 hpm hX hab' hint
    (fun t ht htb => Real.log_le_log (by linarith) htb) hlb hbook
  have hmax : (b : ℝ) - max (a : ℝ) X₀ = max ((b : ℝ) - max (a : ℝ) X₀) 0 :=
    (max_eq_left (by rw [sub_nonneg]; exact max_le hab' hb)).symm
  rw [hmax]
  linarith [hsum n]

/-- **Corollary 5.40 (`Comp⁽²⁾(I) ≤ s₂|I|`) ⟹ the field `comp2` of `Queue6.QueueInputs`**. -/
theorem comp2Field_of
    (hI : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      Comp2Ident θ X₀ a b ω) :
    Comp2Field θ X₀ D := by
  intro m a b hadm
  filter_upwards [hI m a b hadm] with ω hω hG n
  obtain ⟨comp2, s2, h1, h2, hs⟩ := hω hG
  linarith [hs n]

end Margin

end

namespace Margin

/-- `R1Field` and `Comp2Field` are exactly the types of the fields `R1` and `comp2` of
`Queue6.QueueInputs`. -/
example (θ : ℝ) (X₀ : ℕ) (q : Queue6.QueueInputs θ X₀) :
    R1Field θ X₀ q.sec5 ∧ Comp2Field θ X₀ q.sec5 :=
  ⟨q.R1, q.comp2⟩

end Margin
