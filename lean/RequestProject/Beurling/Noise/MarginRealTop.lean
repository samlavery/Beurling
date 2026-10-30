module

public import RequestProject.Beurling.Model.TopM
public import RequestProject.Beurling.Queue6.TNPHyp

/-!
# Proposition 5.38 is needed only up to the window: the local interface for the top level

`BModel.Theorem21InputsM` asks for `PointwiseMargin (marginM θ X₀ ω) X₀` — the margin at
**every** height `t ≥ X₀` — a.s. on `Good(< b)`. That event controls the construction only up to
its horizon (on `Good(< z)`, (HBS) holds on `[1, ž]`, `ž = z - 12 log z - 3`, Remark *horizon*;
Model's `hbs_local` reads the queue and cluster events only at heights `≤ Z`), so the margin
above the horizon is not determined by it, and the unbounded statement is not what Corollary 5.40
uses: on the window `[a, b)` it reads `m` only on `[a, b]`.

This file states the margin only where it is used:

* `PointwiseMarginOn m X₀ T` : `0.399 ≤ m t log t` for `X₀ ≤ t ≤ T`, and `m = 0` below `X₀`;
* `pointwiseMargin_extendM` : the function equal to `m` on `(-∞, T]` and to `1` above satisfies the
  global `PointwiseMargin` (`log t ≥ log X₀ ≥ 0.399` above `T`);
* `r1Ident_of_marginOn` : `Margin.R1Ident` on every admissible window `[a, b)`, a.s. on
  `Good(< b)`, from `PointwiseMarginOn (marginM θ X₀ ω) X₀ b` (`R1Ident` is existential in the
  margin function, so the extension is admissible: it agrees with `marginM` on `[a, b]`);
* `Theorem21InputsMOn`, `corollary_2_2_of_MOn` : the top level with the local margin.

Also `twR_eq` : the decision times of `MarginObjects` (`BModel.twR`, read through
`realisedSrc`) and of `Queue6.TNPHyp` (`Queue6.twR`, read through `decT`) coincide, so
`Queue6.tnpHyp_R` applies to `KptR`'s decision order.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueMono Queue6

namespace BModel

/-- **Proposition 5.38 up to the height `T`**: `0.399 ≤ m(t) log t` on `[X₀, T]`, `m = 0` below
`X₀`. -/
structure PointwiseMarginOn (m : ℝ → ℝ) (X0 T : ℝ) : Prop where
  ge : ∀ t, X0 ≤ t → t ≤ T → 0.399 ≤ m t * Real.log t
  zero : ∀ t, t < X0 → m t = 0

/-- `m` on `(-∞, T]`, `1` above. -/
noncomputable def extendM (m : ℝ → ℝ) (T : ℝ) (t : ℝ) : ℝ := if t ≤ T then m t else 1

lemma pointwiseMargin_extendM {m : ℝ → ℝ} {X0 T : ℝ} (h : PointwiseMarginOn m X0 T)
    (hX : 0.399 ≤ Real.log X0) (hX1 : 1 < X0) (hT : X0 ≤ T) :
    Margin.PointwiseMargin (extendM m T) X0 where
  ge t ht := by
    unfold extendM
    split_ifs with htT
    · exact h.ge t ht htT
    · rw [one_mul]; exact hX.trans (Real.log_le_log (by linarith) ht)
  zero t ht := by
    unfold extendM
    rw [if_pos (by linarith)]; exact h.zero t ht

lemma extendM_eqOn {m : ℝ → ℝ} {T a : ℝ} (hab : a ≤ T) :
    EqOn (extendM m T) m (Set.uIcc a T) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  unfold extendM; rw [if_pos ht.2]

section R1

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`R1Ident` from the local Proposition 5.38**: the margin is needed on `[X₀, b]` only. -/
theorem r1Ident_of_marginOn (D : Sec5Family)
    (hPM : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      PointwiseMarginOn (marginM θ X₀ ω) X₀ b) :
    ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      Margin.R1Ident θ X₀ m a b ω := by
  intro m a b hadm
  have hadm' := hadm
  obtain ⟨hub, -, hab, -⟩ := hadm'
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  filter_upwards [hPM m a b hadm, compSum_le hc hev m hab, hnice] with ω hP hS hN hG
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hb : (X₀ : ℝ) ≤ b := (X₀_le_uS (X₀ := X₀) (by linarith) m).trans hub
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨hTi, -⟩ := integral_TpCont hc ω hab' hb
  have hmi : IntervalIntegrable (marginM θ X₀ ω) volume (a : ℝ) (b : ℝ) :=
    hTi.sub (compR_intervalIntegrable hc hev ω hab')
  have hlog : (0.399 : ℝ) ≤ Real.log X₀ := by have := hc.hX; norm_num at this ⊢; linarith
  have hEq := extendM_eqOn (m := marginM θ X₀ ω) hab'
  have hint : ∫ t in (a : ℝ)..(b : ℝ), extendM (marginM θ X₀ ω) b t =
      ∫ t in (a : ℝ)..(b : ℝ), marginM θ X₀ ω t :=
    intervalIntegral.integral_congr hEq
  refine ⟨extendM (marginM θ X₀ ω) b, ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal,
    pointwiseMargin_extendM (hP hG) hlog hX1 hb,
    (hmi.congr (hEq.symm.mono Set.uIoc_subset_uIcc)), ?_, hS⟩
  rw [hint]
  exact bookkeeping_m hc hev hN hab hb

end R1

/-- **Theorem 2.1, hypothesis, local form**: the second branch of (s2), and Proposition 5.38 for
the margin density of the construction on `[X₀, b]`, a.s. on `Good(< b)`. -/
def Theorem21InputsMOn : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
      S2SecondBranch θ X₀ ∧
      ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
        ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → PointwiseMarginOn (marginM θ X₀ ω) X₀ b

/-- The global form implies the local one. -/
theorem theorem21InputsMOn_of_M (h : Theorem21InputsM) : Theorem21InputsMOn := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨hS, hPM⟩ := hX X₀ hev h1 h2
  refine ⟨hS, fun m a b hadm => ?_⟩
  filter_upwards [hPM m a b hadm] with ω hω hG
  exact ⟨fun t ht _ => (hω hG).ge t ht, (hω hG).zero⟩

/-- `Theorem21InputsMOn` implies `Theorem21InputsZ`, given (84). -/
theorem theorem21InputsZ_of_MOn (hHB : ShortIntervalPNT) (h : Theorem21InputsMOn) :
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
           r1Ident := r1Ident_of_marginOn hc hev (e3Family θ X₀) hPM
           s2E2 := e2S2Bound_of hc hev hcore }⟩

/-- **Corollary 2.2** from the local form `Theorem21InputsMOn` and (84). -/
theorem corollary_2_2_of_MOn (hHB : ShortIntervalPNT) (h : Theorem21InputsMOn) :
    ¬ QuestionQ :=
  corollary_2_2_of_Z hHB (theorem21InputsZ_of_MOn hHB h)

/-! ## The two decision orders agree -/

theorem twR_eq {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (ω : JitterΩ) :
    BModel.twR θ X₀ ω = Queue6.twR (hokR hc ω) := by
  classical
  funext r
  unfold BModel.twR Queue6.twR
  by_cases hr : r.Prime
  · have hex : ∃ j, BeurlingSystem.qp j = r := ⟨Nat.count Nat.Prime r, Nat.nth_count hr⟩
    rw [if_pos hr, dif_pos hex]
    have hj : hex.choose = Nat.count Nat.Prime r := by
      apply BeurlingSystem.qp_injective
      rw [hex.choose_spec]; exact (Nat.nth_count hr).symm
    rw [hj, realisedSrc_eq (hokR hc ω), realisedSystem_p (hokR hc ω)]
    rcases (hokR hc ω).equiv (Nat.count Nat.Prime r) with p | k
    · rfl
    · rfl
  · rw [if_neg hr, dif_neg]
    rintro ⟨j, hj⟩
    exact hr (hj ▸ BeurlingSystem.qp_prime j)

end BModel

end
