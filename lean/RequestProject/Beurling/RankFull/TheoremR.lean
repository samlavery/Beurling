module

public import RequestProject.Beurling.RankFull.BlockBound
public import RequestProject.Beurling.RankFull.PatternSum
public import RequestProject.Beurling.RankFull.CorR
public import RequestProject.Beurling.RankFull.PatternTail
public import RequestProject.Beurling.Covers

/-!
# Theorem A.12 (Theorem R) and Proposition 6.11 (the cluster event), abstractly

The probabilistic inputs of Theorem A.12 are isolated as named hypotheses about an abstract
probability space; everything else (the sum over the pivot patterns, Lemma A.3; the sum over the
run structures, the `k^k/k!` of entry #55; the bookkeeping) is proved.

## Theorem A.12

A *skeleton* of a rank-full `k`-configuration is a pair `(E_P, l)` of an invertible pivot pattern
`E_P ∈ ℕ^{k×k}` (columns in decision order) and a run structure `l ∈ comps k`. For each skeleton,
`X (E_P, l) : Ω → ℝ≥0∞` is the number of ordered configurations with that skeleton
(Lemma A.5's `X_𝔰`).

* `SkeletonReduction` (the reduction step of the proof of Theorem A.12; pathwise counting): a
  `k`-subset of rank `k` has `k!` orderings, each with exactly one skeleton, so
  `k! · #{rank-k k-subsets} ≤ ∑_{E_P} ∑_l X(E_P, l)`.
* `SkeletonBound` (**Lemma A.5 + Theorem A.10, evaluated with the cover `C = B'`**, as in the
  "One skeleton" step of the proof of Theorem A.12): for every skeleton,
  `E[X(E_P, l); Good(<t_J)] ≤ θ^k δ^k ∏_j τ_j^{-(s_j-1)} Fin(l)`, with
  `Fin(l) = G_T(Eu_rat) + Eu_rat^{j_T} G_{T-1}(Eu_rat)` (`finG A_top l Eu_rat`).

`RankFull.theorem_R` : from these two, `E[#{rank-k k-subsets}; Good] ≤
(k^k/k!) (θ A_top δ)^k ∏_j (1 - 1/τ_j)^{-k}`.
`RankFull.theorem_R_second_line` : the second line of Theorem A.12 from the first, given
Lemma A.3's second inequality `∏_j (1 - 1/τ_j)^{-k} ≤ a^k u^{1.02k}` and `A_top ≤ A_R b`.

## Proposition 6.11

`RankFull.prop_6_11` : `P(E_cl(z)ᶜ ∩ Good(<t_z)) ≤ L^{-2}`, from
* the rank-`≥ r₀` bound `∑_J E[#{rank-r₀ r₀-subsets of S(J)}; Good] ≤ L^{-4}` (Theorem A.12 with
  Corollary A.13; see `prop_6_11_of_theorem_R`), and
* Theorem 6.23(a): `P(∃ J, rank S(J) < r₀ ∧ |S(J)| ≥ r₀ + φ(r₀); Good) ≤ L^{-3}`,
with `M₁ = r₀ + φ(r₀) + 1`, `L ≥ 465`, and `#(N ∩ J) ≤ |S(J)| + 1` (at most one element of a window
has no jittered prime). The exponent vectors are in `Fin m → ℕ` (any fixed `m`; the jittered
primes below `2z + 1` can be indexed by `Fin m`).
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal

namespace RankFull

instance (k : ℕ) : Countable (Matrix (Fin k) (Fin k) ℕ) :=
  inferInstanceAs (Countable (Fin k → Fin k → ℕ))

/-! ## Theorem A.12 -/

/-- The invertible pivot patterns (over `ℚ`). -/
def InvPattern (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℕ) :=
  {E | (E.map (Nat.cast : ℕ → ℚ)).det ≠ 0}

/-- The weight `∏_j τ_j^{-(s_j - 1)}` of a pivot pattern. -/
noncomputable def patternWeight {k : ℕ} (τ : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) : ℝ :=
  ∏ j, (τ j)⁻¹ ^ ((∑ i, E i j) - 1)

/-- **Reduction to skeletons** (proof of Theorem A.12; pathwise). -/
def SkeletonReduction {Ω : Type*} (k : ℕ) (N : Ω → ℝ≥0∞)
    (X : Matrix (Fin k) (Fin k) ℕ → List ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ ω, (k.factorial : ℝ≥0∞) * N ω ≤
    ∑' E, (InvPattern k).indicator (fun E => ∑ l ∈ comps k, X E l ω) E

/-- **Lemma A.5 + Theorem A.10 with the cover `C = B'`** ("One skeleton" in the proof of
Theorem A.12): `E[X_𝔰; Good(<t_J)] ≤ θ^k δ^k ∏_j τ_j^{-(s_j-1)} Fin(𝔰)`. -/
def SkeletonBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω) (k : ℕ)
    (θ δ A Eu : ℝ) (τ : Fin k → ℝ) (X : Matrix (Fin k) (Fin k) ℕ → List ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ E ∈ InvPattern k, ∀ l ∈ comps k,
    ∫⁻ ω in Good, X E l ω ∂P ≤
      ENNReal.ofReal (θ ^ k * δ ^ k * patternWeight τ E * finG A l Eu)

/-- **Theorem A.12 (Theorem R)**, first line, with the pattern sum in the form
`∏_j (1 - 1/τ_j)^{-k}` (Lemma A.3, first inequality). -/
theorem theorem_R {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω) {k : ℕ}
    (hk : 1 ≤ k) {θ δ A Eu : ℝ} (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hA : 0 < A) (hEu : 0 < Eu)
    (hEuA : Eu ≤ A) (τ : Fin k → ℝ) (hτ : ∀ j, 1 < τ j) (N : Ω → ℝ≥0∞)
    (X : Matrix (Fin k) (Fin k) ℕ → List ℕ → Ω → ℝ≥0∞) (hXm : ∀ E l, Measurable (X E l))
    (hred : SkeletonReduction k N X) (hbound : SkeletonBound P Good k θ δ A Eu τ X) :
    ∫⁻ ω in Good, N ω ∂P ≤ ENNReal.ofReal ((k : ℝ) ^ k / k.factorial * (θ * A * δ) ^ k *
      ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k) := by
  classical
  have hτ0 : ∀ j, 0 < (τ j)⁻¹ := fun j => inv_pos.mpr (by linarith [hτ j])
  have hτ1 : ∀ j, 0 ≤ (1 - (τ j)⁻¹)⁻¹ := fun j =>
    inv_nonneg.mpr (by linarith [inv_lt_one_of_one_lt₀ (hτ j)])
  set Y : Matrix (Fin k) (Fin k) ℕ → Ω → ℝ≥0∞ :=
    fun E ω => (InvPattern k).indicator (fun E => ∑ l ∈ comps k, X E l ω) E with hY
  have hYm : ∀ E, Measurable (Y E) := by
    intro E
    by_cases hE : E ∈ InvPattern k
    · simp only [hY, Set.indicator_of_mem hE]
      exact Finset.measurable_sum _ fun l _ => hXm E l
    · simp only [hY, Set.indicator_of_notMem hE]; exact measurable_const
  -- the sum of the skeleton bounds
  have hsum : ∑' E, ∫⁻ ω in Good, Y E ω ∂P ≤
      ∑' E, (InvPattern k).indicator
        (fun E => ENNReal.ofReal (θ ^ k * δ ^ k) *
          (∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E i j) - 1))) *
          ∑ l ∈ comps k, ENNReal.ofReal (finG A l Eu)) E := by
    refine ENNReal.tsum_le_tsum fun E => ?_
    by_cases hE : E ∈ InvPattern k
    · simp only [hY, Set.indicator_of_mem hE]
      rw [lintegral_finset_sum _ fun l _ => hXm E l, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => (hbound E hE l hl).trans_eq ?_
      have hfin := finG_nonneg (A := A) l hEu
      have hpw : 0 ≤ patternWeight τ E := Finset.prod_nonneg fun j _ => by
        have := hτ0 j; positivity
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        patternWeight, ENNReal.ofReal_prod_of_nonneg (fun j _ => by have := hτ0 j; positivity)]
    · simp [hY, Set.indicator_of_notMem hE]
  have hpat := pattern_sum τ hτ
  have hruns := sum_comps_finG_le k hk hA hEu.le hEuA
  have hfin0 : ∀ l, 0 ≤ finG A l Eu := fun l => finG_nonneg l hEu
  have hruns' : ∑ l ∈ comps k, ENNReal.ofReal (finG A l Eu) ≤
      ENNReal.ofReal (A ^ k * ((k : ℝ) ^ k / k.factorial)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hfin0 l]
    exact ENNReal.ofReal_le_ofReal hruns
  -- assemble
  have hfact : (0 : ℝ≥0∞) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hfact' : (k.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmain : (k.factorial : ℝ≥0∞) * ∫⁻ ω in Good, N ω ∂P ≤
      (k.factorial : ℝ≥0∞) * ENNReal.ofReal ((k : ℝ) ^ k / k.factorial * (θ * A * δ) ^ k *
        ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k) := by
    calc (k.factorial : ℝ≥0∞) * ∫⁻ ω in Good, N ω ∂P
        = ∫⁻ ω in Good, (k.factorial : ℝ≥0∞) * N ω ∂P := (lintegral_const_mul' _ _ hfact').symm
      _ ≤ ∫⁻ ω in Good, ∑' E, Y E ω ∂P := lintegral_mono fun ω => hred ω
      _ = ∑' E, ∫⁻ ω in Good, Y E ω ∂P := lintegral_tsum fun E => (hYm E).aemeasurable
      _ ≤ _ := hsum
      _ = ENNReal.ofReal (θ ^ k * δ ^ k) * (∑' E, (InvPattern k).indicator
            (fun E => ∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E i j) - 1))) E) *
            ∑ l ∈ comps k, ENNReal.ofReal (finG A l Eu) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun E => ?_
          by_cases hE : E ∈ InvPattern k
          · simp only [Set.indicator_of_mem hE]
          · simp [Set.indicator_of_notMem hE]
      _ ≤ ENNReal.ofReal (θ ^ k * δ ^ k) *
            (k.factorial * ∏ j, ENNReal.ofReal ((1 - (τ j)⁻¹)⁻¹ ^ k)) *
            ENNReal.ofReal (A ^ k * ((k : ℝ) ^ k / k.factorial)) := by
          gcongr
          exact hpat
      _ = (k.factorial : ℝ≥0∞) * ENNReal.ofReal ((k : ℝ) ^ k / k.factorial * (θ * A * δ) ^ k *
            ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k) := by
          have hp : 0 ≤ ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k := Finset.prod_nonneg fun j _ =>
            pow_nonneg (hτ1 j) k
          have hθδ : 0 ≤ θ ^ k * δ ^ k := by positivity
          have hfr : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
          rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => pow_nonneg (hτ1 j) k,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hfr, ← ENNReal.ofReal_mul hθδ,
            ← ENNReal.ofReal_mul (mul_nonneg hθδ (mul_nonneg hfr hp)),
            ← ENNReal.ofReal_mul hfr]
          congr 1
          have : (k.factorial : ℝ) ≠ 0 := by positivity
          rw [mul_pow, mul_pow]
          field_simp
  exact (ENNReal.mul_le_mul_iff_right hfact.ne' hfact').mp hmain

/-- **Theorem A.12, second line.** From the first line, with Lemma A.3's second inequality
`∏_j (1 - 1/τ_j)^{-k} ≤ a^k u^{1.02k}` (`a = e^{(3H(X₀)+2)/X₀}`, `u = 1 + k/X₀`), the sure top
bound `A_top ≤ A_R b` (`b = e^{2.2/Λ}`, Lemma A.6 (S3)(d)) and `k^k/k! ≤ e^k`:
`(k^k/k!) (θ A_top δ)^k ∏_j (1 - 1/τ_j)^{-k} ≤ (e θ A_R δ)^k a^k u^{1.02k} b^k`. -/
theorem theorem_R_second_line {k : ℕ} {θ δ A A_R a b u : ℝ} (hθ : 0 ≤ θ) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (hAR : A ≤ A_R * b) (τ : Fin k → ℝ) (hτ : ∀ j, 1 < τ j)
    (hpat : ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k ≤ a ^ k * u ^ (1.02 * (k : ℝ))) :
    (k : ℝ) ^ k / k.factorial * (θ * A * δ) ^ k * ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k ≤
      (Real.exp 1 * θ * A_R * δ) ^ k * a ^ k * u ^ (1.02 * (k : ℝ)) * b ^ k := by
  have hτ1 : ∀ j, 0 ≤ (1 - (τ j)⁻¹)⁻¹ := fun j =>
    inv_nonneg.mpr (by linarith [inv_lt_one_of_one_lt₀ (hτ j)])
  have hp : 0 ≤ ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k := Finset.prod_nonneg fun j _ => pow_nonneg (hτ1 j) k
  have hkk : (k : ℝ) ^ k / k.factorial ≤ Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hAb : 0 ≤ A_R * b := hA.trans hAR
  have h1 : (θ * A * δ) ^ k ≤ (θ * (A_R * b) * δ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by gcongr) k
  have h2 : 0 ≤ (k : ℝ) ^ k / k.factorial := by positivity
  calc (k : ℝ) ^ k / k.factorial * (θ * A * δ) ^ k * ∏ j, (1 - (τ j)⁻¹)⁻¹ ^ k
      ≤ Real.exp 1 ^ k * (θ * (A_R * b) * δ) ^ k * (a ^ k * u ^ (1.02 * (k : ℝ))) := by
        gcongr
    _ = (Real.exp 1 * θ * A_R * δ) ^ k * a ^ k * u ^ (1.02 * (k : ℝ)) * b ^ k := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]; ring

/-! ## Proposition 6.11 -/

/-- The number of rank-`k` `k`-subsets of `S` (`k`-subsets whose vectors are linearly
independent over `ℚ`). -/
noncomputable def rankFullCount {m : ℕ} (k : ℕ) (S : Finset (Fin m → ℕ)) : ℕ := by
  classical exact ((S.powersetCard k).filter fun T : Finset (Fin m → ℕ) =>
    LinearIndepOn ℚ Covers.vq (↑T : Set (Fin m → ℕ))).card

/-- A set of rank `≥ k` has a linearly independent `k`-subset. -/
lemma one_le_rankFullCount {m : ℕ} {k : ℕ} {S : Finset (Fin m → ℕ)} (h : k ≤ Covers.rank S) :
    1 ≤ rankFullCount k S := by
  classical
  obtain ⟨B, hB⟩ := Covers.exists_basisOf S
  rw [Covers.rank_eq_card hB] at h
  obtain ⟨T, hTB, hT⟩ := Finset.exists_subset_card_eq h
  unfold rankFullCount
  apply Finset.one_le_card.mpr
  refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hTB.trans hB.1, hT⟩, ?_⟩⟩
  exact hB.2.1.mono (by exact_mod_cast hTB)

/-- **Proposition 6.11 (the cluster event)**, abstractly: on a measure space with a measurable
good event, for a finite family `W` of windows with exponent-vector sets `S J ω` and counts
`cnt J ω ≤ |S J ω| + 1`, if (Theorem A.12 + Corollary A.13)
`∑_J E[#{rank-r₀ r₀-subsets of S(J)}; Good] ≤ L^{-4}` and (Theorem 6.23(a))
`P(∃ J, rank S(J) < r₀ ∧ |S(J)| ≥ r₀ + φ(r₀); Good) ≤ L^{-3}`, then, with `M₁ = r₀ + φ(r₀) + 1`
and `L ≥ 465`, `P(∃ J, #(N ∩ J) > M₁; Good) ≤ L^{-2}`. -/
theorem prop_6_11 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ))
    (cnt : ι → Ω → ℕ) (hcnt : ∀ J ω, cnt J ω ≤ (S J ω).card + 1) (r₀ : ℕ) {c Q M₁ L : ℝ}
    (hM₁ : M₁ = r₀ + Covers.phi c Q r₀ + 1) (hL : 465 ≤ L)
    (hmeas : ∀ J ∈ W, Measurable fun ω => (rankFullCount r₀ (S J ω) : ℝ≥0∞))
    (hR : ∑ J ∈ W, ∫⁻ ω in Good, (rankFullCount r₀ (S J ω) : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (L ^ (-4 : ℝ)))
    (hcap : P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi c Q r₀ ≤ (S J ω).card} ∩ Good) ≤ ENNReal.ofReal (L ^ (-3 : ℝ))) :
    P ({ω | ∃ J ∈ W, M₁ < cnt J ω} ∩ Good) ≤ ENNReal.ofReal (L ^ (-2 : ℝ)) := by
  classical
  set A₁ := ⋃ J ∈ W, {ω | 1 ≤ (rankFullCount r₀ (S J ω) : ℝ≥0∞)} ∩ Good
  set A₂ := {ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi c Q r₀ ≤ (S J ω).card} ∩ Good
  have hsub : {ω | ∃ J ∈ W, M₁ < cnt J ω} ∩ Good ⊆ A₁ ∪ A₂ := by
    rintro ω ⟨⟨J, hJ, hcntJ⟩, hG⟩
    by_cases hr : r₀ ≤ Covers.rank (S J ω)
    · left
      refine Set.mem_biUnion hJ ⟨?_, hG⟩
      show (1 : ℝ≥0∞) ≤ (rankFullCount r₀ (S J ω) : ℝ≥0∞)
      exact_mod_cast one_le_rankFullCount hr
    · right
      refine ⟨⟨J, hJ, not_le.mp hr, ?_⟩, hG⟩
      have := hcnt J ω
      have h2 : (cnt J ω : ℝ) ≤ (S J ω).card + 1 := by exact_mod_cast this
      rw [hM₁] at hcntJ
      linarith
  have hA₁ : P A₁ ≤ ENNReal.ofReal (L ^ (-4 : ℝ)) := by
    refine (measure_biUnion_finset_le W _).trans ?_
    refine le_trans (Finset.sum_le_sum fun J hJ => ?_) hR
    rw [← Measure.restrict_apply' hGood]
    have := mul_meas_ge_le_lintegral₀ (μ := P.restrict Good) (hmeas J hJ).aemeasurable 1
    simpa using this
  have hL0 : 0 < L := by linarith
  have hfin : L ^ (-4 : ℝ) + L ^ (-3 : ℝ) ≤ L ^ (-2 : ℝ) := by
    have e4 : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) * L⁻¹ := by
      rw [show (-4 : ℝ) = -3 + -1 by norm_num, Real.rpow_add hL0, Real.rpow_neg_one]
    have e2 : L ^ (-2 : ℝ) = L ^ (-3 : ℝ) * L := by
      rw [show (-2 : ℝ) = -3 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    rw [e4, e2]
    have h3 : 0 < L ^ (-3 : ℝ) := by positivity
    have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    nlinarith
  calc P ({ω | ∃ J ∈ W, M₁ < cnt J ω} ∩ Good) ≤ P (A₁ ∪ A₂) := measure_mono hsub
    _ ≤ P A₁ + P A₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (L ^ (-4 : ℝ)) + ENNReal.ofReal (L ^ (-3 : ℝ)) := add_le_add hA₁ hcap
    _ = ENNReal.ofReal (L ^ (-4 : ℝ) + L ^ (-3 : ℝ)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (L ^ (-2 : ℝ)) := ENNReal.ofReal_le_ofReal hfin

/-- **Proposition 6.11 from Theorem A.12**: the rank-`≥ r₀` hypothesis of `prop_6_11` follows
from the per-window bound of Theorem A.12 (second line) with `k = r₀`, `δ = 4L^{-6}`, at most
`2z/δ + 1` windows, and Corollary A.13 (`cor_R_numeric`). -/
theorem prop_6_11_of_theorem_R {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ))
    (cnt : ι → Ω → ℕ) (hcnt : ∀ J ω, cnt J ω ≤ (S J ω).card + 1) (r₀ : ℕ)
    {c Q M₁ L z θ a b A_R u : ℝ}
    (hM₁ : M₁ = r₀ + Covers.phi c Q r₀ + 1) (hL : 465 ≤ L) (hz0 : 0 < z) (hz : z ≤ Real.exp L)
    (hθ : 0 < θ) (ha : 0 < a) (hb : 0 < b) (hθab : θ * a * b ≤ 1.01) (hAR0 : 0 ≤ A_R)
    (hAR : A_R ≤ 1.8 * (L + 4)) (hu1 : 1 ≤ u) (hu : u ≤ 2 * L)
    (hr₀ : L / (3 * Real.log L) + 3 ≤ r₀)
    (hW : (W.card : ℝ) ≤ 2 * z / (4 * L ^ (-6 : ℝ)) + 1)
    (hmeas : ∀ J ∈ W, Measurable fun ω => (rankFullCount r₀ (S J ω) : ℝ≥0∞))
    (hthmR : ∀ J ∈ W, ∫⁻ ω in Good, (rankFullCount r₀ (S J ω) : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ))) ^ r₀ * a ^ r₀ *
        u ^ (1.02 * (r₀ : ℝ)) * b ^ r₀))
    (hcap : P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi c Q r₀ ≤ (S J ω).card} ∩ Good) ≤ ENNReal.ofReal (L ^ (-3 : ℝ))) :
    P ({ω | ∃ J ∈ W, M₁ < cnt J ω} ∩ Good) ≤ ENNReal.ofReal (L ^ (-2 : ℝ)) := by
  refine prop_6_11 P hGood W S cnt hcnt r₀ hM₁ hL hmeas ?_ hcap
  set R := (Real.exp 1 * θ * A_R * (4 * L ^ (-6 : ℝ))) ^ r₀ * a ^ r₀ *
        u ^ (1.02 * (r₀ : ℝ)) * b ^ r₀ with hRdef
  have hL0 : 0 < L := by linarith
  have hR0 : 0 ≤ R := by positivity
  calc ∑ J ∈ W, ∫⁻ ω in Good, (rankFullCount r₀ (S J ω) : ℝ≥0∞) ∂P
      ≤ ∑ _J ∈ W, ENNReal.ofReal R := Finset.sum_le_sum hthmR
    _ = ENNReal.ofReal (W.card * R) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (L ^ (-4 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have := cor_R_numeric hL hz0 hz hθ ha hb hθab hAR0 hAR hu1 hu hr₀
        calc (W.card : ℝ) * R ≤ (2 * z / (4 * L ^ (-6 : ℝ)) + 1) * R :=
              mul_le_mul_of_nonneg_right hW hR0
          _ ≤ L ^ (-4 : ℝ) := by rw [hRdef]; linarith [this]

/-! ## Theorem A.12 and Proposition 6.11 with the slot bounds `τ_j` of (A.tau) -/

/-- **Theorem A.12 (Theorem R)**, both lines, with `τ_j` the slot bounds (A.tau) and Lemma A.3
proved in full: from `SkeletonReduction`, `SkeletonBound` (Lemma A.5 + Theorem A.10 with `C = B'`)
and the sure top bound `Eu_rat ≤ A_top ≤ A_R b` (Lemma A.6 (S3)(d)),
`E[#{rank-k k-subsets}; Good] ≤ (e θ A_R δ)^k e^{(3H(X₀)+2)k/X₀} (1 + k/X₀)^{1.02k} b^k`. -/
theorem theorem_R_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω) {k : ℕ}
    (hk : 1 ≤ k) {θ δ A Eu A_R b X₀ : ℝ} {H : ℝ → ℝ} (hH : SlotHyp H X₀) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hEu : 0 < Eu) (hEuA : Eu ≤ A) (hAR : A ≤ A_R * b) (N : Ω → ℝ≥0∞)
    (X : Matrix (Fin k) (Fin k) ℕ → List ℕ → Ω → ℝ≥0∞) (hXm : ∀ E l, Measurable (X E l))
    (hred : SkeletonReduction k N X)
    (hbound : SkeletonBound P Good k θ δ A Eu (fun j => tauSlot H X₀ j) X) :
    ∫⁻ ω in Good, N ω ∂P ≤ ENNReal.ofReal ((Real.exp 1 * θ * A_R * δ) ^ k *
      Real.exp ((3 * H X₀ + 2) / X₀) ^ k * (1 + k / X₀) ^ (1.02 * (k : ℝ)) * b ^ k) := by
  have hA : 0 < A := hEu.trans_le hEuA
  refine (theorem_R P Good hk hθ hδ hA hEu hEuA _ (fun j => hH.one_lt_tauSlot j) N X hXm hred
    hbound).trans (ENNReal.ofReal_le_ofReal ?_)
  apply theorem_R_second_line hθ hδ hA.le hAR _ (fun j => hH.one_lt_tauSlot j)
  have := hH.pattern_sum_tail k
  rw [← Fin.prod_univ_eq_prod_range (fun j => (1 - (tauSlot H X₀ j)⁻¹)⁻¹ ^ k)] at this
  refine this.trans_eq ?_
  rw [← Real.exp_nat_mul]; congr 2; ring

/-- **Proposition 6.11 (the cluster event)** from Theorem A.12's named inputs and
Theorem 6.23(a): with `k = r₀ ≥ L/(3ℓ) + 3`, `δ = 4L^{-6}`, `L ≥ 465`, at most `2z/δ + 1` windows,
`θ e^{(3H(X₀)+2)/X₀} b ≤ 1.01`, `A_R ≤ 1.8(L+4)`, `1 + r₀/X₀ ≤ 2L`, and, for each window `J`,
the reduction to skeletons and the skeleton bound for the rank-full `r₀`-subsets of `S(J)`,
`P(∃ J, #(N ∩ J) > M₁; Good) ≤ L^{-2}`. -/
theorem prop_6_11_full {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ))
    (cnt : ι → Ω → ℕ) (hcnt : ∀ J ω, cnt J ω ≤ (S J ω).card + 1) (r₀ : ℕ)
    {c Q M₁ L z θ A Eu A_R b X₀ : ℝ} {H : ℝ → ℝ} (hH : SlotHyp H X₀)
    (hM₁ : M₁ = r₀ + Covers.phi c Q r₀ + 1) (hL : 465 ≤ L) (hz0 : 0 < z) (hz : z ≤ Real.exp L)
    (hθ : 0 < θ) (hb : 0 < b) (hθab : θ * Real.exp ((3 * H X₀ + 2) / X₀) * b ≤ 1.01)
    (hAR0 : 0 ≤ A_R) (hAR : A_R ≤ 1.8 * (L + 4)) (hu : 1 + r₀ / X₀ ≤ 2 * L)
    (hr₀ : L / (3 * Real.log L) + 3 ≤ r₀)
    (hW : (W.card : ℝ) ≤ 2 * z / (4 * L ^ (-6 : ℝ)) + 1)
    (hEu : 0 < Eu) (hEuA : Eu ≤ A) (hAtop : A ≤ A_R * b)
    (X : ι → Matrix (Fin r₀) (Fin r₀) ℕ → List ℕ → Ω → ℝ≥0∞)
    (hXm : ∀ J E l, Measurable (X J E l))
    (hmeas : ∀ J ∈ W, Measurable fun ω => (rankFullCount r₀ (S J ω) : ℝ≥0∞))
    (hred : ∀ J ∈ W, SkeletonReduction r₀ (fun ω => (rankFullCount r₀ (S J ω) : ℝ≥0∞)) (X J))
    (hbound : ∀ J ∈ W, SkeletonBound P Good r₀ θ (4 * L ^ (-6 : ℝ)) A Eu
      (fun j => tauSlot H X₀ j) (X J))
    (hcap : P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi c Q r₀ ≤ (S J ω).card} ∩ Good) ≤ ENNReal.ofReal (L ^ (-3 : ℝ))) :
    P ({ω | ∃ J ∈ W, M₁ < cnt J ω} ∩ Good) ≤ ENNReal.ofReal (L ^ (-2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hk : 1 ≤ r₀ := by
    have : (1 : ℝ) ≤ r₀ := by
      have : 0 ≤ L / (3 * Real.log L) := by
        have : 0 < Real.log L := Real.log_pos (by linarith)
        positivity
      linarith
    exact_mod_cast this
  have hX0 : 0 < X₀ := hH.X₀_pos
  have hu1 : (1 : ℝ) ≤ 1 + r₀ / X₀ := by
    have : (0 : ℝ) ≤ r₀ / X₀ := by positivity
    linarith
  refine prop_6_11_of_theorem_R P hGood W S cnt hcnt r₀ hM₁ hL hz0 hz hθ (Real.exp_pos _) hb
    hθab hAR0 hAR hu1 hu hr₀ hW hmeas ?_ hcap
  intro J hJ
  exact theorem_R_full P Good hk hH hθ.le (by positivity) hEu hEuA hAtop _ (X J) (hXm J)
    (hred J hJ) (hbound J hJ)

end RankFull
