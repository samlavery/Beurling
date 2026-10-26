module

public import RequestProject.Beurling.RankFull.TheoremR
public import RequestProject.Beurling.CoversHighDegree
public import RequestProject.Beurling.TypeUnion

/-!
# Proposition 6.19 (Cover Bound) and Theorem 6.23(a) (CapL-w), abstractly

## Proposition 6.19

For a skeleton `𝔰` of a configuration `(B', C)` of rank `r` with `κ = |C|` cover rows and `|R|`
rows outside the cover, let `l` be the list of the numbers `j_t` of rows of `C` joining at the
stages `t` (earliest stage first; `j_t = 0` allowed, `∑ j_t = κ`). The named hypothesis
`CoverSkeletonBound` is the output of Lemma A.5 + Theorem A.10 with the cover `C`, as collected in
the proof of Proposition 6.19 ("From Lemma A.5", "Exact identity", "Allocation", "Bookkeeping"):
`E[X_𝔰; Good(<t_z)] ≤ θ^r δ^r ∏_i τ_i^{-e_i} z^{-|R|} Fin(l)`.
`RankFull.cover_bound` then proves (6.19) `E[X_𝔰; Good] ≤ (θδ)^r Σ̄_𝔰`,
`Σ̄_𝔰 = (1 + κλ)^{s_R} (κ^κ/κ!) Ch^κ ∏_i τ_i^{-e_i} z^{-|R|}`, with `s_R` the number of stages at
which no row of `C` joins, from the chain bound `finG_le_cover` ("The chain recursion").

## Theorem 6.23(a)

`RankFull.IsConfig` is the notion of configuration of Section 6.7 (a rank-full `B' ⊆ S(J)` of rank
`< r₀` with a minimum cover `C ⊆ B'`), restricted to `|R| ≥ 1 + j` and all rows of `R` of degree
`≥ k + 1`; `configCount` counts them.

* `RankFull.exists_config` (Step 0 / Lemma 6.21(i), deterministic): if `rank S < r₀`,
  `|S| ≥ r₀ + φ(r₀)`, `0 ∉ S`, all degrees `≤ D`, `e (r₀(D+1))^{2j+1} < c`, and every heavy
  subspace `V` of dimension `< r₀` has at most `Q` elements of degree `≤ k` in `S ∩ V`, then
  `configCount ≥ 1`.
* `RankFull.theorem_6_23a` : from `TypeUnionBound` (Lemma 6.21(ii) summed over the ranks
  `r < r₀`, with Lemma 6.22 bounding the weight of every row of degree `≥ k + 1` by `w`) and the
  criterion (80) `(1 + j) log(1/w) ≥ L + 10ℓ + 10` (Steps 2–4 of the proof), the probability on
  `Good` that some window has `rank S(J) < r₀` and `|S(J)| ≥ r₀ + φ(r₀)` is at most `L^{-3}`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal

namespace RankFull

/-! ## Proposition 6.19 -/

/-- **Lemma A.5 + Theorem A.10 with the cover `C`** (proof of Proposition 6.19). -/
def CoverSkeletonBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω) (r : ℕ)
    (θ δ A Eu z : ℝ) (τ : Fin r → ℝ) (e : Fin r → ℕ) (nR : ℕ) (l : List ℕ) (X : Ω → ℝ≥0∞) :
    Prop :=
  ∫⁻ ω in Good, X ω ∂P ≤
    ENNReal.ofReal (θ ^ r * δ ^ r * (∏ i, (τ i)⁻¹ ^ e i) * z⁻¹ ^ nR * finG A l Eu)

/-- `Σ̄_𝔰 = (1 + κλ)^{s_R} (κ^κ/κ!) Ch^κ ∏_i τ_i^{-e_i} z^{-|R|}` of (6.19). -/
noncomputable def sigmaBar {r : ℕ} (κ sR nR : ℕ) (lam Ch z : ℝ) (τ : Fin r → ℝ) (e : Fin r → ℕ) :
    ℝ :=
  (1 + κ * lam) ^ sR * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * (∏ i, (τ i)⁻¹ ^ e i) * z⁻¹ ^ nR

/-- **Proposition 6.19 (Cover Bound)**: `E[X_𝔰; Good(<t_z)] ≤ (θδ)^r Σ̄_𝔰`, with
`κ = l.sum ≥ 1`, `s_R = #{t : j_t = 0}`, `0 < Eu_rat ≤ A_top ≤ Ch` and `λ ≥ log(A_top/Eu_rat)`. -/
theorem cover_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω) {r : ℕ}
    {θ δ A Eu z Ch lam : ℝ} (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hz : 0 < z) (hEu : 0 < Eu) (hEuA : Eu ≤ A)
    (hACh : A ≤ Ch) (hlam : Real.log (A / Eu) ≤ lam) (τ : Fin r → ℝ) (hτ : ∀ i, 0 < τ i)
    (e : Fin r → ℕ) (nR : ℕ) (l : List ℕ) (hκ : 1 ≤ l.sum) (X : Ω → ℝ≥0∞)
    (h : CoverSkeletonBound P Good r θ δ A Eu z τ e nR l X) :
    ∫⁻ ω in Good, X ω ∂P ≤
      ENNReal.ofReal ((θ * δ) ^ r * sigmaBar l.sum (l.count 0) nR lam Ch z τ e) := by
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA : 0 < A := hEu.trans_le hEuA
  have hfin := finG_le_cover hA hEu hEuA hlam l hκ
  have hAk : A ^ l.sum ≤ Ch ^ l.sum := pow_le_pow_left₀ hA.le hACh _
  have hτp : 0 ≤ ∏ i, (τ i)⁻¹ ^ e i := Finset.prod_nonneg fun i _ => by
    have := hτ i; positivity
  have hlam0 : 0 ≤ lam := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hEu]; linarith)) hlam
  have hfin' : finG A l Eu ≤ (1 + l.sum * lam) ^ l.count 0 *
      (Ch ^ l.sum * ((l.sum : ℝ) ^ l.sum / (l.sum).factorial)) := by
    refine hfin.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul_of_nonneg_right hAk (by positivity)
  have hpre : 0 ≤ θ ^ r * δ ^ r * (∏ i, (τ i)⁻¹ ^ e i) * z⁻¹ ^ nR := by positivity
  calc θ ^ r * δ ^ r * (∏ i, (τ i)⁻¹ ^ e i) * z⁻¹ ^ nR * finG A l Eu
      ≤ θ ^ r * δ ^ r * (∏ i, (τ i)⁻¹ ^ e i) * z⁻¹ ^ nR * ((1 + l.sum * lam) ^ l.count 0 *
          (Ch ^ l.sum * ((l.sum : ℝ) ^ l.sum / (l.sum).factorial))) :=
        mul_le_mul_of_nonneg_left hfin' hpre
    _ = (θ * δ) ^ r * sigmaBar l.sum (l.count 0) nR lam Ch z τ e := by
        unfold sigmaBar; rw [mul_pow]; ring

/-! ## Theorem 6.23(a) -/

open Covers

variable {m : ℕ}

/-- A configuration of Section 6.7 with `|R| ≥ 1 + j` rows outside the cover, all of degree
`≥ k + 1`: `B ⊆ S` linearly independent of rank `< r₀`, `C ⊆ B` a minimum cover of `B`. -/
def IsConfig (r₀ j k : ℕ) (S : Finset (Fin m → ℕ)) (CB : Finset (Fin m → ℕ) × Finset (Fin m → ℕ)) :
    Prop :=
  CB.2 ⊆ S ∧ LinearIndepOn ℚ vq (CB.2 : Set (Fin m → ℕ)) ∧ rank CB.2 < r₀ ∧
    IsCover CB.2 CB.1 ∧ CB.1.card = kappa CB.2 ∧ j + 1 ≤ (CB.2 \ CB.1).card ∧
    ∀ y ∈ CB.2 \ CB.1, k + 1 ≤ deg y

/-- The number of configurations (`IsConfig`) in `S`. -/
noncomputable def configCount (r₀ j k : ℕ) (S : Finset (Fin m → ℕ)) : ℕ := by
  classical exact ((S.powerset ×ˢ S.powerset).filter (IsConfig r₀ j k S)).card

lemma P_mono {S T : Finset (Fin m → ℕ)} (h : S ⊆ T) : Covers.P S ⊆ Covers.P T :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- **Step 0 of the proof of Theorem 6.23(a)** (Lemma 6.14 + Lemma 6.21(i)): a window with
`rank S < r₀` and `|S| ≥ r₀ + φ(r₀)` contains a configuration with `|R| ≥ 1 + j` rows outside a
minimum cover, all of degree `≥ k + 1`, provided `e (r₀(D+1))^{2j+1} < c` and every
element-spanned `V` of dimension `< r₀` has at most `Q` elements of `S ∩ V` of degree `≤ k`. -/
theorem exists_config {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j k : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) {c Q : ℝ} (hQ : 0 ≤ Q) {r₀ : ℕ}
    (hrank : rank S < r₀) (hcard : (r₀ : ℝ) + phi c Q r₀ ≤ S.card)
    (hc : Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) < c)
    (hlow : ∀ V : Submodule ℚ (Fin m → ℚ), ElemSpanned S V → Module.finrank ℚ V < r₀ →
      (((inter S V).filter (fun y => deg y ≤ k)).card : ℝ) ≤ Q) :
    1 ≤ configCount r₀ j k S := by
  classical
  obtain ⟨V, hVes, -, -, hrk, hmain⟩ := extras_drop_out_heavy h0 hD hQ hrank hcard (j := j) (k := k)
  -- `dim V ≤ rank S < r₀`
  have hdim : Module.finrank ℚ V < r₀ := by
    obtain ⟨T, hTS, rfl⟩ := hVes
    refine lt_of_le_of_lt ?_ hrank
    exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by exact_mod_cast hTS)))
  have hc' : Real.exp 1 * ((Module.finrank ℚ V : ℝ) * (D + 1)) ^ (2 * j + 1) < c := by
    refine lt_of_le_of_lt ?_ hc
    gcongr
  obtain ⟨-, C, B, hC, hCcard, hB, hCB, hj, hk⟩ := hmain hc' (hlow V hVes hdim)
  have hSV : inter S V ⊆ S := Finset.filter_subset _ _
  -- `C` is a minimum cover of `B`
  have hPB : Covers.P B = Covers.P (inter S V) :=
    le_antisymm (P_mono hB.1) ((basis_isCover hB).2 ▸ le_rfl)
  have hCcov : IsCover B C := ⟨hCB, by rw [hC.2, hPB]⟩
  have hκB : C.card = kappa B := by
    apply le_antisymm
    · -- every cover of `B` covers `S ∩ V`
      obtain ⟨C', hC', hC'card⟩ := exists_min_cover B
      rw [← hC'card, hCcard]
      exact kappa_le_card ⟨hC'.1.trans hB.1, by rw [hC'.2, hPB]⟩
    · exact kappa_le_card hCcov
  have hrB : rank B < r₀ := by
    have : rank B ≤ rank S := by
      unfold rank
      exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by
        exact_mod_cast hB.1.trans hSV)))
    omega
  unfold configCount
  apply Finset.one_le_card.mpr
  refine ⟨(C, B), Finset.mem_filter.mpr ⟨?_, hB.1.trans hSV, hB.2.1, hrB, hCcov, hκB, hj, hk⟩⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (hCB.trans (hB.1.trans hSV)),
    Finset.mem_powerset.mpr (hB.1.trans hSV)⟩

/-- **Lemma 6.21(ii), summed over the ranks `r < r₀`** (with Lemma 6.22 bounding the weight `w_y`
of every row of degree `≥ k + 1` by `w`, and Proposition 6.19 for each skeleton):
`∑_J E[#configurations in S(J); Good(<t_z)] ≤ r₀ · 13 L^{5.1} z w^{1+j}`. -/
def TypeUnionBound {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Good : Set Ω)
    (W : Finset ι) (S : ι → Ω → Finset (Fin m → ℕ)) (r₀ j k : ℕ) (L z w : ℝ) : Prop :=
  ∑ J ∈ W, ∫⁻ ω in Good, (configCount r₀ j k (S J ω) : ℝ≥0∞) ∂P ≤
    ENNReal.ofReal (r₀ * (13 * L ^ (5.1 : ℝ) * z) * w ^ (1 + j))

/-- **Theorem 6.23(a) (counting)**, abstractly: on `Good(<t_z)`, the probability that some grid
window `J` has `rank S(J) < r₀` and `|S(J)| ≥ r₀ + φ(r₀)` is at most `L^{-3}`. Inputs: the
deterministic Step 0 (`exists_config`, proved), `TypeUnionBound` (Lemma 6.21(ii)), and the
criterion (80) for the chosen `j, k, w` (Steps 2–4). Here `z = e^L`, `L ≥ 60`, `r₀ ≤ L`. -/
theorem theorem_6_23a {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) (S : ι → Ω → Finset (Fin m → ℕ))
    (h0 : ∀ J ω, 0 ∉ S J ω) {D j k r₀ : ℕ} (hD : ∀ J ω, ∀ v ∈ S J ω, deg v ≤ D)
    {c Q L w : ℝ} (hQ : 0 ≤ Q) (hL : 60 ≤ L) (hr₀L : (r₀ : ℝ) ≤ L) (hw0 : 0 < w)
    (hc : Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) < c)
    (hlow : ∀ J ω, ∀ V : Submodule ℚ (Fin m → ℚ), ElemSpanned (S J ω) V →
      Module.finrank ℚ V < r₀ → (((inter (S J ω) V).filter (fun y => deg y ≤ k)).card : ℝ) ≤ Q)
    (hmeas : ∀ J ∈ W, Measurable fun ω => (configCount r₀ j k (S J ω) : ℝ≥0∞))
    (htu : TypeUnionBound P Good W S r₀ j k L (Real.exp L) w)
    (h80 : L + 10 * Real.log L + 10 ≤ (1 + j) * Real.log (1 / w)) :
    P ({ω | ∃ J ∈ W, rank (S J ω) < r₀ ∧ (r₀ : ℝ) + phi c Q r₀ ≤ (S J ω).card} ∩ Good) ≤
      ENNReal.ofReal (L ^ (-3 : ℝ)) := by
  classical
  have hsub : {ω | ∃ J ∈ W, rank (S J ω) < r₀ ∧ (r₀ : ℝ) + phi c Q r₀ ≤ (S J ω).card} ∩ Good ⊆
      ⋃ J ∈ W, {ω | 1 ≤ (configCount r₀ j k (S J ω) : ℝ≥0∞)} ∩ Good := by
    rintro ω ⟨⟨J, hJ, hr, hcard⟩, hG⟩
    refine Set.mem_biUnion hJ ⟨?_, hG⟩
    show (1 : ℝ≥0∞) ≤ (configCount r₀ j k (S J ω) : ℝ≥0∞)
    exact_mod_cast exists_config (h0 J ω) (hD J ω) hQ hr hcard hc (hlow J ω)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le W _).trans ?_)
  refine le_trans (Finset.sum_le_sum fun J hJ => ?_) (htu.trans ?_)
  · rw [← Measure.restrict_apply' hGood]
    have := mul_meas_ge_le_lintegral₀ (μ := P.restrict Good) (hmeas J hJ).aemeasurable 1
    simpa using this
  · apply ENNReal.ofReal_le_ofReal
    have := Covers.union_bound_le hL hw0 hr₀L j h80
    exact this

/-- The second sentence of Theorem 6.23(a): for such a window, with `V` a heavy subspace of
least dimension, `Cap(S(J) ∩ V) ≥ c` (Lemma 6.14(i)). -/
theorem theorem_6_23a_cap {S : Finset (Fin m → ℕ)} {c Q : ℝ} (hQ : 0 ≤ Q) {r₀ : ℕ}
    (hrank : rank S < r₀) (hcard : (r₀ : ℝ) + phi c Q r₀ ≤ S.card) :
    ∃ V : Submodule ℚ (Fin m → ℚ), ElemSpanned S V ∧ Heavy c Q S V ∧
      (∀ W, ElemSpanned S W → Heavy c Q S W → Module.finrank ℚ V ≤ Module.finrank ℚ W) ∧
      c ≤ (cap (inter S V) : ℝ) := by
  obtain ⟨V, h1, h2, h3, ⟨h4, h5⟩, -, -⟩ := heavy_subspace hQ hrank hcard
  exact ⟨V, h1, h2, h3, h5.trans h4⟩

end RankFull
