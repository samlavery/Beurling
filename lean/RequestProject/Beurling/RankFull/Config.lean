module

public import RequestProject.Beurling.RankFull.TheoremR
public import RequestProject.Beurling.RankFull.StageJoin

/-!
# The realised-configuration model: skeletons and the reduction to skeletons (Theorem A.12)

Jittered primes are indexed by their decision slots `n : Fin N` (decision order = slot order);
an element of `N` with a jittered prime has an exponent vector `v : Fin N → ℕ` over the slots
(its rigid `X₀`-smooth part is not recorded here; by (V1) distinct elements of a window have
distinct vectors). A window set `S` is a `Finset (Fin N → ℕ)`.

For an ordered `k`-tuple `t : Fin k → (Fin N → ℕ)` of exponent vectors:
* its **columns** are the slots of its support `colSupp t` (the primes occurring), listed in
  decision order **latest first** (`colSlot`), and its exponent matrix is `cfgMat t` (over `ℚ`, in
  the convention of `BSCert.StageRows`: column `0` is the latest decided);
* its **greedy pivots** are `BSCert.StageRows.IsPivot` (`isPivot_iff_greedy`), its runs and stages
  are `RunStart`/`stageOf`/`numRuns`;
* its **skeleton** `skel t = (E_P, l)` (Appendix A, "Skeletons"): the pivot pattern `E_P` with the
  pivot columns in decision order, **earliest first** (as in Lemma A.3 and `tauSlot`), and the run
  structure `l = [j_T, …, j_1]` (earliest run first, as in `comps`/`finG`).

Results:
* `RankFull.Config.skel_mem` : for a rank-`k` tuple, `E_P` is invertible and `l ∈ comps k`;
* `RankFull.Config.factorial_mul_rankFullCount_le` : `k! · #{rank-k k-subsets of S} ≤
  #{ordered rank-k k-tuples}`;
* `RankFull.Config.skeletonReduction` : **the reduction to skeletons** (proof of Theorem A.12) for
  the skeleton counts `skelCount`, i.e. `SkeletonReduction k (rankFullCount k S) (skelCount S)`
  pathwise.
-/

@[expose] public section

open Finset BSCert.StageRows
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

/-- The ordered rank-`k` `k`-tuples of distinct vectors of `S`. -/
noncomputable def rankTuples (k : ℕ) (S : Finset (Fin N → ℕ)) : Finset (Fin k → (Fin N → ℕ)) :=
  (Fintype.piFinset fun _ => S).filter fun t =>
    Function.Injective t ∧ LinearIndependent ℚ (fun i => Covers.vq (t i))

/-- `k! · #{rank-k k-subsets} ≤ #{ordered rank-k k-tuples}`. -/
theorem factorial_mul_rankFullCount_le (k : ℕ) (S : Finset (Fin N → ℕ)) :
    k.factorial * rankFullCount k S ≤ (rankTuples k S).card := by
  set subs := (S.powersetCard k).filter fun T : Finset (Fin N → ℕ) =>
    LinearIndepOn ℚ Covers.vq (↑T : Set (Fin N → ℕ)) with hsubs
  have hRF : rankFullCount k S = subs.card := by
    unfold rankFullCount; rfl
  set fib : Finset (Fin N → ℕ) → Finset (Fin k → (Fin N → ℕ)) :=
    fun T => (rankTuples k S).filter fun t => univ.image t = T with hfib
  have hdisj : (subs : Set (Finset (Fin N → ℕ))).PairwiseDisjoint fib := by
    intro T _ T' _ hTT'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht ht'
    exact hTT' ((Finset.mem_filter.mp ht).2.symm.trans (Finset.mem_filter.mp ht').2)
  have hbig : (subs.biUnion fib).card ≤ (rankTuples k S).card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr fun T _ => Finset.filter_subset _ _)
  rw [Finset.card_biUnion hdisj] at hbig
  have hfiber : ∀ T ∈ subs, k.factorial ≤ (fib T).card := by
    intro T hT
    obtain ⟨hTS, hTli⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTsub, hTk⟩ := Finset.mem_powersetCard.mp hTS
    have hcard : Fintype.card (Fin k) = Fintype.card T := by simp [hTk]
    have e0 : Fin k ≃ T := Fintype.equivOfCardEq hcard
    have hk : (Finset.univ : Finset (Fin k ≃ T)).card = k.factorial := by
      rw [Finset.card_univ, Fintype.card_equiv e0, Fintype.card_fin]
    rw [← hk]
    refine Finset.card_le_card_of_injOn (fun e i => ((e i : T) : Fin N → ℕ)) ?_ ?_
    · intro e _
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [Fintype.mem_piFinset]; intro i; exact hTsub (e i).2
      · intro i j hij; exact e.injective (Subtype.ext hij)
      · have : LinearIndependent ℚ (fun x : T => Covers.vq (x : Fin N → ℕ)) := hTli
        exact this.comp e e.injective
      · ext v
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩; exact (e i).2
        · intro hv; exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    · intro e _ e' _ h
      ext i
      have := congrFun h i
      exact congrArg Subtype.val (Subtype.ext this) |>.symm ▸ rfl
  calc k.factorial * rankFullCount k S = ∑ _T ∈ subs, k.factorial := by
        rw [hRF, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ T ∈ subs, (fib T).card := Finset.sum_le_sum hfiber
    _ ≤ _ := hbig

/-! ## Columns, the exponent matrix, pivots and runs of a tuple -/

/-- The slots occurring in the tuple (the columns `P(B')`). -/
noncomputable def colSupp {k : ℕ} (t : Fin k → (Fin N → ℕ)) : Finset (Fin N) :=
  univ.filter fun n => ∃ i, t i n ≠ 0

/-- Column `c` (latest first) is the slot `colSlot t c`. -/
noncomputable def colSlot {k : ℕ} (t : Fin k → (Fin N → ℕ)) (c : Fin (colSupp t).card) : Fin N :=
  (colSupp t).orderEmbOfFin rfl (Fin.rev c)

/-- The exponent matrix of the tuple, columns latest first. -/
noncomputable def cfgMat {k : ℕ} (t : Fin k → (Fin N → ℕ)) :
    Matrix (Fin k) (Fin (colSupp t).card) ℚ :=
  fun i c => (t i (colSlot t c) : ℚ)

/-- The greedy pivots. -/
noncomputable def pivs {k : ℕ} (t : Fin k → (Fin N → ℕ)) : Finset (Fin (colSupp t).card) :=
  pivotsIn (cfgMat t) Set.univ

/-- The run structure `[j_T, …, j_1]` (earliest run first). -/
noncomputable def runList {k : ℕ} (t : Fin k → (Fin N → ℕ)) : List ℕ :=
  (List.range (numRuns (cfgMat t))).reverse.map fun i =>
    ((pivs t).filter fun p => stageOf (cfgMat t) p = i + 1).card

/-- The pivot pattern `E_P` (pivots earliest first), when there are `k` pivots. -/
noncomputable def pattern {k : ℕ} (t : Fin k → (Fin N → ℕ)) : Matrix (Fin k) (Fin k) ℕ :=
  if h : (pivs t).card = k then
    fun i j => t i (colSlot t ((pivs t).orderEmbOfFin h (Fin.rev j)))
  else 0

/-- **The skeleton** `(E_P, l)` of an ordered tuple. -/
noncomputable def skel {k : ℕ} (t : Fin k → (Fin N → ℕ)) : Matrix (Fin k) (Fin k) ℕ × List ℕ :=
  (pattern t, runList t)

/-- The rows of the exponent matrix of a rank-`k` tuple are linearly independent. -/
lemma cfgMat_rows_li {k : ℕ} {t : Fin k → (Fin N → ℕ)}
    (ht : LinearIndependent ℚ (fun i => Covers.vq (t i))) :
    LinearIndependent ℚ (cfgMat t).row := by
  rw [Fintype.linearIndependent_iff] at ht ⊢
  intro g hg i
  apply ht g _ i
  funext n
  by_cases hn : n ∈ colSupp t
  · -- `n` is a column
    obtain ⟨c, hc⟩ : ∃ c : Fin (colSupp t).card, colSlot t c = n := by
      have hn' : n ∈ Set.range ((colSupp t).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hn
      obtain ⟨c', hc'⟩ := hn'
      exact ⟨Fin.rev c', by simp [colSlot, hc']⟩
    have := congrFun hg c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← hc]
    simpa [Matrix.row, cfgMat, Covers.vq] using this
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ∀ i, t i n = 0 := by
      intro i; by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, h⟩)
    simp [Covers.vq, this]

/-- A rank-`k` tuple has exactly `k` greedy pivots. -/
lemma card_pivs {k : ℕ} {t : Fin k → (Fin N → ℕ)}
    (ht : LinearIndependent ℚ (fun i => Covers.vq (t i))) : (pivs t).card = k := by
  have h1 := card_stageRows (cfgMat t) (rk := fun i : Fin k => (i : ℕ)) Fin.val_injective
    Set.univ
  rw [stageRows_univ (cfgMat t) Fin.val_injective (cfgMat_rows_li ht)] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  exact h1.symm

/-- **For a rank-`k` tuple, `E_P` is invertible and `l ∈ comps k`.** -/
theorem skel_mem {k : ℕ} {t : Fin k → (Fin N → ℕ)}
    (ht : LinearIndependent ℚ (fun i => Covers.vq (t i))) :
    (skel t).1 ∈ InvPattern k ∧ (skel t).2 ∈ comps k := by
  have hk := card_pivs ht
  refine ⟨?_, ?_⟩
  · -- the pivot columns are linearly independent
    show ((pattern t).map (Nat.cast : ℕ → ℚ)).det ≠ 0
    set e := (pivs t).orderEmbOfFin hk with he
    have hmat : (pattern t).map (Nat.cast : ℕ → ℚ) =
        Matrix.of fun i j => cfgMat t i (e (Fin.rev j)) := by
      ext i j; simp [pattern, hk, cfgMat, he]
    rw [hmat]
    have hli := pivots_linIndepOn (cfgMat t) Set.univ
    have hcols : LinearIndependent ℚ (Matrix.of fun i j => cfgMat t i (e (Fin.rev j))).col := by
      have h1 : LinearIndependent ℚ (fun p : (pivs t) => (cfgMat t).col p) := hli
      have h2 : Function.Injective fun j : Fin k => (⟨e (Fin.rev j), by
          simp [he, Finset.orderEmbOfFin_mem]⟩ : pivs t) := by
        intro a b hab
        have := congrArg Subtype.val hab
        simpa using this
      have h3 := h1.comp _ h2
      convert h3 using 1
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)).ne_zero
  · -- the run structure is a composition of `k`
    rw [mem_comps]
    refine ⟨?_, ?_⟩
    · intro j hj
      change j ∈ runList t at hj
      unfold runList at hj
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
      have haT : a < numRuns (cfgMat t) := by simpa using ha
      obtain ⟨p, hp, hps⟩ := exists_pivot_of_stage (cfgMat t) (t := a + 1) (by omega) (by omega)
      apply Finset.card_pos.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨mem_pivotsIn.mpr ⟨Set.mem_univ _, hp⟩, hps⟩⟩
    · show (runList t).sum = k
      unfold runList
      rw [list_sum_map_range_reverse]
      refine Eq.trans ?_ hk
      symm
      rw [Finset.card_eq_sum_card_fiberwise (f := fun p => stageOf (cfgMat t) p - 1)
        (t := range (numRuns (cfgMat t)))]
      · refine Finset.sum_congr rfl fun i hi => ?_
        congr 1
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, h⟩
          refine ⟨hp, ?_⟩
          have := one_le_stageOf_of_pivot (cfgMat t) (mem_pivotsIn.mp hp).2
          omega
        · rintro ⟨hp, h⟩; exact ⟨hp, by omega⟩
      · intro p hp
        have h1 := one_le_stageOf_of_pivot (cfgMat t) (mem_pivotsIn.mp hp).2
        have h2 := stageOf_le_numRuns (cfgMat t) p
        simp only [Finset.coe_range, Set.mem_Iio]
        omega

/-! ## The reduction to skeletons -/

/-- The skeleton counts `X_𝔰`: the number of ordered rank-`k` tuples of `S` with skeleton `𝔰`. -/
noncomputable def skelCount {k : ℕ} (S : Finset (Fin N → ℕ)) (E : Matrix (Fin k) (Fin k) ℕ)
    (l : List ℕ) : ℝ≥0∞ :=
  ((rankTuples k S).filter fun t => skel t = (E, l)).card

/-- **The reduction to skeletons** (proof of Theorem A.12), pathwise. -/
theorem skeletonReduction {Ω : Type*} (k : ℕ) (S : Ω → Finset (Fin N → ℕ)) :
    SkeletonReduction k (fun ω => (rankFullCount k (S ω) : ℝ≥0∞))
      (fun E l ω => skelCount (S ω) E l) := by
  intro ω
  set T := rankTuples k (S ω)
  -- the tuples, grouped by skeleton
  have hcount : ((T.card : ℕ) : ℝ≥0∞) ≤
      ∑' E, (InvPattern k).indicator (fun E => ∑ l ∈ comps k, skelCount (S ω) E l) E := by
    -- the skeletons that occur
    set Sk := T.image skel
    have hSk : ∀ s ∈ Sk, s.1 ∈ InvPattern k ∧ s.2 ∈ comps k := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact skel_mem (Finset.mem_filter.mp ht).2.2
    have h1 : T.card = ∑ s ∈ Sk, (T.filter fun t => skel t = s).card :=
      Finset.card_eq_sum_card_fiberwise (fun t ht => Finset.mem_image_of_mem _ ht)
    -- each fibre is a term of the double sum
    set F : Matrix (Fin k) (Fin k) ℕ × List ℕ → ℝ≥0∞ := fun s =>
      ((T.filter fun t => skel t = s).card : ℝ≥0∞)
    have h2 : ((T.card : ℕ) : ℝ≥0∞) = ∑ s ∈ Sk, F s := by
      rw [h1]; push_cast; rfl
    rw [h2]
    have h3 : ∑ s ∈ Sk, F s ≤ ∑ s ∈ Sk.image Prod.fst ×ˢ (comps k), F s := by
      apply Finset.sum_le_sum_of_subset
      intro s hs
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs, (hSk s hs).2⟩
    refine h3.trans ?_
    rw [Finset.sum_product]
    calc ∑ E ∈ Sk.image Prod.fst, ∑ l ∈ comps k, F (E, l)
        = ∑ E ∈ Sk.image Prod.fst,
            (InvPattern k).indicator (fun E => ∑ l ∈ comps k, skelCount (S ω) E l) E := by
          refine Finset.sum_congr rfl fun E hE => ?_
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hE
          rw [Set.indicator_of_mem (hSk s hs).1]
          rfl
      _ ≤ ∑' E, (InvPattern k).indicator (fun E => ∑ l ∈ comps k, skelCount (S ω) E l) E :=
          ENNReal.sum_le_tsum _
  calc (k.factorial : ℝ≥0∞) * (rankFullCount k (S ω) : ℝ≥0∞)
      = ((k.factorial * rankFullCount k (S ω) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((T.card : ℕ) : ℝ≥0∞) := by exact_mod_cast factorial_mul_rankFullCount_le k (S ω)
    _ ≤ _ := hcount

end RankFull.Config
