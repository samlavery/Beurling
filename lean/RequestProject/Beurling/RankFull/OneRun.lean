module

public import RequestProject.Beurling.RankFull.ConfigReduction

/-!
# The pivot structure of a one-run tuple

For an ordered rank-`k` tuple `t` (`Config.lean`), the pivot slots `pivSlot t hk j` (pivot `j`
the `j`-th earliest) are strictly increasing in `j`, and if the run structure is the single run
`[k]` (Appendix A, "Runs and blocks": `T = 1`, no late block), every free column is decided
before every pivot (`free_lt_pivSlot`): the early block `F_T` is the only block.
-/

@[expose] public section

open Finset BSCert.StageRows
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

lemma colSlot_strictAnti {k : ℕ} (t : Fin k → (Fin N → ℕ)) : StrictAnti (colSlot t) := by
  intro a b hab
  unfold colSlot
  exact ((colSupp t).orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hab)

lemma pivSlot_strictMono {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) :
    StrictMono (pivSlot t hk) := by
  intro a b hab
  unfold pivSlot
  exact colSlot_strictAnti t (((pivs t).orderEmbOfFin hk).strictMono (Fin.rev_lt_rev.mpr hab))

lemma exists_colSlot {k : ℕ} {t : Fin k → (Fin N → ℕ)} {n : Fin N} (hn : n ∈ colSupp t) :
    ∃ c, colSlot t c = n := by
  have hn' : n ∈ Set.range ((colSupp t).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hn
  obtain ⟨c', hc'⟩ := hn'
  exact ⟨Fin.rev c', by simp [colSlot, hc']⟩

lemma colSlot_mem {k : ℕ} (t : Fin k → (Fin N → ℕ)) (c : Fin (colSupp t).card) :
    colSlot t c ∈ colSupp t := by
  unfold colSlot; exact Finset.orderEmbOfFin_mem _ _ _

/-- The latest column is a pivot. -/
lemma isPivot_zero {k : ℕ} (t : Fin k → (Fin N → ℕ)) (c : Fin (colSupp t).card)
    (hc : (c : ℕ) = 0) : IsPivot (cfgMat t) c := by
  unfold IsPivot
  have hempty : {q : Fin (colSupp t).card | q < c} = ∅ := by
    ext q; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Fin.le_def.mpr (by omega)
  rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot]
  intro h0
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp (colSlot_mem t c)).2
  have := congrFun h0 i
  simp only [Matrix.col_apply, cfgMat, Pi.zero_apply, Nat.cast_eq_zero] at this
  exact hi this

lemma numRuns_of_runList {k : ℕ} {t : Fin k → (Fin N → ℕ)} (h : runList t = [k]) :
    numRuns (cfgMat t) = 1 := by
  have := congrArg List.length h
  unfold runList at this
  simpa using this

/-- In a one-run tuple, the pivots are the latest columns: every column decided no earlier than a
pivot is a pivot. -/
lemma isPivot_of_le {k : ℕ} {t : Fin k → (Fin N → ℕ)} (h1 : numRuns (cfgMat t) = 1) :
    ∀ (n : ℕ) (p : Fin (colSupp t).card), (p : ℕ) = n → IsPivot (cfgMat t) p →
      ∀ q, q ≤ p → IsPivot (cfgMat t) q := by
  intro n
  induction n with
  | zero =>
    intro p hp _ q hq
    exact isPivot_zero t q (by have := Fin.le_def.mp hq; omega)
  | succ n ih =>
    intro p hp hpiv q hq
    rcases Fin.lt_or_eq_of_le hq with hlt | rfl
    · -- the predecessor of `p` is a pivot, else `p` would start a second run
      set p' : Fin (colSupp t).card := ⟨n, by omega⟩ with hp'
      have hp'piv : IsPivot (cfgMat t) p' := by
        by_contra hnot
        have hrs : RunStart (cfgMat t) p := ⟨hpiv, fun q' hq' => by
          have : q' = p' := Fin.ext (by simp [hp']; omega)
          rw [this]; exact hnot⟩
        set z : Fin (colSupp t).card := ⟨0, by omega⟩ with hz
        have hrz : RunStart (cfgMat t) z := ⟨isPivot_zero t z rfl, fun q' hq' => by
          simp [hz] at hq'⟩
        have hpz : p ≠ z := fun h => by
          have := congrArg Fin.val h; simp [hz] at this; omega
        have h2 : 2 ≤ numRuns (cfgMat t) := by
          unfold numRuns
          have : ({p, z} : Finset _) ⊆ univ.filter (fun p => RunStart (cfgMat t) p) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrz⟩
          have := Finset.card_le_card this
          rw [Finset.card_pair hpz] at this
          exact this
        omega
      exact ih p' rfl hp'piv q (Fin.le_def.mpr (by have := Fin.lt_def.mp hlt; simp [hp']; omega))
    · exact hpiv

/-- **One run** (`l = [k]`): every free slot of the tuple is decided before every pivot. -/
theorem free_lt_pivSlot {k : ℕ} {t : Fin k → (Fin N → ℕ)} (hk : (pivs t).card = k)
    (hrun : runList t = [k]) {n : Fin N} (hn : ∃ i, t i n ≠ 0)
    (hnp : ∀ j, pivSlot t hk j ≠ n) (j : Fin k) : n < pivSlot t hk j := by
  have h1 := numRuns_of_runList hrun
  obtain ⟨c, rfl⟩ := exists_colSlot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  set p := (pivs t).orderEmbOfFin hk (Fin.rev j) with hp
  have hpp : p ∈ pivs t := Finset.orderEmbOfFin_mem _ _ _
  have hppiv : IsPivot (cfgMat t) p := (mem_pivotsIn.mp hpp).2
  -- `c` is not a pivot
  have hcnp : ¬ IsPivot (cfgMat t) c := by
    intro hc
    have hcm : c ∈ pivs t := mem_pivotsIn.mpr ⟨Set.mem_univ _, hc⟩
    have : c ∈ Set.range ((pivs t).orderEmbOfFin hk) := by
      rw [Finset.range_orderEmbOfFin]; exact hcm
    obtain ⟨i, hi⟩ := this
    exact hnp (Fin.rev i) (by simp [pivSlot, hi])
  have hpc : p < c := by
    by_contra hle
    push_neg at hle
    exact hcnp (isPivot_of_le h1 p p rfl hppiv c hle)
  exact colSlot_strictAnti t hpc

/-- The set of pivot slots of a tuple. -/
noncomputable def pivSet {k : ℕ} (t : Fin k → (Fin N → ℕ)) : Finset (Fin N) :=
  (pivs t).image (colSlot t)

lemma pivSet_eq_image {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) :
    pivSet t = univ.image (pivSlot t hk) := by
  ext n
  simp only [pivSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have : c ∈ Set.range ((pivs t).orderEmbOfFin hk) := by
      rw [Finset.range_orderEmbOfFin]; exact hc
    obtain ⟨i, hi⟩ := this
    exact ⟨Fin.rev i, by simp [pivSlot, hi]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, Finset.orderEmbOfFin_mem _ _ _, rfl⟩

lemma mem_pivSet {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) (n : Fin N) :
    n ∈ pivSet t ↔ ∃ j, pivSlot t hk j = n := by
  rw [pivSet_eq_image t hk]; simp

lemma pivSlot_mem_colSupp {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k)
    (j : Fin k) : ∃ i, t i (pivSlot t hk j) ≠ 0 :=
  (Finset.mem_filter.mp (colSlot_mem t _)).2

/-- Splitting a monomial into its free part and its pivot part. -/
lemma prod_split {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) (q : Fin N → ℝ)
    (v : Fin N → ℕ) :
    ∏ n, q n ^ v n = (∏ n, q n ^ (if n ∈ pivSet t then 0 else v n)) *
      ∏ j, q (pivSlot t hk j) ^ v (pivSlot t hk j) := by
  have h1 : ∀ n, q n ^ v n = q n ^ (if n ∈ pivSet t then 0 else v n) *
      (if n ∈ pivSet t then q n ^ v n else 1) := by
    intro n; split_ifs <;> simp
  rw [Finset.prod_congr rfl fun n _ => h1 n, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, pivSet_eq_image t hk,
    Finset.prod_image fun a _ b _ h => pivSlot_injective t hk h]

end RankFull.Config
