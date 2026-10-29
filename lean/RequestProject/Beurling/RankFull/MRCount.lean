module

public import RequestProject.Beurling.RankFull.MultiRun

/-!
# The run structure of a realised tuple

For an ordered rank-`K` tuple `t` with skeleton `(E, l)`, the runs of `l` (`runNum`, `runFirst`)
are the runs of greedy pivots of `t` (`BSCert.StageRows.RunStart`/`stageOf`):
* `RankFull.Config.runNum_tuple` : the run index of pattern column `j` is `T - stage`;
* `RankFull.Config.sameRun_iff` : consecutive pattern columns are in the same run iff no slot of
  the tuple lies strictly between their pivot slots.
-/

@[expose] public section

open Finset BSCert.StageRows RankFull.Runs
open scoped ENNReal Classical

namespace RankFull.Config

variable {N K : ℕ}

/-- The `k`-th pivot column (latest first). -/
noncomputable def pk (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (k : Fin K) :
    Fin (colSupp t).card :=
  (pivs t).orderEmbOfFin hk k

lemma pk_mem (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (k : Fin K) :
    pk t hk k ∈ pivs t := Finset.orderEmbOfFin_mem _ _ _

lemma pk_strictMono (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) :
    StrictMono (pk t hk) := ((pivs t).orderEmbOfFin hk).strictMono

lemma pk_surj (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) {c : Fin (colSupp t).card}
    (hc : c ∈ pivs t) : ∃ k, pk t hk k = c := by
  have : c ∈ Set.range ((pivs t).orderEmbOfFin hk) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact this

lemma pivSlot_eq (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (j : Fin K) :
    pivSlot t hk j = colSlot t (pk t hk (Fin.rev j)) := rfl

/-- No pivot strictly between consecutive pivots. -/
lemma no_pivot_between (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) {k : ℕ}
    (hk1 : k + 1 < K) {c : Fin (colSupp t).card} (h1 : pk t hk ⟨k, by omega⟩ < c)
    (h2 : c < pk t hk ⟨k + 1, hk1⟩) : c ∉ pivs t := by
  intro hc
  obtain ⟨i, rfl⟩ := pk_surj t hk hc
  have a := (pk_strictMono t hk).lt_iff_lt.mp h1
  have b := (pk_strictMono t hk).lt_iff_lt.mp h2
  have := Fin.lt_def.mp a
  have := Fin.lt_def.mp b
  simp at *
  omega

/-- A pivot starts a run iff a column lies strictly between it and the previous pivot. -/
lemma runStart_iff (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) {k : ℕ}
    (hk1 : k + 1 < K) :
    RunStart (cfgMat t) (pk t hk ⟨k + 1, hk1⟩) ↔
      ∃ c, pk t hk ⟨k, by omega⟩ < c ∧ c < pk t hk ⟨k + 1, hk1⟩ := by
  have hlt : pk t hk ⟨k, by omega⟩ < pk t hk ⟨k + 1, hk1⟩ :=
    pk_strictMono t hk (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
  constructor
  · rintro ⟨-, hno⟩
    have hp : 1 ≤ ((pk t hk ⟨k + 1, hk1⟩ : Fin (colSupp t).card) : ℕ) := by
      have := Fin.lt_def.mp hlt; omega
    set q : Fin (colSupp t).card := ⟨(pk t hk ⟨k + 1, hk1⟩ : ℕ) - 1, by omega⟩ with hq
    have hqnp := hno q (by simp [hq]; omega)
    refine ⟨q, ?_, Fin.lt_def.mpr (by simp [hq]; omega)⟩
    have hle : pk t hk ⟨k, by omega⟩ ≤ q := Fin.le_def.mpr (by
      have := Fin.lt_def.mp hlt; simp [hq]; omega)
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso; apply hqnp; rw [← h]; exact (mem_pivotsIn.mp (pk_mem t hk _)).2
  · rintro ⟨c, h1, h2⟩
    refine ⟨(mem_pivotsIn.mp (pk_mem t hk _)).2, fun q hq hqp => ?_⟩
    have hqc : pk t hk ⟨k, by omega⟩ < q := by
      have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2
      exact Fin.lt_def.mpr (by omega)
    have hqk : q < pk t hk ⟨k + 1, hk1⟩ := Fin.lt_def.mpr (by omega)
    exact no_pivot_between t hk hk1 hqc hqk (mem_pivotsIn.mpr ⟨Set.mem_univ _, hqp⟩)

/-- The stage increases by one exactly at the run starts. -/
lemma stageOf_succ (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) {k : ℕ}
    (hk1 : k + 1 < K) :
    stageOf (cfgMat t) (pk t hk ⟨k + 1, hk1⟩) = stageOf (cfgMat t) (pk t hk ⟨k, by omega⟩) +
      if RunStart (cfgMat t) (pk t hk ⟨k + 1, hk1⟩) then 1 else 0 := by
  set c := pk t hk ⟨k, by omega⟩ with hc
  set c' := pk t hk ⟨k + 1, hk1⟩ with hc'
  have hlt : c < c' := pk_strictMono t hk (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
  unfold stageOf
  have hsplit : (univ.filter fun p => p ≤ c' ∧ RunStart (cfgMat t) p) =
      (univ.filter fun p => p ≤ c ∧ RunStart (cfgMat t) p) ∪
        (if RunStart (cfgMat t) c' then {c'} else ∅) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hp, hrs⟩
      by_cases hpc : p ≤ c
      · exact Or.inl ⟨hpc, hrs⟩
      · right
        push_neg at hpc
        rcases hp.lt_or_eq with hp' | rfl
        · exact absurd (mem_pivotsIn.mpr ⟨Set.mem_univ _, hrs.1⟩)
            (no_pivot_between t hk hk1 hpc hp')
        · rw [if_pos hrs]; exact Finset.mem_singleton_self _
    · rintro (⟨hpc, hrs⟩ | h)
      · exact ⟨hpc.trans hlt.le, hrs⟩
      · split_ifs at h with hrs
        · rw [Finset.mem_singleton] at h; subst h; exact ⟨le_rfl, hrs⟩
        · exact absurd h (Finset.notMem_empty _)
  rw [hsplit, Finset.card_union_of_disjoint]
  · split_ifs <;> simp
  · rw [Finset.disjoint_left]
    intro p hp hp'
    split_ifs at hp' with hrs
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact absurd (Finset.mem_filter.mp hp).2.1 (not_le.mpr hlt)
    · exact absurd hp' (Finset.notMem_empty _)

/-- The first pivot is the latest column, of stage `1`. -/
lemma stageOf_pk_zero (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hK : 0 < K) :
    stageOf (cfgMat t) (pk t hk ⟨0, hK⟩) = 1 := by
  have hcard : 0 < (colSupp t).card := by
    have := Finset.card_le_univ (pivs t)
    rw [Fintype.card_fin] at this; omega
  set z : Fin (colSupp t).card := ⟨0, hcard⟩ with hz
  have hzp : z ∈ pivs t := mem_pivotsIn.mpr ⟨Set.mem_univ _, isPivot_zero t z rfl⟩
  obtain ⟨i, hi⟩ := pk_surj t hk hzp
  have hpk0 : pk t hk ⟨0, hK⟩ = z := by
    apply le_antisymm _ (Fin.le_def.mpr (Nat.zero_le _))
    rw [← hi]
    exact (pk_strictMono t hk).monotone (Fin.le_def.mpr (Nat.zero_le _))
  rw [hpk0]
  unfold stageOf
  have : (univ.filter fun p => p ≤ z ∧ RunStart (cfgMat t) p) = {z} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, -⟩; exact le_antisymm hp (Fin.le_def.mpr (Nat.zero_le _))
    · rintro rfl
      exact ⟨le_rfl, isPivot_zero t z rfl, fun q hq => by simp [hz] at hq⟩
  rw [this, Finset.card_singleton]

lemma sum_take_eq_getD (l : List ℕ) : ∀ i : ℕ, (l.take i).sum = ∑ i' ∈ range i, l.getD i' 0
  | 0 => by simp
  | i + 1 => by
    rw [List.take_succ, List.sum_append, sum_take_eq_getD l i, Finset.sum_range_succ]
    congr 1
    by_cases hi : i < l.length
    · simp [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
    · push_neg at hi
      simp [List.getElem?_eq_none hi, List.getD_eq_default _ _ hi]

/-- A down-closed set of `Fin K` is an initial segment. -/
lemma mem_iff_lt_card_of_downClosed {S : Finset (Fin K)}
    (hS : ∀ a b, a ≤ b → b ∈ S → a ∈ S) (j : Fin K) : j ∈ S ↔ (j : ℕ) < S.card := by
  constructor
  · intro hj
    have hsub : (univ.filter fun a : Fin K => a ≤ j) ⊆ S := fun a ha =>
      hS a j (Finset.mem_filter.mp ha).2 hj
    have h1 := Finset.card_le_card hsub
    have h2 : (univ.filter fun a : Fin K => a ≤ j).card = (j : ℕ) + 1 := by
      have := Fin.card_filter_val_lt (n := K) (m := (j : ℕ) + 1)
      have e : (univ.filter fun a : Fin K => a ≤ j) =
          (univ.filter fun a : Fin K => (a : ℕ) < (j : ℕ) + 1) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => Nat.lt_succ_of_le (Fin.le_def.mp h),
          fun h => Fin.le_def.mpr (Nat.le_of_lt_succ h)⟩
      rw [e, this]; have := j.isLt; omega
    omega
  · intro hj
    by_contra hjS
    have hsub : S ⊆ (univ.filter fun a : Fin K => (a : ℕ) < (j : ℕ)) := by
      intro a ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra h
      push_neg at h
      exact hjS (hS j a (Fin.le_def.mpr h) ha)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at h1
    omega

/-- **The run index of a pattern column is `T - stage`.** -/
theorem runNum_tuple (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K)
    (hrun : runList t = l) (hsum : l.sum = K) (j : Fin K) :
    runNum l j = numRuns (cfgMat t) - stageOf (cfgMat t) (pk t hk (Fin.rev j)) := by
  set T := numRuns (cfgMat t) with hT
  set r : Fin K → ℕ := fun j => T - stageOf (cfgMat t) (pk t hk (Fin.rev j)) with hr
  have hrmono : Monotone r := by
    intro a b hab
    simp only [hr]
    have := stageOf_mono (cfgMat t) ((pk_strictMono t hk).monotone (Fin.rev_le_rev.mpr hab))
    omega
  have hst1 : ∀ k, 1 ≤ stageOf (cfgMat t) (pk t hk k) := fun k =>
    one_le_stageOf_of_pivot _ (mem_pivotsIn.mp (pk_mem t hk k)).2
  have hstT : ∀ k, stageOf (cfgMat t) (pk t hk k) ≤ T := fun k => stageOf_le_numRuns _ _
  -- the counts of the stages
  have hget : ∀ i', l.getD i' 0 = if i' < T then
      ((pivs t).filter fun p => stageOf (cfgMat t) p = T - i').card else 0 := by
    intro i'
    rw [← hrun]
    unfold runList
    by_cases hi : i' < T
    · rw [if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    · rw [if_neg hi, List.getD_eq_default _ _ (by simpa using hi)]
  have hfib : ∀ i', (univ.filter fun j' : Fin K => r j' = i').card = l.getD i' 0 := by
    intro i'
    rw [hget]
    split_ifs with hi
    · have himg : (univ.filter fun j' : Fin K => r j' = i').image
          (fun j' => pk t hk (Fin.rev j')) =
          (pivs t).filter fun p => stageOf (cfgMat t) p = T - i' := by
        ext p
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hr]
        constructor
        · rintro ⟨j', hj', rfl⟩
          exact ⟨pk_mem t hk _, by have := hst1 (Fin.rev j'); have := hstT (Fin.rev j'); omega⟩
        · rintro ⟨hp, hps⟩
          obtain ⟨k, rfl⟩ := pk_surj t hk hp
          refine ⟨Fin.rev k, ?_, by simp⟩
          rw [Fin.rev_rev]; have := hst1 k; omega
      rw [← himg, Finset.card_image_of_injective _ (f := fun j' => pk t hk (Fin.rev j'))
        (fun a b h => Fin.rev_injective ((pk_strictMono t hk).injective h))]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j' _ hj'
      have := hst1 (Fin.rev j')
      have := hstT (Fin.rev j')
      simp only [hr] at hj'
      omega
  have hcount : ∀ i, (univ.filter fun j' : Fin K => r j' < i).card = (l.take i).sum := by
    intro i
    rw [sum_take_eq_getD, Finset.card_eq_sum_card_fiberwise (f := r) (t := range i)
      (fun j' hj' => Finset.mem_range.mpr (Finset.mem_filter.mp hj').2)]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    rw [← hfib i']
    congr 1
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact Finset.mem_range.mp hi', h⟩
  have hdown : ∀ i, ∀ a b : Fin K, a ≤ b → b ∈ (univ.filter fun j' : Fin K => r j' < i) →
      a ∈ (univ.filter fun j' : Fin K => r j' < i) := by
    intro i a b hab hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_le_of_lt (hrmono hab) (Finset.mem_filter.mp hb).2⟩
  have key := runNum_eq_of_lt_iff l (fun j' => if h : j' < K then r ⟨j', h⟩ else 0)
    (j := j) (by rw [hsum]; exact j.isLt) (fun i => by
      simp only [dif_pos j.isLt]
      have := mem_iff_lt_card_of_downClosed (hdown i) j
      rw [Finset.mem_filter, hcount i] at this
      simpa using this)
  rw [key]
  simp only [j.isLt, dif_pos, hr]

/-- **Consecutive pattern columns are in the same run iff no slot of the tuple lies strictly
between their pivot slots.** -/
theorem sameRun_iff (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hrun : runList t = l)
    (hsum : l.sum = K) {j : ℕ} (hj1 : 1 ≤ j) (hjK : j < K) :
    runNum l (j - 1) = runNum l j ↔
      ¬ ∃ g ∈ colSupp t, pivSlot t hk ⟨j - 1, by omega⟩ < g ∧ g < pivSlot t hk ⟨j, hjK⟩ := by
  have h1 := runNum_tuple t hk hrun hsum ⟨j - 1, by omega⟩
  have h2 := runNum_tuple t hk hrun hsum ⟨j, hjK⟩
  simp only at h1 h2
  rw [h1, h2]
  set k := K - 1 - j with hkdef
  have e1 : Fin.rev (⟨j - 1, by omega⟩ : Fin K) = ⟨k + 1, by omega⟩ := Fin.ext (by simp; omega)
  have e2 : Fin.rev (⟨j, hjK⟩ : Fin K) = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
  rw [e1, e2, stageOf_succ t hk (k := k) (by omega)]
  have hst1 := one_le_stageOf_of_pivot (cfgMat t) (mem_pivotsIn.mp (pk_mem t hk ⟨k, by omega⟩)).2
  have hstT := stageOf_le_numRuns (cfgMat t) (pk t hk ⟨k + 1, by omega⟩)
  rw [stageOf_succ t hk (k := k) (by omega)] at hstT
  have hiff : (numRuns (cfgMat t) - (stageOf (cfgMat t) (pk t hk ⟨k, by omega⟩) +
      if RunStart (cfgMat t) (pk t hk ⟨k + 1, by omega⟩) then 1 else 0) =
      numRuns (cfgMat t) - stageOf (cfgMat t) (pk t hk ⟨k, by omega⟩)) ↔
      ¬ RunStart (cfgMat t) (pk t hk ⟨k + 1, by omega⟩) := by
    split_ifs with h <;> simp [h] at hstT ⊢ <;> omega
  rw [hiff, runStart_iff t hk (k := k) (by omega)]
  have ep1 : pivSlot t hk ⟨j - 1, by omega⟩ = colSlot t (pk t hk ⟨k + 1, by omega⟩) := by
    rw [pivSlot_eq, e1]
  have ep2 : pivSlot t hk ⟨j, hjK⟩ = colSlot t (pk t hk ⟨k, by omega⟩) := by
    rw [pivSlot_eq, e2]
  rw [ep1, ep2]
  constructor
  · intro hno ⟨g, hg, hg1, hg2⟩
    obtain ⟨c, rfl⟩ := exists_colSlot hg
    apply hno
    refine ⟨c, ?_, ?_⟩
    · by_contra h; push_neg at h
      rcases h.lt_or_eq with h | h
      · exact absurd hg2 (not_lt.mpr (colSlot_strictAnti t h).le)
      · rw [h] at hg2; exact lt_irrefl _ hg2
    · by_contra h; push_neg at h
      rcases h.lt_or_eq with h | h
      · exact absurd hg1 (not_lt.mpr (colSlot_strictAnti t h).le)
      · rw [← h] at hg1; exact lt_irrefl _ hg1
  · intro hno ⟨c, hc1, hc2⟩
    exact hno ⟨colSlot t c, colSlot_mem t c, colSlot_strictAnti t hc2, colSlot_strictAnti t hc1⟩

/-! ## The constraints of the recursion for a realised tuple -/

lemma pk_zero_val (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hK : 0 < K) :
    ((pk t hk ⟨0, hK⟩ : Fin (colSupp t).card) : ℕ) = 0 := by
  have hcard : 0 < (colSupp t).card := by
    have := Finset.card_le_univ (pivs t)
    rw [Fintype.card_fin] at this; omega
  set z : Fin (colSupp t).card := ⟨0, hcard⟩ with hz
  have hzp : z ∈ pivs t := mem_pivotsIn.mpr ⟨Set.mem_univ _, isPivot_zero t z rfl⟩
  obtain ⟨i, hi⟩ := pk_surj t hk hzp
  have : pk t hk ⟨0, hK⟩ ≤ z := by
    rw [← hi]; exact (pk_strictMono t hk).monotone (Fin.le_def.mpr (Nat.zero_le _))
  have := Fin.le_def.mp this
  simp [hz] at this; omega

/-- The latest pivot slot is the latest slot of the tuple. -/
lemma le_pivSlot_last (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hK : 0 < K)
    {g : Fin N} (hg : g ∈ colSupp t) : g ≤ pivSlot t hk ⟨K - 1, by omega⟩ := by
  obtain ⟨c, rfl⟩ := exists_colSlot hg
  rw [pivSlot_eq]
  have e : Fin.rev (⟨K - 1, by omega⟩ : Fin K) = ⟨0, hK⟩ := Fin.ext (by simp; omega)
  rw [e]
  apply (colSlot_strictAnti t).antitone
  exact Fin.le_def.mpr (by rw [pk_zero_val t hk hK]; exact Nat.zero_le _)

/-- No free slot of the tuple strictly inside the labels of a run. -/
lemma not_between_run (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K)
    (hrun : runList t = l) (hsum : l.sum = K) {g : Fin N} (hg : g ∈ colSupp t)
    (hfree : ∀ i, pivSlot t hk i ≠ g) :
    ∀ (d j : ℕ) (hj : j + d < K), runNum l j = runNum l (j + d) →
      ¬ (pivSlot t hk ⟨j, by omega⟩ < g ∧ g < pivSlot t hk ⟨j + d, hj⟩) := by
  intro d
  induction d with
  | zero => intro j hj _ ⟨h1, h2⟩; exact absurd (h1.trans h2) (lt_irrefl _)
  | succ d ih =>
    intro j hj hr ⟨h1, h2⟩
    have hmid : runNum l j = runNum l (j + d) := by
      have a := runNum_mono l (show j ≤ j + d by omega)
      have b := runNum_mono l (show j + d ≤ j + (d + 1) by omega)
      omega
    have hlast : runNum l (j + d + 1 - 1) = runNum l (j + d + 1) := by
      have a := runNum_mono l (show j + d ≤ j + d + 1 by omega)
      have b := runNum_mono l (show j ≤ j + d by omega)
      have : runNum l (j + d + 1) = runNum l (j + (d + 1)) := by ring_nf
      simp only [Nat.add_sub_cancel]
      omega
    rcases lt_trichotomy g (pivSlot t hk ⟨j + d, by omega⟩) with h | h | h
    · exact ih j (by omega) hmid ⟨h1, h⟩
    · exact hfree _ h.symm
    · have hs := (sameRun_iff t hk hrun hsum (j := j + d + 1) (by omega) (by omega)).mp hlast
      refine hs ⟨g, hg, ?_, ?_⟩
      · convert h using 3
      · convert h2 using 3

/-- The span condition for a free slot of the tuple (Theorem A.10(ii)): its column is a real
combination of the pattern columns of the pivots decided later. -/
theorem free_col_span (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hpat : pattern t = E)
    {g : Fin N} (hg : g ∈ colSupp t) (hfree : g ∉ pivSet t) :
    (fun y => t y g) ∈ SpanSet E {j | K ≤ (j : ℕ) ∨ ∃ h : (j : ℕ) < K,
      (g : ℕ) < (pivSlot t hk ⟨j, h⟩ : ℕ)} := by
  obtain ⟨q, rfl⟩ := exists_colSlot hg
  have hqnp : ¬ IsPivot (cfgMat t) q := by
    intro hq
    exact hfree (Finset.mem_image.mpr ⟨q, mem_pivotsIn.mpr ⟨Set.mem_univ _, hq⟩, rfl⟩)
  have hspan := col_mem_span_pivots (cfgMat t) q
  obtain ⟨S, hS, a, ha⟩ := (Submodule.mem_span_image_iff_exists_fun ℚ).mp hspan
  set v : Fin K → ℝ := fun j =>
    if h : pk t hk (Fin.rev j) ∈ S then ((a ⟨pk t hk (Fin.rev j), h⟩ : ℚ) : ℝ) else 0 with hv
  refine ⟨v, fun j hj => ?_, fun y => ?_⟩
  · simp only [hv]
    rw [dif_neg]
    intro hmem
    apply hj
    have hle := (hS hmem).1
    have hne : pk t hk (Fin.rev j) ≠ q := fun h => hqnp (h ▸ (hS hmem).2)
    have hlt : pk t hk (Fin.rev j) < q := lt_of_le_of_ne hle hne
    right
    refine ⟨j.isLt, ?_⟩
    have := colSlot_strictAnti t hlt
    rw [pivSlot_eq]
    exact this
  · -- evaluate the combination at row `y`
    have hy := congrFun ha y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul] at hy
    have hcast : ((t y (colSlot t q) : ℕ) : ℝ) = ∑ i : S, ((a i : ℚ) : ℝ) *
        ((cfgMat t y (i : Fin (colSupp t).card) : ℚ) : ℝ) := by
      have : ((cfgMat t y q : ℚ) : ℝ) = ∑ i : S, ((a i : ℚ) : ℝ) *
          ((cfgMat t y (i : Fin (colSupp t).card) : ℚ) : ℝ) := by
        rw [← hy]; push_cast; rfl
      rw [← this]; simp [cfgMat]
    rw [hcast]
    -- reindex the pivots of `S` by the pattern columns
    have hpiv : ∀ i : S, ∃ j : Fin K, pk t hk (Fin.rev j) = i := by
      intro i
      obtain ⟨k', hk'⟩ := pk_surj t hk (mem_pivotsIn.mpr ⟨Set.mem_univ _, (hS i.2).2⟩)
      exact ⟨Fin.rev k', by simp [hk']⟩
    have hval : ∀ j : Fin K, ((cfgMat t y (pk t hk (Fin.rev j)) : ℚ) : ℝ) = (E y j : ℝ) := by
      intro j
      have := pattern_eq t hk y j
      rw [hpat] at this
      simp [cfgMat, ← pivSlot_eq, this]
    have hrhs : ∑ j, (E y j : ℝ) * v j =
        ∑ j ∈ univ.filter (fun j : Fin K => pk t hk (Fin.rev j) ∈ S),
        (E y j : ℝ) * v j := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_).symm
      have : pk t hk (Fin.rev j) ∉ S := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [hv, this]
    rw [hrhs]
    symm
    refine Finset.sum_bij (fun j hj => (⟨pk t hk (Fin.rev j), (Finset.mem_filter.mp hj).2⟩ : S))
      (fun j hj => Finset.mem_univ _) (fun j hj j' hj' h => ?_) (fun i _ => ?_) (fun j hj => ?_)
    · have := congrArg Subtype.val h
      exact Fin.rev_injective ((pk_strictMono t hk).injective this)
    · obtain ⟨j, hj⟩ := hpiv i
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ i.2⟩, Subtype.ext hj⟩
    · have hmem := (Finset.mem_filter.mp hj).2
      simp only [hv, dif_pos hmem]
      rw [hval j]
      ring

/-- **The constraints of the recursion hold for a realised tuple.** -/
theorem cons_tuple (t : Fin K → (Fin N → ℕ)) (hk : (pivs t).card = K) (hpat : pattern t = E)
    (hrun : runList t = l) (hsum : l.sum = K) (hpos : ∀ a ∈ l, 1 ≤ a) (hK : 0 < K)
    {smax : ℕ} (hsm : ∀ j, (pivSlot t hk j : ℕ) ≤ smax) (tl : (Fin N → ℕ) → ℕ) :
    ConsM E l smax K (fun j => (pivSlot t hk j : ℕ))
      (fun i => (fun n => if n ∈ pivSet t then 0 else t i n, tl (t i))) := by
  have hmono := pivSlot_strictMono t hk
  refine ⟨fun a b hab => hmono hab, fun j => ⟨(pivSlot t hk j).isLt, hsm j⟩,
    fun y g hg => ?_, fun j hj1 hj2 => ?_⟩
  · simp only at hg
    have hgp : g ∉ pivSet t := by intro h; rw [if_pos h] at hg; exact hg rfl
    rw [if_neg hgp] at hg
    have hgS : g ∈ colSupp t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hg⟩
    have hfree : ∀ i, pivSlot t hk i ≠ g := fun i h =>
      hgp ((mem_pivSet t hk g).mpr ⟨i, h⟩)
    have hnb := not_between_run t hk hrun hsum hgS hfree
    -- (C5)
    have h5 : ∀ j j' : Fin K, runNum l j = runNum l j' →
        ¬ ((pivSlot t hk j : ℕ) ≤ g ∧ (g : ℕ) ≤ pivSlot t hk j') := by
      intro j j' hjj ⟨h1, h2⟩
      have h1' : pivSlot t hk j < g := lt_of_le_of_ne (Fin.le_def.mpr h1) (hfree j)
      have h2' : g < pivSlot t hk j' := lt_of_le_of_ne (Fin.le_def.mpr h2) (hfree j').symm
      have hjj' : j < j' := hmono.lt_iff_lt.mp (h1'.trans h2')
      have := hnb ((j' : ℕ) - j) j (by omega) (by
        rw [show (j : ℕ) + ((j' : ℕ) - j) = j' by omega]; exact hjj)
      apply this
      refine ⟨h1', ?_⟩
      convert h2' using 2
      exact Fin.ext (by simp; omega)
    refine ⟨fun hK' => ?_, fun j j' hjj => h5 j j' hjj, ?_⟩
    · -- (C4)
      set rf := runFirst l (K - 1) with hrf
      have hrfK : rf < K := lt_of_le_of_lt (runFirst_le l (K - 1)) (by omega)
      have hlast := le_pivSlot_last t hk hK hgS
      by_contra hge
      push_neg at hge
      have hrun' := (runNum_eq_of_between l (j := K - 1) (j' := rf) le_rfl
        (runFirst_le l (K - 1))).1
      exact h5 ⟨rf, hrfK⟩ ⟨K - 1, by omega⟩ hrun' ⟨hge, hlast⟩
    · -- (C6)
      have := free_col_span t hk hpat hgS hgp
      convert this using 1
      funext y'
      simp [colC, hgp]
  · -- (C7)
    have hpred := runNum_pred_of_first l (j := j) (by rw [hsum]; exact j.isLt) hj1 hj2 hpos
    have hns : ¬ runNum l ((j : ℕ) - 1) = runNum l j := by omega
    rw [sameRun_iff t hk hrun hsum hj1 j.isLt] at hns
    push_neg at hns
    obtain ⟨g, hgS, hg1, hg2⟩ := hns
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hgS).2
    have hgp : g ∉ pivSet t := by
      intro h
      obtain ⟨i, rfl⟩ := (mem_pivSet t hk g).mp h
      have a1 := hmono.lt_iff_lt.mp hg1
      have a2 := hmono.lt_iff_lt.mp hg2
      have := Fin.lt_def.mp a1
      have := Fin.lt_def.mp a2
      simp at *
      omega
    refine ⟨y, g, ?_, hg1, hg2⟩
    simp only [if_neg hgp]
    exact hy

end RankFull.Config
