module

public import RequestProject.BSCert.StageRows

/-!
# The join list of the cover rows, and `s_R ≤ |R|` (proof of Proposition 6.19)

For a rank-full exponent matrix `E` (rows = `B'`, columns in decision order, latest first), a
cover `C` and a row order `rk` with the rows of `C` first, the stage rows are
`C_t = R≤t \ R≤(t-1)` (`BSCert.StageRows.rowsUpTo`, Lemma A.8). The number of rows of `C`
joining at stage `t` is `j_t = |C ∩ C_t|`, and the join list (earliest stage first, as used by
`CoverSkeletonBound`) is `joinList = [j_T, …, j_1]`.

* `RankFull.joinList_sum` : `∑_t j_t = |C|` (`R≤0 = ∅`, `R≤T = B'`);
* `RankFull.joinList_count_zero_le` : **`s_R ≤ |R|`**: the number of stages at which no row of
  `C` joins is at most `|R| = r - |C|`. (Every stage adds `|P_t| ≥ 1` rows, the runs being
  non-empty; at a stage with `j_t = 0` they are rows of `R`, and different stages add different
  rows.)

These are the two facts about the join list assumed in `CoverSkeletonBound` /
`typeUnionBound_of_cover`.
-/

@[expose] public section

open Finset BSCert.StageRows

namespace RankFull

variable {K : Type*} [Field K] {r m : ℕ}

/-- Every pivot is preceded (weakly) by the start of its run. -/
lemma exists_runStart_le (E : Matrix (Fin r) (Fin m) K) :
    ∀ p : Fin m, IsPivot E p → ∃ q ≤ p, RunStart E q := by
  suffices h : ∀ n : ℕ, ∀ p : Fin m, (p : ℕ) = n → IsPivot E p → ∃ q ≤ p, RunStart E q from
    fun p => h p p rfl
  intro n
  induction n with
  | zero =>
    intro p hp0 hp
    exact ⟨p, le_rfl, hp, fun q hq => by omega⟩
  | succ n ih =>
    intro p hpn hp
    have hn : n < m := by have := p.2; omega
    by_cases hi : IsPivot E ⟨n, hn⟩
    · obtain ⟨q, hq, hqs⟩ := ih ⟨n, hn⟩ rfl hi
      exact ⟨q, hq.trans (by rw [Fin.le_def]; simp; omega), hqs⟩
    · refine ⟨p, le_rfl, hp, fun q hq => ?_⟩
      have : q = ⟨n, hn⟩ := by ext; simp; omega
      rw [this]; exact hi

/-- Pivots have stage `≥ 1`. -/
lemma one_le_stageOf_of_pivot (E : Matrix (Fin r) (Fin m) K) {p : Fin m} (hp : IsPivot E p) :
    1 ≤ stageOf E p := by
  classical
  obtain ⟨q, hq, hqs⟩ := exists_runStart_le E p hp
  unfold stageOf
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hqs⟩⟩

/-- In a finite linear order, every count `1 ≤ t ≤ |s|` is attained as `#{y ∈ s : y ≤ x}`. -/
lemma exists_count_eq {α : Type*} [LinearOrder α] (s : Finset α) :
    ∀ t, 1 ≤ t → t ≤ s.card → ∃ x ∈ s, (s.filter (· ≤ x)).card = t := by
  classical
  induction s using Finset.induction_on_max with
  | h0 => intro t h1 h2; simp at h2; omega
  | step a s ha ih =>
    intro t h1 h2
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.card_insert_of_notMem has] at h2
    rcases Nat.lt_or_ge t (s.card + 1) with h | h
    · obtain ⟨x, hx, hxc⟩ := ih t h1 (by omega)
      refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
      rw [Finset.filter_insert, if_neg (not_le.mpr (ha x hx)), hxc]
    · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.filter_insert, if_pos le_rfl, Finset.card_insert_of_notMem
        (fun h => has (Finset.mem_filter.mp h).1), Finset.filter_true_of_mem
        (fun y hy => (ha y hy).le)]
      omega

/-- Every stage `1 ≤ t ≤ T` has a pivot of stage exactly `t` (a run start). -/
lemma exists_pivot_of_stage (E : Matrix (Fin r) (Fin m) K) {t : ℕ} (h1 : 1 ≤ t)
    (hT : t ≤ numRuns E) : ∃ p, IsPivot E p ∧ stageOf E p = t := by
  classical
  obtain ⟨p, hp, hpc⟩ := exists_count_eq (Finset.univ.filter (fun q => RunStart E q)) t h1 hT
  refine ⟨p, (Finset.mem_filter.mp hp).2.1, ?_⟩
  unfold stageOf
  rw [← hpc, Finset.filter_filter]
  congr 1
  ext q; simp [and_comm]

/-- `R≤0 = ∅`. -/
lemma rowsUpTo_zero (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) : rowsUpTo E rk 0 = ∅ := by
  have h := card_stageRows E (D := upTo E 0) hrk
  have hp : pivUpTo E 0 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have := (mem_pivotsIn.mp hp)
    have h1 := one_le_stageOf_of_pivot E this.2
    have h2 : stageOf E p ≤ 0 := this.1
    omega
  rw [← Finset.card_eq_zero]
  unfold rowsUpTo
  rw [h]
  exact Finset.card_eq_zero.mpr hp

/-- `P≤(t-1) ⊊ P≤t` for `1 ≤ t ≤ T`, hence the stage rows of stage `t` are non-empty. -/
lemma stage_rows_nonempty (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) {t : ℕ} (h1 : 1 ≤ t) (hT : t ≤ numRuns E) :
    (rowsUpTo E rk t \ rowsUpTo E rk (t - 1)).Nonempty := by
  classical
  obtain ⟨p, hp, hps⟩ := exists_pivot_of_stage E h1 hT
  have hmono : pivUpTo E (t - 1) ⊆ pivUpTo E t := fun q hq => by
    have := mem_pivotsIn.mp hq
    exact mem_pivotsIn.mpr ⟨upTo_mono E (by omega) this.1, this.2⟩
  have hpt : p ∈ pivUpTo E t := mem_pivotsIn.mpr ⟨by show stageOf E p ≤ t; omega, hp⟩
  have hpt' : p ∉ pivUpTo E (t - 1) := fun h => by
    have := (mem_pivotsIn.mp h).1
    have : stageOf E p ≤ t - 1 := this
    omega
  have hlt : (pivUpTo E (t - 1)).card < (pivUpTo E t).card :=
    Finset.card_lt_card ⟨hmono, fun h => hpt' (h hpt)⟩
  have hc1 := card_stageRows E (D := upTo E t) hrk
  have hc0 := card_stageRows E (D := upTo E (t - 1)) hrk
  have hsub : rowsUpTo E rk (t - 1) ⊆ rowsUpTo E rk t :=
    stageRows_mono E rk (upTo_mono E (by omega))
  rw [Finset.sdiff_nonempty]
  intro h
  have : (rowsUpTo E rk t).card ≤ (rowsUpTo E rk (t - 1)).card := Finset.card_le_card h
  unfold rowsUpTo at this
  rw [hc1, hc0] at this
  exact absurd this (not_le.mpr hlt)

/-- `j_t = |C ∩ (R≤t \ R≤(t-1))|`. -/
noncomputable def joinCount (E : Matrix (Fin r) (Fin m) K) (rk : Fin r → ℕ) (C : Finset (Fin r))
    (t : ℕ) : ℕ := by
  classical exact (C ∩ (rowsUpTo E rk t \ rowsUpTo E rk (t - 1))).card

/-- The join list `[j_T, …, j_1]` (earliest stage first). -/
noncomputable def joinList (E : Matrix (Fin r) (Fin m) K) (rk : Fin r → ℕ) (C : Finset (Fin r)) :
    List ℕ :=
  (List.range (numRuns E)).reverse.map fun i => joinCount E rk C (i + 1)

lemma list_sum_map_range_reverse (f : ℕ → ℕ) : ∀ T,
    ((List.range T).reverse.map f).sum = ∑ i ∈ range T, f i
  | 0 => rfl
  | T + 1 => by
    rw [List.range_succ, List.reverse_append, List.map_append, List.sum_append,
      list_sum_map_range_reverse f T, Finset.sum_range_succ]
    simp [add_comm]

lemma list_count_map_range_reverse (f : ℕ → ℕ) : ∀ T,
    ((List.range T).reverse.map f).count 0 = ((range T).filter (fun i => f i = 0)).card
  | 0 => rfl
  | T + 1 => by
    rw [List.range_succ, List.reverse_append, List.map_append, List.count_append,
      list_count_map_range_reverse f T, Finset.range_add_one, Finset.filter_insert]
    by_cases h : f T = 0
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h, add_comm]
    · rw [if_neg h]; simp [h]

/-- **`∑_t j_t = |C|`.** -/
theorem joinList_sum (E : Matrix (Fin r) (Fin m) K) (hE : LinearIndependent K E.row)
    (C : Finset (Fin r)) (hcov : ∀ j, (∃ i, E i j ≠ 0) → ∃ y ∈ C, E y j ≠ 0)
    {rk : Fin r → ℕ} (hrk : Function.Injective rk) (hCfirst : ∀ y ∈ C, ∀ w ∉ C, rk y < rk w) :
    (joinList E rk C).sum = C.card := by
  classical
  obtain ⟨⟨hnest, htop⟩, -, -⟩ := lemmaA8 E hE C hcov hrk hCfirst
  unfold joinList
  rw [list_sum_map_range_reverse]
  have key : ∀ T, ∑ i ∈ range T, joinCount E rk C (i + 1) = (C ∩ rowsUpTo E rk T).card := by
    intro T
    induction T with
    | zero => simp [rowsUpTo_zero E hrk]
    | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      unfold joinCount
      simp only [Nat.add_sub_cancel]
      have hsub := hnest T (T + 1) (by omega)
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro (⟨hy1, hy2⟩ | ⟨hy1, hy2, -⟩)
          · exact ⟨hy1, hsub hy2⟩
          · exact ⟨hy1, hy2⟩
        · rintro ⟨hy1, hy2⟩
          by_cases h : y ∈ rowsUpTo E rk T
          · exact Or.inl ⟨hy1, h⟩
          · exact Or.inr ⟨hy1, hy2, h⟩
      · rw [Finset.disjoint_left]
        intro y hy hy'
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy').2).2 (Finset.mem_inter.mp hy).2
  rw [key, htop, Finset.inter_univ]

/-- **`s_R ≤ |R|`**: the number of stages at which no row of `C` joins is at most `r - |C|`. -/
theorem joinList_count_zero_le (E : Matrix (Fin r) (Fin m) K) (hE : LinearIndependent K E.row)
    (C : Finset (Fin r)) (hcov : ∀ j, (∃ i, E i j ≠ 0) → ∃ y ∈ C, E y j ≠ 0)
    {rk : Fin r → ℕ} (hrk : Function.Injective rk) (hCfirst : ∀ y ∈ C, ∀ w ∉ C, rk y < rk w) :
    (joinList E rk C).count 0 ≤ r - C.card := by
  classical
  obtain ⟨⟨hnest, -⟩, -, -⟩ := lemmaA8 E hE C hcov hrk hCfirst
  unfold joinList
  rw [list_count_map_range_reverse]
  set Z := (range (numRuns E)).filter fun i => joinCount E rk C (i + 1) = 0
  set Dt : ℕ → Finset (Fin r) := fun i => rowsUpTo E rk (i + 1) \ rowsUpTo E rk i
  have hsub : Z.biUnion Dt ⊆ univ \ C := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
    have h0 := (Finset.mem_filter.mp hi).2
    unfold joinCount at h0
    simp only [Nat.add_sub_cancel] at h0
    rw [Finset.card_eq_zero] at h0
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hyC => ?_⟩
    have : y ∈ C ∩ (rowsUpTo E rk (i + 1) \ rowsUpTo E rk i) := Finset.mem_inter.mpr ⟨hyC, hyi⟩
    rw [h0] at this; simp at this
  have hdisj : (Z : Set ℕ).PairwiseDisjoint Dt := by
    intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro y hy hy'
    rcases Nat.lt_or_gt_of_ne hii' with h | h
    · exact (Finset.mem_sdiff.mp hy').2 (hnest (i + 1) i' (by omega) (Finset.mem_sdiff.mp hy).1)
    · exact (Finset.mem_sdiff.mp hy).2 (hnest (i' + 1) i (by omega) (Finset.mem_sdiff.mp hy').1)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  have hge : Z.card ≤ ∑ i ∈ Z, (Dt i).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiT : i + 1 ≤ numRuns E := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega
    have := stage_rows_nonempty E hrk (t := i + 1) (by omega) hiT
    simp only [Nat.add_sub_cancel] at this
    exact Finset.card_pos.mpr this
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    at hcard
  omega

end RankFull
