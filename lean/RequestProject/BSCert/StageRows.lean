module

public import Mathlib

/-!
# Lemma A.8 (nested stage rows) of the paper, in general

This file proves Lemma A.8 of Appendix A for an arbitrary matrix over a field. It is the claim
that the scripts `sc_check.py`, `sc_greedy.py` and `sc_check_independent.py` test on random
integer matrices, and it gives the structural facts tested by `svl_stress.py`
(see `SVLFacts.lean`).

Conventions (as in Appendix A):
* `E : Matrix (Fin r) (Fin m) K` is the exponent matrix: rows are the elements of `B'`, columns
  are the primes **in decision order, latest first** (column `0` is the latest decided).
* Column `j` is a (greedy) *pivot* if it is not in the span of the columns decided later, i.e.
  of the columns with smaller index (`IsPivot`). `isPivot_iff_greedy` shows that this is the
  same as the paper's greedy rule (not in the span of the *pivots* decided later).
* The rows are ordered by an injective rank function `rk`; the lexicographically first basis of
  the row matroid of `E` restricted to the columns `P` is `lexBasis`.
-/

@[expose] public section

open Submodule Set

namespace BSCert.StageRows

variable {K : Type*} [Field K]

/-! ## A general linear-independence criterion -/

/-- If each vector of a finite family is outside the span of the members of smaller rank, the
family is linearly independent. -/
lemma linIndepOn_of_notMem_span {ι V : Type*} [AddCommGroup V] [Module K V] [DecidableEq ι]
    (v : ι → V) (rk : ι → ℕ) (hrk : Function.Injective rk) (S : Finset ι)
    (h : ∀ i ∈ S, v i ∉ span K (v '' {j | j ∈ S ∧ rk j < rk i})) :
    LinearIndepOn K v (S : Set ι) := by
  suffices H : ∀ s : Finset ι, s ⊆ S → LinearIndepOn K v (s : Set ι) from H S subset_rfl
  intro s
  induction s using Finset.induction_on_max_value rk with
  | h0 => intro _; simp
  | step a s ha hmax ih =>
    intro hsub
    rw [Finset.coe_insert, linearIndepOn_insert (by simpa using ha)]
    refine ⟨ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)), fun hmem => ?_⟩
    apply h a (hsub (Finset.mem_insert_self a s))
    refine span_mono ?_ hmem
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ⟨hsub (Finset.mem_insert_of_mem hx), lt_of_le_of_ne (hmax x hx) ?_⟩, rfl⟩
    intro e
    exact ha (hrk e ▸ hx)

/-! ## The lexicographically first basis -/

section LexBasis

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]

open Classical in
/-- The lexicographically first basis of the family `v` for the order given by `rk`: a member
is taken iff it is not in the span of the members listed before it. -/
noncomputable def lexBasis (v : ι → V) (rk : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun y => v y ∉ span K (v '' {w | rk w < rk y}))

omit [DecidableEq ι] in
lemma mem_lexBasis {v : ι → V} {rk : ι → ℕ} {y : ι} :
    y ∈ lexBasis (K := K) v rk ↔ v y ∉ span K (v '' {w | rk w < rk y}) := by
  classical
  simp [lexBasis]

/-- Every member is in the span of the basis members listed no later than it. -/
lemma mem_span_lexBasis_le (v : ι → V) (rk : ι → ℕ) (y : ι) :
    v y ∈ span K (v '' {w | w ∈ lexBasis (K := K) v rk ∧ rk w ≤ rk y}) := by
  induction hn : rk y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    by_cases hy : y ∈ lexBasis (K := K) v rk
    · exact subset_span ⟨y, ⟨hy, hn.le⟩, rfl⟩
    · rw [mem_lexBasis, not_not] at hy
      refine span_le.mpr ?_ hy
      rintro _ ⟨w, hw, rfl⟩
      have hw' : rk w < n := hn ▸ hw
      refine span_mono ?_ (ih (rk w) hw' w rfl)
      rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
      exact ⟨u, ⟨hu1, by omega⟩, rfl⟩

/-- A member outside the basis is in the span of the basis members listed before it. -/
lemma mem_span_lexBasis_lt (v : ι → V) (rk : ι → ℕ) {y : ι}
    (hy : y ∉ lexBasis (K := K) v rk) :
    v y ∈ span K (v '' {w | w ∈ lexBasis (K := K) v rk ∧ rk w < rk y}) := by
  rw [mem_lexBasis, not_not] at hy
  refine span_le.mpr ?_ hy
  rintro _ ⟨w, hw, rfl⟩
  refine span_mono ?_ (mem_span_lexBasis_le v rk w)
  rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
  exact ⟨u, ⟨hu1, lt_of_le_of_lt hu2 hw⟩, rfl⟩

lemma lexBasis_linIndepOn (v : ι → V) (rk : ι → ℕ) (hrk : Function.Injective rk) :
    LinearIndepOn K v (lexBasis (K := K) v rk : Set ι) := by
  refine linIndepOn_of_notMem_span v rk hrk _ (fun i hi hmem => ?_)
  rw [mem_lexBasis] at hi
  exact hi (span_mono (by rintro _ ⟨x, ⟨_, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩) hmem)

lemma span_lexBasis (v : ι → V) (rk : ι → ℕ) :
    span K (v '' (lexBasis (K := K) v rk : Set ι)) = span K (range v) := by
  apply le_antisymm
  · exact span_mono (image_subset_range _ _)
  · refine span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    refine span_mono ?_ (mem_span_lexBasis_le (K := K) v rk y)
    rintro _ ⟨u, ⟨hu, _⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

lemma card_lexBasis (v : ι → V) (rk : ι → ℕ) (hrk : Function.Injective rk) :
    (lexBasis (K := K) v rk).card = Module.finrank K (span K (range v)) := by
  have hli := lexBasis_linIndepOn (K := K) v rk hrk
  have := finrank_span_eq_card (R := K) (b := fun y : (lexBasis (K := K) v rk) => v y) hli
  rw [← span_lexBasis (K := K) v rk]
  have hr : range (fun y : (lexBasis (K := K) v rk) => v y) =
      v '' (lexBasis (K := K) v rk : Set ι) := by
    ext x; simp
  rw [hr] at this
  rw [this]
  simp

end LexBasis

/-! ## Greedy pivots -/

variable {r m : ℕ}

/-- Column `j` is a pivot: it is not in the span of the columns decided later (smaller
index). -/
def IsPivot (E : Matrix (Fin r) (Fin m) K) (j : Fin m) : Prop :=
  E.col j ∉ span K (E.col '' {q | q < j})

/-- Every column is in the span of the pivot columns decided no earlier than it. -/
lemma col_mem_span_pivots (E : Matrix (Fin r) (Fin m) K) (q : Fin m) :
    E.col q ∈ span K (E.col '' {p | p ≤ q ∧ IsPivot E p}) := by
  induction q using WellFoundedLT.induction with
  | _ q ih =>
    by_cases hq : IsPivot E q
    · exact subset_span ⟨q, ⟨le_rfl, hq⟩, rfl⟩
    · unfold IsPivot at hq
      rw [not_not] at hq
      refine span_le.mpr ?_ hq
      rintro _ ⟨q', hq', rfl⟩
      refine span_mono ?_ (ih q' hq')
      rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨p, ⟨hp1.trans (le_of_lt hq'), hp2⟩, rfl⟩

/-- The span of the columns decided later than `j` is spanned by the pivots among them. -/
lemma span_lt_eq_span_pivots (E : Matrix (Fin r) (Fin m) K) (j : Fin m) :
    span K (E.col '' {q | q < j}) = span K (E.col '' {q | q < j ∧ IsPivot E q}) := by
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    refine span_mono ?_ (col_mem_span_pivots E q)
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact ⟨p, ⟨lt_of_le_of_lt hp1 hq, hp2⟩, rfl⟩
  · exact span_mono (image_mono (fun q hq => hq.1))

/-- `IsPivot` is the paper's greedy rule: a column is a pivot iff it is not in the span of the
pivots decided later. -/
theorem isPivot_iff_greedy (E : Matrix (Fin r) (Fin m) K) (j : Fin m) :
    IsPivot E j ↔ E.col j ∉ span K (E.col '' {q | q < j ∧ IsPivot E q}) := by
  rw [IsPivot, span_lt_eq_span_pivots]

open Classical in
/-- The pivots in a set `D` of columns. -/
noncomputable def pivotsIn (E : Matrix (Fin r) (Fin m) K) (D : Set (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => j ∈ D ∧ IsPivot E j)

lemma mem_pivotsIn {E : Matrix (Fin r) (Fin m) K} {D : Set (Fin m)} {j : Fin m} :
    j ∈ pivotsIn E D ↔ j ∈ D ∧ IsPivot E j := by
  classical
  simp [pivotsIn]

/-- The pivot columns are linearly independent. -/
lemma pivots_linIndepOn (E : Matrix (Fin r) (Fin m) K) (D : Set (Fin m)) :
    LinearIndepOn K E.col (pivotsIn E D : Set (Fin m)) := by
  classical
  refine linIndepOn_of_notMem_span E.col (fun j => (j : ℕ)) Fin.val_injective _
    (fun i hi hmem => ?_)
  rw [mem_pivotsIn] at hi
  exact hi.2 (span_mono (by rintro _ ⟨x, ⟨_, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩) hmem)

/-- The rows of `E` restricted to the columns of `P`. -/
def rowsOn (E : Matrix (Fin r) (Fin m) K) (P : Finset (Fin m)) : Fin r → (P → K) :=
  fun y p => E y p

/-- The nested stage rows `R(D)`: the lexicographically first basis (for the row order `rk`) of
the row matroid of `E` restricted to the pivots in `D`. -/
noncomputable def stageRows (E : Matrix (Fin r) (Fin m) K) (rk : Fin r → ℕ)
    (D : Set (Fin m)) : Finset (Fin r) :=
  lexBasis (K := K) (rowsOn E (pivotsIn E D)) rk

/-- The rank of the rows restricted to the pivots of `D` is the number of these pivots. -/
lemma finrank_rowsOn (E : Matrix (Fin r) (Fin m) K) (D : Set (Fin m)) :
    Module.finrank K (span K (range (rowsOn E (pivotsIn E D)))) = (pivotsIn E D).card := by
  set P := pivotsIn E D
  let A : Matrix (Fin r) P K := Matrix.of fun y p => E y p
  have h1 : Module.finrank K (span K (range (rowsOn E P))) = A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]; rfl
  have hli : LinearIndependent K A.col := by
    have := (pivots_linIndepOn E D)
    exact this
  rw [h1, Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hli]
  simp

/-- **Lemma A.8 (2).** `|R(D)| = |P(D)|`. -/
theorem card_stageRows (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) (D : Set (Fin m)) :
    (stageRows E rk D).card = (pivotsIn E D).card := by
  rw [stageRows, card_lexBasis _ _ hrk, finrank_rowsOn]

/-- **Lemma A.8 (2).** `E[R(D), P(D)]` is invertible. -/
theorem stageRows_invertible (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) (D : Set (Fin m)) :
    ∃ N : Matrix (pivotsIn E D) (stageRows E rk D) K,
      (Matrix.of fun (y : stageRows E rk D) (p : pivotsIn E D) => E y p) * N = 1 ∧
      N * (Matrix.of fun (y : stageRows E rk D) (p : pivotsIn E D) => E y p) = 1 := by
  set R := stageRows E rk D
  set P := pivotsIn E D
  let M : Matrix R P K := Matrix.of fun y p => E y p
  have hcard : Fintype.card R = Fintype.card P := by
    simpa using card_stageRows E hrk D
  let e : R ≃ P := Fintype.equivOfCardEq hcard
  let M' : Matrix P P K := Matrix.of fun a b => M (e.symm a) b
  have hli : LinearIndependent K M'.row := by
    have h0 := lexBasis_linIndepOn (K := K) (rowsOn E P) rk hrk
    have h1 : LinearIndependent K (fun y : R => rowsOn E P y) := h0
    have h2 := h1.comp e.symm e.symm.injective
    exact h2
  obtain ⟨N', hN'⟩ := (Matrix.linearIndependent_rows_iff_isUnit.mp hli).exists_right_inv
  have hN'' : N' * M' = 1 := mul_eq_one_comm.mp hN'
  refine ⟨Matrix.of fun q y => N' q (e y), ?_, ?_⟩
  · ext y y'
    have := congrFun (congrFun hN' (e y)) (e y')
    simp only [Matrix.mul_apply, Matrix.of_apply, M', M, Equiv.symm_apply_apply] at this ⊢
    rw [this]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · ext q q'
    have := congrFun (congrFun hN'' q) q'
    simp only [Matrix.mul_apply, Matrix.of_apply, M', M] at this ⊢
    rw [← this]
    exact Fintype.sum_equiv e _ _ (fun y => by simp)

/-- **Lemma A.8 (1).** The stage rows are nested. -/
theorem stageRows_mono (E : Matrix (Fin r) (Fin m) K) (rk : Fin r → ℕ) {D D' : Set (Fin m)}
    (hDD' : D ⊆ D') : stageRows E rk D ⊆ stageRows E rk D' := by
  intro y hy
  rw [stageRows, mem_lexBasis] at hy ⊢
  intro hmem
  apply hy
  have hsub : pivotsIn E D ⊆ pivotsIn E D' := by
    intro j hj
    rw [mem_pivotsIn] at hj ⊢
    exact ⟨hDD' hj.1, hj.2⟩
  let π : ((pivotsIn E D') → K) →ₗ[K] ((pivotsIn E D) → K) :=
    LinearMap.funLeft K K (Set.inclusion hsub)
  have hπ : ∀ w, π (rowsOn E (pivotsIn E D') w) = rowsOn E (pivotsIn E D) w := by
    intro w; rfl
  have := Submodule.mem_map_of_mem (f := π) hmem
  rw [Submodule.map_span, ← Set.image_comp] at this
  rw [← hπ y]
  convert this using 3

/-- **Lemma A.8 (1), last part.** For a rank-full matrix (independent rows), the stage rows
of the set of all columns are all the rows. -/
theorem stageRows_univ (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) (hE : LinearIndependent K E.row) :
    stageRows E rk Set.univ = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_stageRows E hrk]
  simp only [Fintype.card_fin]
  have h1 : Module.finrank K (span K (range E.row)) = r := by
    rw [finrank_span_eq_card hE, Fintype.card_fin]
  rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_cols] at h1
  refine Eq.trans ?_ h1
  have hspan : span K (range E.col) =
      span K (E.col '' (pivotsIn E Set.univ : Set (Fin m))) := by
    apply le_antisymm
    · refine span_le.mpr ?_
      rintro _ ⟨q, rfl⟩
      refine span_mono ?_ (col_mem_span_pivots E q)
      rintro _ ⟨p, ⟨_, hp⟩, rfl⟩
      exact ⟨p, by simpa [mem_pivotsIn] using hp, rfl⟩
    · exact span_mono (image_subset_range _ _)
  rw [hspan]
  have hli := pivots_linIndepOn E Set.univ
  have := finrank_span_eq_card (R := K)
    (b := fun p : (pivotsIn E Set.univ) => E.col p) hli
  have hr : range (fun p : (pivotsIn E Set.univ) => E.col p) =
      E.col '' (pivotsIn E Set.univ : Set (Fin m)) := by
    ext x; simp
  rw [hr] at this
  rw [this]
  simp

/-- **Lemma A.8 (3).** Let `D` be a set of columns closed under passing to later-decided
columns, and let the rows of the cover `C` come first in the order `rk`. Then every non-zero
column `j ∈ D` has a non-zero entry in some row of `C ∩ R(D)`. -/
theorem stageRows_cover (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (C : Finset (Fin r)) (hCfirst : ∀ y ∈ C, ∀ w ∉ C, rk y < rk w)
    (hcov : ∀ j, (∃ i, E i j ≠ 0) → ∃ y ∈ C, E y j ≠ 0)
    {D : Set (Fin m)} (hD : ∀ j ∈ D, ∀ q ≤ j, q ∈ D)
    {j : Fin m} (hj : j ∈ D) (hj0 : ∃ i, E i j ≠ 0) :
    ∃ y ∈ C ∩ stageRows E rk D, E y j ≠ 0 := by
  classical
  set P := pivotsIn E D
  obtain ⟨y, hyC, hyj⟩ := hcov j hj0
  -- column `j` is a combination of the pivot columns in `D`
  have hcolj : E.col j ∈ span K (range (fun p : P => E.col p)) := by
    refine span_mono ?_ (col_mem_span_pivots E j)
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact ⟨⟨p, mem_pivotsIn.mpr ⟨hD j hj p hp1, hp2⟩⟩, rfl⟩
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hcolj
  have hrow : ∀ i, E i j = ∑ p : P, β p * E i p := by
    intro i
    have := congrFun hβ i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    exact this.symm
  let f : (P → K) →ₗ[K] K :=
    { toFun := fun u => ∑ p : P, β p * u p
      map_add' := by intro u u'; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring) }
  have hf : ∀ i, f (rowsOn E P i) = E i j := by
    intro i; rw [hrow i]; rfl
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ w ∈ C ∩ stageRows E rk D, f (rowsOn E P w) = 0 := by
    intro w hw; rw [hf]; exact hcon w hw
  by_cases hyR : y ∈ stageRows E rk D
  · exact hyj (hcon y (Finset.mem_inter.mpr ⟨hyC, hyR⟩))
  · have hmem := mem_span_lexBasis_lt (K := K) (rowsOn E P) rk hyR
    have hle : span K ((rowsOn E P) '' {w | w ∈ stageRows E rk D ∧ rk w < rk y}) ≤
        LinearMap.ker f := by
      refine span_le.mpr ?_
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have hwC : w ∈ C := by
        by_contra hwC
        exact absurd (hCfirst y hyC w hwC) (by omega)
      exact hzero w (Finset.mem_inter.mpr ⟨hwC, hw1⟩)
    have := hle hmem
    rw [LinearMap.mem_ker, hf] at this
    exact hyj this

/-- Column `j ∈ D` is determined by its entries in the rows `R(D)`: any combination of the
pivot columns of `D` that matches column `j` on the rows `R(D)` matches it on every row. -/
theorem col_determined (E : Matrix (Fin r) (Fin m) K) {rk : Fin r → ℕ}
    (hrk : Function.Injective rk) {D : Set (Fin m)} (hD : ∀ j ∈ D, ∀ q ≤ j, q ∈ D)
    {j : Fin m} (hj : j ∈ D) (β : pivotsIn E D → K)
    (hβ : ∀ y ∈ stageRows E rk D, E y j = ∑ p, β p * E y p) :
    ∀ i, E i j = ∑ p, β p * E i p := by
  classical
  have hcolj : E.col j ∈ span K (range (fun p : pivotsIn E D => E.col p)) := by
    refine span_mono ?_ (col_mem_span_pivots E j)
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact ⟨⟨p, mem_pivotsIn.mpr ⟨hD j hj p hp1, hp2⟩⟩, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hcolj
  have hrow : ∀ i, E i j = ∑ p : pivotsIn E D, γ p * E i p := by
    intro i
    have := congrFun hγ i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    exact this.symm
  -- on the rows `R(D)` the two coefficient vectors agree, by invertibility
  obtain ⟨N, hMN, hNM⟩ := stageRows_invertible E hrk D
  set M : Matrix (stageRows E rk D) (pivotsIn E D) K := Matrix.of fun y p => E y p
  have hMβ : M.mulVec β = M.mulVec γ := by
    ext y
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    have h1 := hβ y y.2
    have h2 := hrow y
    rw [← Finset.sum_congr rfl (fun p _ => mul_comm (β p) (E y p)),
      ← Finset.sum_congr rfl (fun p _ => mul_comm (γ p) (E y p)), ← h1, ← h2]
  have hβγ : β = γ := by
    have := congrArg (N.mulVec) hMβ
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  intro i
  rw [hβγ]
  exact hrow i

/-! ## Runs, stages and the statement of Lemma A.8 -/

/-- A pivot that starts a run: the column decided just later (index one less), if any, is not a
pivot. The runs `P₁, P₂, …` are the maximal sets of consecutive pivots, latest first. -/
def RunStart (E : Matrix (Fin r) (Fin m) K) (j : Fin m) : Prop :=
  IsPivot E j ∧ ∀ q : Fin m, (q : ℕ) + 1 = j → ¬ IsPivot E q

open Classical in
/-- The stage of a column: the number of runs that start at or before it (in decision order,
latest first). A pivot of the run `Pₜ` has stage `t`; a free column of the late block `Fₜ`
(between `Pₜ` and `Pₜ₊₁`) has stage `t`; the early block `F_T` has stage `T`. -/
noncomputable def stageOf (E : Matrix (Fin r) (Fin m) K) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun p => p ≤ j ∧ RunStart E p)).card

open Classical in
/-- The number `T` of runs. -/
noncomputable def numRuns (E : Matrix (Fin r) (Fin m) K) : ℕ :=
  (Finset.univ.filter (fun p => RunStart E p)).card

lemma stageOf_mono (E : Matrix (Fin r) (Fin m) K) {j j' : Fin m} (h : j ≤ j') :
    stageOf E j ≤ stageOf E j' := by
  classical
  unfold stageOf
  exact Finset.card_le_card (fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.trans h, hp.2⟩)

lemma stageOf_le_numRuns (E : Matrix (Fin r) (Fin m) K) (j : Fin m) :
    stageOf E j ≤ numRuns E := by
  classical
  unfold stageOf numRuns
  exact Finset.card_le_card (fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.2)

/-- The columns of the first `t` runs and blocks, `P≤t ∪ F≤t`. -/
def upTo (E : Matrix (Fin r) (Fin m) K) (t : ℕ) : Set (Fin m) := {j | stageOf E j ≤ t}

/-- `P≤t`: the pivots of the runs `P₁, …, Pₜ`. -/
noncomputable def pivUpTo (E : Matrix (Fin r) (Fin m) K) (t : ℕ) : Finset (Fin m) :=
  pivotsIn E (upTo E t)

/-- `F≤t`: the free columns of the blocks `F₁, …, Fₜ`. -/
def freeUpTo (E : Matrix (Fin r) (Fin m) K) (t : ℕ) : Set (Fin m) :=
  {j | ¬ IsPivot E j ∧ stageOf E j ≤ t}

/-- `R≤t`: the lexicographically first basis of the row matroid `Mₜ` of `E_{·,P≤t}`, for the
row order `rk`. -/
noncomputable def rowsUpTo (E : Matrix (Fin r) (Fin m) K) (rk : Fin r → ℕ) (t : ℕ) :
    Finset (Fin r) :=
  stageRows E rk (upTo E t)

lemma upTo_downClosed (E : Matrix (Fin r) (Fin m) K) (t : ℕ) :
    ∀ j ∈ upTo E t, ∀ q ≤ j, q ∈ upTo E t :=
  fun _ hj _ hq => le_trans (stageOf_mono E hq) hj

lemma upTo_mono (E : Matrix (Fin r) (Fin m) K) {t t' : ℕ} (h : t ≤ t') :
    upTo E t ⊆ upTo E t' := fun _ hj => le_trans hj h

lemma upTo_numRuns (E : Matrix (Fin r) (Fin m) K) : upTo E (numRuns E) = Set.univ :=
  Set.eq_univ_of_forall (fun j => stageOf_le_numRuns E j)

/-- **Lemma A.8 (Nested stage rows).** Let `E` be rank-full (independent rows), let `C` be a
cover (every non-zero column has a non-zero entry in a row of `C`), and order the rows by an
injective `rk` in which the rows of `C` come first. Let `R≤t` be the lexicographically first
basis of `Mₜ`. Then
1. `R≤1 ⊆ R≤2 ⊆ ⋯ ⊆ R≤T = B'`;
2. `|R≤t| = |P≤t|`, and `E_{R≤t,P≤t}` is invertible;
3. every non-zero column `j ∈ P≤t ∪ F≤t` has a non-zero entry in some row of `C ∩ R≤t`. -/
theorem lemmaA8 (E : Matrix (Fin r) (Fin m) K) (hE : LinearIndependent K E.row)
    (C : Finset (Fin r)) (hcov : ∀ j, (∃ i, E i j ≠ 0) → ∃ y ∈ C, E y j ≠ 0)
    {rk : Fin r → ℕ} (hrk : Function.Injective rk) (hCfirst : ∀ y ∈ C, ∀ w ∉ C, rk y < rk w) :
    ((∀ t t', t ≤ t' → rowsUpTo E rk t ⊆ rowsUpTo E rk t') ∧
        rowsUpTo E rk (numRuns E) = Finset.univ) ∧
      (∀ t, (rowsUpTo E rk t).card = (pivUpTo E t).card ∧
        ∃ N : Matrix (pivUpTo E t) (rowsUpTo E rk t) K,
          (Matrix.of fun (y : rowsUpTo E rk t) (p : pivUpTo E t) => E y p) * N = 1 ∧
          N * (Matrix.of fun (y : rowsUpTo E rk t) (p : pivUpTo E t) => E y p) = 1) ∧
      (∀ t j, (j ∈ pivUpTo E t ∨ j ∈ freeUpTo E t) → (∃ i, E i j ≠ 0) →
        ∃ y ∈ C ∩ rowsUpTo E rk t, E y j ≠ 0) := by
  refine ⟨⟨fun t t' h => stageRows_mono E rk (upTo_mono E h), ?_⟩,
    fun t => ⟨card_stageRows E hrk _, stageRows_invertible E hrk _⟩, ?_⟩
  · rw [rowsUpTo, upTo_numRuns]
    exact stageRows_univ E hrk hE
  · intro t j hj hj0
    have hjD : j ∈ upTo E t := by
      rcases hj with hj | hj
      · exact (mem_pivotsIn.mp hj).1
      · exact hj.2
    exact stageRows_cover E C hCfirst hcov (upTo_downClosed E t) hjD hj0

/-- The row order of Lemma A.8: the rows of `C` first, each group in index order. -/
def rkCFirst (C : Finset (Fin r)) (y : Fin r) : ℕ := if y ∈ C then y else r + y

lemma rkCFirst_injective (C : Finset (Fin r)) : Function.Injective (rkCFirst C) := by
  intro a b h
  unfold rkCFirst at h
  have ha := a.2; have hb := b.2
  split_ifs at h <;> omega

lemma rkCFirst_first (C : Finset (Fin r)) : ∀ y ∈ C, ∀ w ∉ C, rkCFirst C y < rkCFirst C w := by
  intro y hy w hw
  unfold rkCFirst
  rw [if_pos hy, if_neg hw]
  have := y.2
  omega

end BSCert.StageRows
