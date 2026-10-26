module

public import RequestProject.BSCert.StageRows

/-!
# The order of the rows matters (Remark A.9)

`sc_check_independent.py` also runs the construction of Lemma A.8 with the rows of `C` listed
**last**, and reports coverage failures (`advfail`). Remark A.9 of the paper: "if the rows of
`B' \ C` are listed first, conclusion (3) can fail". Here is an explicit instance:
```
E = | 1 1 1 |     (row y₀, the cover C = {y₀})
    | 1 1 0 |     (row y₁)
```
Column `0` is a pivot, column `1` is free (equal to column `0`) and column `2` is a pivot, so
there are two runs. With `y₁` listed first, `R≤1 = {y₁}`, which contains no row of `C`, although
column `0 ∈ P≤1` is non-zero.
-/

@[expose] public section

namespace BSCert.StageRows

/-- The example matrix. -/
def exE : Matrix (Fin 2) (Fin 3) ℚ := !![1, 1, 1; 1, 1, 0]

/-- The row order with the row outside the cover first. -/
def exRk (y : Fin 2) : ℕ := if y = 0 then 1 else 0

lemma exRk_injective : Function.Injective exRk := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [exRk]

lemma ex_isPivot0 : IsPivot exE 0 := by
  unfold IsPivot
  have : {q : Fin 3 | q < 0} = ∅ := by ext q; simp [Fin.lt_def]
  rw [this, Set.image_empty, Submodule.span_empty, Submodule.mem_bot]
  intro h
  have := congrFun h 0
  simp [exE, Matrix.col] at this

lemma ex_not_isPivot1 : ¬ IsPivot exE 1 := by
  unfold IsPivot
  rw [not_not]
  have h : exE.col 1 = exE.col 0 := by
    ext i; fin_cases i <;> simp [exE, Matrix.col]
  rw [h]
  exact Submodule.subset_span ⟨0, by simp [Fin.lt_def], rfl⟩

lemma ex_isPivot2 : IsPivot exE 2 := by
  unfold IsPivot
  -- every vector in the span of the first two columns has equal coordinates
  let f : (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun v => v 0 - v 1
      map_add' := by intro u v; simp; ring
      map_smul' := by intro c v; simp; ring }
  intro hmem
  have hle : Submodule.span ℚ (exE.col '' {q | q < 2}) ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    simp only [Set.mem_setOf_eq] at hq
    fin_cases q <;> simp_all [exE, Matrix.col, f, Fin.lt_def]
  have := hle hmem
  simp [f, exE, Matrix.col] at this

lemma ex_runStart0 : RunStart exE 0 := ⟨ex_isPivot0, fun q hq => by simp at hq⟩

lemma ex_runStart2 : RunStart exE 2 := by
  refine ⟨ex_isPivot2, fun q hq => ?_⟩
  have : q = 1 := by ext; simp at hq ⊢; omega
  rw [this]; exact ex_not_isPivot1

lemma ex_stage2 : 2 ≤ stageOf exE 2 := by
  classical
  unfold stageOf
  have hsub : ({0, 2} : Finset (Fin 3)) ⊆
      Finset.univ.filter (fun p => p ≤ 2 ∧ RunStart exE p) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp [ex_runStart0]
    · simp [ex_runStart2]
  have := Finset.card_le_card hsub
  convert this using 1

lemma ex_stage0 : stageOf exE 0 ≤ 1 := by
  classical
  unfold stageOf
  have hsub : Finset.univ.filter (fun p => p ≤ 0 ∧ RunStart exE p) ⊆ ({0} : Finset (Fin 3)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_singleton]
    exact le_antisymm hp.1 (Fin.zero_le _)
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- **Remark A.9.** With the rows outside the cover listed first, conclusion (3) of Lemma A.8
fails: for the example, `E` is rank-full, `C = {y₀}` is a cover, the row `y₁ ∉ C` comes first,
column `0` is a non-zero pivot of `P≤1`, and no row of `C ∩ R≤1` has a non-zero entry in it. -/
theorem order_matters :
    LinearIndependent ℚ exE.row ∧
    (∀ j, (∃ i, exE i j ≠ 0) → ∃ y ∈ ({0} : Finset (Fin 2)), exE y j ≠ 0) ∧
    (∀ y ∉ ({0} : Finset (Fin 2)), ∀ w ∈ ({0} : Finset (Fin 2)), exRk y < exRk w) ∧
    (0 : Fin 3) ∈ pivUpTo exE 1 ∧ (∃ i, exE i 0 ≠ 0) ∧
    ¬ ∃ y ∈ ({0} : Finset (Fin 2)) ∩ rowsUpTo exE exRk 1, exE y 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ⟨0, by simp [exE]⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    have h2 := congrFun hg 2
    simp [Fin.sum_univ_two, exE, Matrix.row] at h0 h2
    fin_cases i <;> simp <;> linarith
  · intro j _
    exact ⟨0, by simp, by fin_cases j <;> simp [exE]⟩
  · intro y hy w hw
    simp only [Finset.mem_singleton] at hy hw
    subst hw
    simp [exRk, hy]
  · rw [pivUpTo, mem_pivotsIn]
    exact ⟨ex_stage0, ex_isPivot0⟩
  · rintro ⟨y, hy, -⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hy
    obtain ⟨rfl, hyR⟩ := hy
    rw [rowsUpTo, stageRows, mem_lexBasis] at hyR
    apply hyR
    -- on the columns `P≤1` (which exclude column `2`) the two rows coincide
    have h2 : (2 : Fin 3) ∉ upTo exE 1 := by
      simp only [upTo, Set.mem_setOf_eq, not_le]
      have := ex_stage2; omega
    have heq : rowsOn exE (pivotsIn exE (upTo exE 1)) 0 =
        rowsOn exE (pivotsIn exE (upTo exE 1)) 1 := by
      ext ⟨p, hp⟩
      rw [mem_pivotsIn] at hp
      have hp2 : p ≠ 2 := fun h => h2 (h ▸ hp.1)
      simp only [rowsOn]
      fin_cases p <;> simp_all [exE]
    rw [heq]
    exact Submodule.subset_span ⟨1, by simp [exRk], rfl⟩

end BSCert.StageRows
