module

public import RequestProject.Beurling.RankFull.CoverBase

/-!
# Lemma A.8 for a cover: the stage rows with the rows of the cover first

For the pivot pattern `E` (columns earliest first, invertible) and a set `Cd` of rows (the cover
`C`), `SR E Cd p` is the lexicographically first basis, with the rows of `Cd` listed first, of
the rows of `E` restricted to the pivot columns `≥ p` (the pivots of the runs already processed).

* `SR_card` : `|SR p| = K - p` (Lemma A.8 (2));
* `SR_mono` : the stage rows are nested (Lemma A.8 (1));
* `SR_det` : a column in the span of the pivot columns `≥ p` is determined by its entries in the
  stage rows;
* `SR_cover` : such a column with a non-zero entry in a row of `Cd` has one in a row of
  `Cd ∩ SR p` (Lemma A.8 (3));
* `joinC` : the join list of the cover (`j_t = |C ∩ R≤t| - |C ∩ R<t|`), with
  `∑ joinC = |C|`, `#{t : j_t = 0} ≤ |R|`, and `∑_{t' ≥ t} j_{t'} = |C ∩ R≤t|`.
-/

@[expose] public section

open Finset Submodule
open scoped Classical

namespace RankFull

variable {K : ℕ}

/-- The order with the rows of `Cd` first. -/
def rkC (Cd : Finset (Fin K)) (y : Fin K) : ℕ := if y ∈ Cd then (y : ℕ) else K + y

lemma rkC_injective (Cd : Finset (Fin K)) : Function.Injective (rkC Cd) := by
  intro a b h
  unfold rkC at h
  have ha' := a.isLt
  have hb' := b.isLt
  by_cases ha : a ∈ Cd <;> by_cases hb : b ∈ Cd <;>
    simp only [ha, hb, if_true, if_false] at h <;> exact Fin.ext (by omega)

lemma rkC_first {Cd : Finset (Fin K)} {y w : Fin K} (hy : y ∈ Cd) (hw : w ∉ Cd) :
    rkC Cd y < rkC Cd w := by
  unfold rkC; rw [if_pos hy, if_neg hw]; have := y.isLt; omega

/-- The rows restricted to the pivot columns `≥ p`. -/
def rowsGe (E : Matrix (Fin K) (Fin K) ℕ) (p : ℕ) (y : Fin K) :
    {j : Fin K // p ≤ (j : ℕ)} → ℝ := fun j => (E y j : ℝ)

/-- The stage rows for the pivot columns `≥ p`, the rows of `Cd` first. -/
noncomputable def SR (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (p : ℕ) :
    Finset (Fin K) :=
  BSCert.StageRows.lexBasis (K := ℝ) (rowsGe E p) (rkC Cd)

lemma cols_li (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (p : ℕ) :
    LinearIndependent ℝ (Matrix.of fun (y : Fin K) (j : {j : Fin K // p ≤ (j : ℕ)}) =>
      (E y j : ℝ)).col := by
  have hcols : LinearIndependent ℝ (Ereal E).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hE))
  have := hcols.comp (Subtype.val : {j : Fin K // p ≤ (j : ℕ)} → Fin K) Subtype.val_injective
  convert! this using 1

theorem SR_card (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (Cd : Finset (Fin K))
    (p : ℕ) : (SR E Cd p).card = K - p := by
  unfold SR
  rw [BSCert.StageRows.card_lexBasis _ _ (rkC_injective Cd)]
  set M : Matrix (Fin K) {j : Fin K // p ≤ (j : ℕ)} ℝ := Matrix.of fun y j => (E y j : ℝ)
  have h1 : Module.finrank ℝ (span ℝ (Set.range (rowsGe E p))) = M.rank := by
    rw [Matrix.rank_eq_finrank_span_row]; rfl
  rw [h1, Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card (cols_li E hE p),
    Config.card_ge]

theorem SR_mono (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) {p p' : ℕ}
    (h : p' ≤ p) : SR E Cd p ⊆ SR E Cd p' := by
  intro y hy
  unfold SR at hy ⊢
  rw [BSCert.StageRows.mem_lexBasis] at hy ⊢
  intro hmem
  apply hy
  -- restrict from the columns `≥ p'` to the columns `≥ p`
  let ρ : ({j : Fin K // p' ≤ (j : ℕ)} → ℝ) →ₗ[ℝ] ({j : Fin K // p ≤ (j : ℕ)} → ℝ) :=
    { toFun := fun u j => u ⟨j, le_trans h j.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ : ∀ w, ρ (rowsGe E p' w) = rowsGe E p w := fun w => rfl
  have := Submodule.mem_map_of_mem (f := ρ) hmem
  rw [Submodule.map_span, ← Set.image_comp] at this
  rw [hρ] at this
  simpa [Function.comp_def, hρ] using this

theorem SR_cover (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (p : ℕ)
    {w : Fin K → ℕ} (hw : w ∈ Config.SpanSet E {j | p ≤ (j : ℕ)})
    (hnz : ∃ y ∈ Cd, w y ≠ 0) : ∃ y ∈ Cd ∩ SR E Cd p, w y ≠ 0 := by
  obtain ⟨v, hv0, hv⟩ := hw
  obtain ⟨y₀, hy₀C, hy₀⟩ := hnz
  let f : ({j : Fin K // p ≤ (j : ℕ)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ j, u j * v j
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hf : ∀ y, f (rowsGe E p y) = (w y : ℝ) := by
    intro y
    rw [hv y]
    show ∑ j : {j : Fin K // p ≤ (j : ℕ)}, (E y j : ℝ) * v j = _
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin K => p ≤ (j : ℕ))]
    have h0 : ∑ j ∈ univ.filter (fun j : Fin K => ¬ p ≤ (j : ℕ)), (E y j : ℝ) * v j = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [hv0 j (by simpa using (Finset.mem_filter.mp hj).2), mul_zero]
    rw [h0, add_zero]
    exact (Finset.sum_subtype _ (fun j => by simp) (fun j => (E y j : ℝ) * v j)).symm
  by_contra hcon
  push_neg at hcon
  by_cases hyR : y₀ ∈ SR E Cd p
  · exact hy₀ (hcon y₀ (Finset.mem_inter.mpr ⟨hy₀C, hyR⟩))
  · have hmem := BSCert.StageRows.mem_span_lexBasis_lt (K := ℝ) (rowsGe E p) (rkC Cd) hyR
    have hle : span ℝ ((rowsGe E p) '' {u | u ∈ SR E Cd p ∧ rkC Cd u < rkC Cd y₀}) ≤
        LinearMap.ker f := by
      refine span_le.mpr ?_
      rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
      have huC : u ∈ Cd := by
        by_contra huC
        exact absurd (rkC_first hy₀C huC) (by omega)
      show f (rowsGe E p u) = 0
      rw [hf]; exact_mod_cast hcon u (Finset.mem_inter.mpr ⟨huC, hu1⟩)
    have := hle hmem
    rw [LinearMap.mem_ker, hf] at this
    exact hy₀ (by exact_mod_cast this)

theorem SR_det (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (Cd : Finset (Fin K))
    (p : ℕ) {w w' : Fin K → ℕ} (hw : w ∈ Config.SpanSet E {j | p ≤ (j : ℕ)})
    (hw' : w' ∈ Config.SpanSet E {j | p ≤ (j : ℕ)}) (hR : ∀ y ∈ SR E Cd p, w y = w' y) :
    w = w' := by
  obtain ⟨v, hv0, hv⟩ := hw
  obtain ⟨v', hv0', hv'⟩ := hw'
  set M : Matrix (Fin K) {j : Fin K // p ≤ (j : ℕ)} ℝ := Matrix.of fun y j => (E y j : ℝ)
  set β : {j : Fin K // p ≤ (j : ℕ)} → ℝ := fun j => v j - v' j
  let f : ({j : Fin K // p ≤ (j : ℕ)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ j, u j * β j
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hsplit : ∀ (u : Fin K → ℝ), (∀ j, j ∉ {j : Fin K | p ≤ (j : ℕ)} → u j = 0) → ∀ y,
      ∑ j, (E y j : ℝ) * u j = ∑ j : {j : Fin K // p ≤ (j : ℕ)}, (E y j : ℝ) * u j := by
    intro u hu y
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin K => p ≤ (j : ℕ))]
    have h0 : ∑ j ∈ univ.filter (fun j : Fin K => ¬ p ≤ (j : ℕ)), (E y j : ℝ) * u j = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [hu j (by simpa using (Finset.mem_filter.mp hj).2), mul_zero]
    rw [h0, add_zero]
    exact Finset.sum_subtype _ (fun j => by simp) (fun j => (E y j : ℝ) * u j)
  have hf : ∀ y, f (rowsGe E p y) = (w y : ℝ) - w' y := by
    intro y
    rw [hv y, hv' y, hsplit v hv0 y, hsplit v' hv0' y, ← Finset.sum_sub_distrib]
    show ∑ j : {j : Fin K // p ≤ (j : ℕ)}, rowsGe E p y j * β j = _
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [β, rowsGe]; ring
  have hspan : ∀ u ∈ span ℝ (Set.range (rowsGe E p)), f u = 0 := by
    intro u hu
    rw [← BSCert.StageRows.span_lexBasis (K := ℝ) (rowsGe E p) (rkC Cd)] at hu
    refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by
      rw [map_add, ha, hb, add_zero]) (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hu
    rintro _ ⟨y, hy, rfl⟩
    rw [hf]; have := hR y hy; rw [this]; ring
  have hβ : β = 0 := by
    have hli := cols_li E hE p
    rw [Fintype.linearIndependent_iff] at hli
    refine funext fun j => hli β ?_ j
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul, Pi.zero_apply,
      Matrix.of_apply]
    have := hspan (rowsGe E p y) (Submodule.subset_span ⟨y, rfl⟩)
    rw [← this]
    show ∑ j : {j : Fin K // p ≤ (j : ℕ)}, β j * (E y j : ℝ) =
      ∑ j : {j : Fin K // p ≤ (j : ℕ)}, rowsGe E p y j * β j
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hvv : ∀ j, v j = v' j := by
    intro j
    by_cases hj : p ≤ (j : ℕ)
    · have := congrFun hβ ⟨j, hj⟩; simp [β] at this; linarith
    · rw [hv0 j hj, hv0' j hj]
  funext y
  have : (w y : ℝ) = w' y := by rw [hv, hv']; simp_rw [hvv]
  exact_mod_cast this

/-! ## The join list of the cover -/

/-- `K_t`: the number of rows of the cover among the stage rows for the pivots `≥ p`. -/
noncomputable def Kc (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (p : ℕ) : ℕ :=
  (SR E Cd p ∩ Cd).card

/-- The number of stage rows outside the cover. -/
noncomputable def Dc (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (p : ℕ) : ℕ :=
  (SR E Cd p \ Cd).card

/-- The join list, run by run (one entry per run, earliest run first). -/
noncomputable def joinAux (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) :
    List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: l, s => (Kc E Cd s - Kc E Cd (s + a)) :: joinAux E Cd l (s + a)

/-- **The join list of the cover** for the run structure `l`. -/
noncomputable def joinC (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (l : List ℕ) :
    List ℕ := joinAux E Cd l 0

lemma Kc_anti (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) {p p' : ℕ} (h : p ≤ p') :
    Kc E Cd p' ≤ Kc E Cd p :=
  Finset.card_le_card (Finset.inter_subset_inter_right (SR_mono E Cd h))

lemma Dc_anti (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) {p p' : ℕ} (h : p ≤ p') :
    Dc E Cd p' ≤ Dc E Cd p :=
  Finset.card_le_card (Finset.sdiff_subset_sdiff (SR_mono E Cd h) (Finset.Subset.refl _))

lemma Kc_add_Dc (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (p : ℕ) :
    Kc E Cd p + Dc E Cd p = (SR E Cd p).card := by
  unfold Kc Dc
  rw [Finset.card_inter_add_card_sdiff]

lemma joinAux_length (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) :
    ∀ (l : List ℕ) (s : ℕ), (joinAux E Cd l s).length = l.length
  | [], _ => rfl
  | a :: l, s => by simp [joinAux, joinAux_length E Cd l]

lemma joinAux_drop_sum (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) :
    ∀ (l : List ℕ) (s i : ℕ), i ≤ l.length →
      ((joinAux E Cd l s).drop i).sum + Kc E Cd (s + l.sum) = Kc E Cd (s + (l.take i).sum)
  | [], s, i, _ => by simp [joinAux]
  | a :: l, s, i, hi => by
    rcases i with _ | i
    · simp only [joinAux, List.drop_zero, List.sum_cons, List.take_zero, List.sum_nil, add_zero]
      have h1 := joinAux_drop_sum E Cd l (s + a) 0 (Nat.zero_le _)
      simp only [List.drop_zero, List.take_zero, List.sum_nil, add_zero] at h1
      have h2 := Kc_anti E Cd (show s ≤ s + a by omega)
      rw [show s + (a + l.sum) = s + a + l.sum by ring]
      omega
    · simp only [joinAux, List.drop_succ_cons, List.take_succ_cons, List.sum_cons,
        List.length_cons] at hi ⊢
      have := joinAux_drop_sum E Cd l (s + a) i (by omega)
      rw [show s + (a + l.sum) = s + a + l.sum by ring,
        show s + (a + (l.take i).sum) = s + a + (l.take i).sum by ring]
      exact this

lemma joinAux_count (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0)
    (Cd : Finset (Fin K)) : ∀ (l : List ℕ) (s : ℕ), (∀ a ∈ l, 1 ≤ a) → s + l.sum ≤ K →
      (joinAux E Cd l s).count 0 + Dc E Cd (s + l.sum) ≤ Dc E Cd s
  | [], s, _, _ => by simp [joinAux]
  | a :: l, s, hpos, hs => by
    have ha := hpos a (by simp)
    simp only [List.sum_cons] at hs
    have ih := joinAux_count E hE Cd l (s + a) (fun b hb => hpos b (by simp [hb])) (by omega)
    have hcs := SR_card E hE Cd s
    have hcs' := SR_card E hE Cd (s + a)
    have h1 := Kc_add_Dc E Cd s
    have h2 := Kc_add_Dc E Cd (s + a)
    have hK := Kc_anti E Cd (show s ≤ s + a by omega)
    have hD := Dc_anti E Cd (show s ≤ s + a by omega)
    simp only [joinAux, List.count_cons, List.sum_cons]
    rw [show s + (a + l.sum) = s + a + l.sum by ring]
    split_ifs with h
    · simp only [beq_iff_eq] at h
      omega
    · omega

/-- `∑ joinC = |C|`. -/
theorem joinC_sum (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (Cd : Finset (Fin K))
    (l : List ℕ) (hsum : l.sum = K) : (joinC E Cd l).sum = Cd.card := by
  have := joinAux_drop_sum E Cd l 0 0 (Nat.zero_le _)
  simp only [List.drop_zero, List.take_zero, List.sum_nil, add_zero, zero_add, hsum] at this
  have hK0 : Kc E Cd K = 0 := by
    unfold Kc
    have := SR_card E hE Cd K
    rw [Nat.sub_self, Finset.card_eq_zero] at this
    rw [this]; simp
  have hK : Kc E Cd 0 = Cd.card := by
    unfold Kc
    have h := SR_card E hE Cd 0
    have : SR E Cd 0 = univ := Finset.eq_univ_of_card _ (by rw [h]; simp)
    rw [this, Finset.univ_inter]
  unfold joinC
  rw [hK0, hK] at this
  omega

/-- `#{t : j_t = 0} ≤ |R|`. -/
theorem joinC_count (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0)
    (Cd : Finset (Fin K)) (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K) :
    (joinC E Cd l).count 0 ≤ K - Cd.card := by
  have h := joinAux_count E hE Cd l 0 hpos (by omega)
  rw [zero_add, hsum] at h
  have hD : Dc E Cd 0 = K - Cd.card := by
    unfold Dc
    have h0 := SR_card E hE Cd 0
    have : SR E Cd 0 = univ := Finset.eq_univ_of_card _ (by rw [h0]; simp)
    rw [this, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  unfold joinC
  omega

/-- `∑_{t' from run i on} j_{t'} = K_t`, the number of cover rows among the stage rows of the
pivots `≥ (l.take i).sum`. -/
theorem joinC_drop_sum (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0)
    (Cd : Finset (Fin K)) (l : List ℕ) (hsum : l.sum = K) {i : ℕ} (hi : i ≤ l.length) :
    ((joinC E Cd l).drop i).sum = Kc E Cd (l.take i).sum := by
  have := joinAux_drop_sum E Cd l 0 i hi
  simp only [zero_add, hsum] at this
  have hK0 : Kc E Cd K = 0 := by
    unfold Kc
    have := SR_card E hE Cd K
    rw [Nat.sub_self, Finset.card_eq_zero] at this
    rw [this]; simp
  unfold joinC
  rw [hK0, add_zero] at this
  exact this

lemma joinC_length (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K)) (l : List ℕ) :
    (joinC E Cd l).length = l.length := joinAux_length E Cd l 0

end RankFull
