module

public import RequestProject.Beurling.RankFull.MultiRunC
public import RequestProject.Beurling.RankFull.MRFinal
public import RequestProject.Beurling.RankFull.ConfigReduction

/-!
# The count decomposition of `cfgSkelCount` (proof of Proposition 6.19)

For a configuration `(C, B)` with skeleton `𝔰 = (r, C', lab, ex, s4)` (`cfgSkel`), the rows of
`B` re-indexed by the matching `σ` and the pivot slots give a `CfgRep`: the pattern
`E y i = t(σ y)(p_i)`, the run list, the constraints `ConsM` of the recursion, and the
identification of the (s1)–(s4) data. The pattern and the run list are **determined by the
skeleton** (`rep_unique`): the rows of `C` carry `ex`, the rows of `R` carry the (s4) monomials
evaluated at the labels, and two consecutive pivots are in the same run iff their labels are
consecutive (`lbl_gap`).

* `RankFull.Config.list_eq_of_runNum` : a composition is determined by its run index;
* `RankFull.Config.cfg_rep` : every configuration with skeleton `𝔰` has a `CfgRep`;
* `RankFull.Config.rep_unique` : two `CfgRep`s of the same skeleton have the same labels, the
  same pattern and the same run list;
* `RankFull.Config.cfgCount_le_ZSC` : pathwise on `G_{<s_max}`, `cfgSkelCount ≤ ZSC (r-1)` (each
  configuration maps injectively to its labels and contents, its term is `≥ 1`);
* `RankFull.Config.coverSkeletonBound_all` : **`CoverSkeletonBound` for every skeleton**, with
  `l = joinC E C lr` (from `multiRunC_chain`);
* `RankFull.Config.hcov_window` : the input `hcov` of `theorem_6_23a_model` and
  `prop_6_11_window` for the window model over a jitter process.
-/

@[expose] public section

open Finset MeasureTheory RankFull.Runs BSCert.StageRows
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

/-! ## Compositions and their run index -/

lemma runNum_succ_cases (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) {j : ℕ} (hj : j + 1 < l.sum) :
    runNum l (j + 1) = runNum l j ∨ runNum l (j + 1) = runNum l j + 1 := by
  by_cases h : runFirst l (j + 1) < j + 1
  · left
    have := (runNum_pred_of_not_first l h).1
    simpa using this.symm
  · right
    have h' : runFirst l (j + 1) = j + 1 := le_antisymm (runFirst_le _ _) (not_lt.mp h)
    have := runNum_pred_of_first l hj (by omega) h' hpos
    simpa using this.symm

/-- Two compositions with the same "same run" relation have the same run index. -/
lemma runNum_eq_of_same {l l' : List ℕ} (hpos : ∀ a ∈ l, 1 ≤ a) (hpos' : ∀ a ∈ l', 1 ≤ a)
    {K : ℕ} (hsum : l.sum = K) (hsum' : l'.sum = K)
    (h : ∀ j, 1 ≤ j → j < K → (runNum l (j - 1) = runNum l j ↔
      runNum l' (j - 1) = runNum l' j)) :
    ∀ j, j < K → runNum l j = runNum l' j := by
  intro j
  induction j with
  | zero => intro _; rw [runNum_zero l hpos, runNum_zero l' hpos']
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := h (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at h2
    rcases runNum_succ_cases l hpos (j := j) (by omega) with a | a <;>
      rcases runNum_succ_cases l' hpos' (j := j) (by omega) with b | b <;> omega

/-- The run index at the last column is the last run. -/
lemma runNum_last {l : List ℕ} (hpos : ∀ a ∈ l, 1 ≤ a) {K : ℕ} (hsum : l.sum = K)
    (hK : 0 < K) : runNum l (K - 1) + 1 = l.length := by
  have h1 := runNum_lt_length l (j := K - 1) (by omega)
  have hlen : 0 < l.length := by
    rcases l with _ | ⟨a, l⟩
    · simp at hsum; omega
    · simp
  have h2 := runNum_lt_iff l (j := K - 1) (l.length - 1) (by omega)
  have h3 := List.sum_take_succ l (l.length - 1) (by omega)
  rw [show l.length - 1 + 1 = l.length by omega, List.take_length] at h3
  have h4 := hpos (l[l.length - 1]'(by omega)) (List.getElem_mem _)
  have h5 : ¬ runNum l (K - 1) < l.length - 1 := by rw [h2]; omega
  omega

lemma sum_take_le (l : List ℕ) (i : ℕ) : (l.take i).sum ≤ l.sum := by
  have := List.sum_take_add_sum_drop l i
  omega

/-- **A composition is determined by its run index.** -/
lemma list_eq_of_runNum {l l' : List ℕ} (hpos : ∀ a ∈ l, 1 ≤ a) (hpos' : ∀ a ∈ l', 1 ≤ a)
    {K : ℕ} (hsum : l.sum = K) (hsum' : l'.sum = K)
    (h : ∀ j, j < K → runNum l j = runNum l' j) : l = l' := by
  have htake : ∀ i, (l.take i).sum = (l'.take i).sum := by
    intro i
    have a1 := sum_take_le l i
    have a2 := sum_take_le l' i
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have b1 := runNum_lt_iff l (j := (l.take i).sum) i (by omega)
      have b2 := runNum_lt_iff l' (j := (l.take i).sum) i (by omega)
      have b3 := h (l.take i).sum (by omega)
      rw [b3] at b1
      exact absurd (b1.mp (b2.mpr hlt)) (lt_irrefl _)
    · have b1 := runNum_lt_iff l (j := (l'.take i).sum) i (by omega)
      have b2 := runNum_lt_iff l' (j := (l'.take i).sum) i (by omega)
      have b3 := h (l'.take i).sum (by omega)
      rw [b3] at b1
      exact absurd (b2.mp (b1.mpr hlt)) (lt_irrefl _)
  have hlong : ∀ {m m' : List ℕ}, (∀ a ∈ m', 1 ≤ a) → m.sum = K → m'.sum = K →
      (∀ i, (m.take i).sum = (m'.take i).sum) → ¬ m.length < m'.length := by
    intro m m' hp' hs hs' ht hlt
    have c1 := List.sum_take_succ m' m.length hlt
    have c2 := ht (m.length + 1)
    have c3 := ht m.length
    rw [List.take_of_length_le (by omega)] at c2
    rw [List.take_length] at c3
    have c4 := hp' (m'[m.length]'hlt) (List.getElem_mem _)
    omega
  have hlen : l.length = l'.length := by
    have e1 := hlong hpos' hsum hsum' htake
    have e2 := hlong hpos hsum' hsum (fun i => (htake i).symm)
    omega
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have d1 := List.sum_take_succ l i h1
  have d2 := List.sum_take_succ l' i h2
  have d3 := htake i
  have d4 := htake (i + 1)
  omega

/-! ## Labels -/

/-- Two strictly monotone sequences with the same values are equal. -/
lemma strictMono_eq_of_mem {r : ℕ} {f g : Fin r → ℕ} (hf : StrictMono f) (hg : StrictMono g)
    (hgf : ∀ i, ∃ j, f j = g i) : f = g := by
  set s := univ.image f with hs
  have hcard : s.card = r := by
    rw [hs, Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.orderEmbOfFin_unique hcard (f := f) (fun x => Finset.mem_image_of_mem _
    (Finset.mem_univ _)) hf
  have h2 := Finset.orderEmbOfFin_unique hcard (f := g) (fun x => by
    obtain ⟨j, hj⟩ := hgf x
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩) hg
  rw [h1, h2]

/-- Two pivots of `P(C)` have a slot of `P(C)` strictly between them iff their labels are not
consecutive. -/
lemma lbl_gap {C : Finset (Fin N → ℕ)} {a b : Fin N} (ha : a ∈ Covers.P C)
    (hb : b ∈ Covers.P C) (hab : a < b) :
    (∃ g ∈ Covers.P C, a < g ∧ g < b) ↔ lbl C a + 1 < lbl C b := by
  constructor
  · rintro ⟨g, hg, h1, h2⟩
    have := lbl_strictMono ha h1
    have := lbl_strictMono hg h2
    omega
  · intro h
    by_contra hno
    push_neg at hno
    have hsub : (Covers.P C).filter (· < b) ⊆ insert a ((Covers.P C).filter (· < a)) := by
      intro x hx
      obtain ⟨hxP, hxb⟩ := Finset.mem_filter.mp hx
      rcases lt_trichotomy x a with h1 | h1 | h1
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxP, h1⟩)
      · rw [h1]; exact Finset.mem_insert_self _ _
      · exact absurd (hno x hxP h1) (not_le.mpr hxb)
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    unfold lbl at h
    omega

lemma sum_filter_lbl {C : Finset (Fin N → ℕ)} {n₀ : Fin N} (hn₀ : n₀ ∈ Covers.P C)
    (f : Fin N → ℕ) :
    ∑ n ∈ (Covers.P C).filter (fun n => lbl C n = lbl C n₀), f n = f n₀ := by
  have : (Covers.P C).filter (fun n => lbl C n = lbl C n₀) = {n₀} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, h⟩; exact lbl_injOn hn hn₀ h
    · rintro rfl; exact ⟨hn₀, rfl⟩
  rw [this, Finset.sum_singleton]

/-! ## The representation of a configuration -/

/-- The constraints pass to the row-permuted tuple. -/
lemma consM_perm {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ} {smax u : ℕ}
    {lab : Fin u → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ} (σ : Equiv.Perm (Fin K))
    (h : ConsM E l smax u lab c) :
    ConsM (E.submatrix σ id) l smax u lab (fun y => c (σ y)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun y g hg => ?_, fun j hj1 hj2 => ?_⟩
  · obtain ⟨a, b, v, hv0, hv⟩ := h3 (σ y) g hg
    exact ⟨a, b, v, hv0, fun y' => by simpa [colC, Matrix.submatrix] using hv (σ y')⟩
  · obtain ⟨y, g, hg, hh⟩ := h4 j hj1 hj2
    exact ⟨σ.symm y, g, by simpa using hg, hh⟩

/-- **The representation of a configuration `(C, B)` with skeleton `(r, Cs, lab, ex, s4)`**:
the rows `T y = t(σ y)`, the pivot slots `p`, the run list `lr`. -/
structure CfgRep (S : Finset (Fin N → ℕ)) (tl : (Fin N → ℕ) → ℕ) (D r₀ : ℕ)
    (CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)) (r : ℕ) (Cs : Finset (Fin r))
    (lab : Finset (Fin (Cs.card * D))) (ex : Fin r → Fin r → ℕ)
    (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) where
  /-- the rows, matched to the pivots -/
  T : Fin r → Fin N → ℕ
  /-- the pivot slots (earliest first) -/
  p : Fin r → Fin N
  /-- the run list -/
  lr : List ℕ
  hr0 : r < r₀
  hr1 : 0 < r
  inj : Function.Injective T
  memS : ∀ y, T y ∈ S
  memB : ∀ v, v ∈ CB.2 ↔ ∃ y, T y = v
  CsubB : CB.1 ⊆ CB.2
  memC : ∀ y, y ∈ Cs ↔ T y ∈ CB.1
  mono : StrictMono p
  pivP : ∀ j, p j ∈ Covers.P CB.1
  suppP : ∀ y n, T y n ≠ 0 → n ∈ Covers.P CB.1
  PCcard : (Covers.P CB.1).card ≤ Cs.card * D
  labC : ∀ ℓ : Fin (Cs.card * D), ℓ ∈ lab ↔ ∃ j, lbl CB.1 (p j) = ℓ.val
  exC : ∀ y i, ex y i = if y ∈ Cs then T y (p i) else 0
  s4C : ∀ y ∉ Cs, s4 y = (fun ℓ : Fin (r₀ * D) =>
    ∑ n ∈ (Covers.P CB.1).filter (fun n => lbl CB.1 n = ℓ.val), T y n, tl (T y))
  cons : ∀ smax, (∀ j, (p j : ℕ) ≤ smax) →
    ConsM (fun y i => T y (p i)) lr smax r (fun j => (p j : ℕ))
      (fun y => (fun n => if ∃ j, p j = n then 0 else T y n, tl (T y)))
  lrpos : ∀ a ∈ lr, 1 ≤ a
  lrsum : lr.sum = r
  same : ∀ j (h1 : 1 ≤ j) (h2 : j < r), runNum lr (j - 1) = runNum lr j ↔
    ¬ ∃ g ∈ Covers.P CB.1, p ⟨j - 1, by omega⟩ < g ∧ g < p ⟨j, h2⟩
  inv : (fun y i => T y (p i) : Matrix (Fin r) (Fin r) ℕ) ∈ InvPattern r

/-- **Every configuration with skeleton `(r, Cs, lab, ex, s4)` has a representation.** -/
theorem cfg_rep {S : Finset (Fin N → ℕ)} {tl : (Fin N → ℕ) → ℕ} {D r₀ : ℕ}
    (hD : ∀ v ∈ S, Covers.deg v ≤ D) {CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)}
    (hCB : CB ∈ configs r₀ 0 0 S) {r : ℕ} {Cs : Finset (Fin r)}
    {lab : Finset (Fin (Cs.card * D))} {ex : Fin r → Fin r → ℕ}
    {s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ} (hs : cfgSkel D r₀ tl CB = ⟨r, Cs, lab, ex, s4⟩) :
    Nonempty (CfgRep S tl D r₀ CB r Cs lab ex s4) := by
  obtain ⟨C, B⟩ := CB
  obtain ⟨-, hcfg⟩ := Finset.mem_filter.mp hCB
  obtain ⟨hBS, hli, hrank, hcov, -, hRj, -⟩ := hcfg
  simp only at hBS hli hrank hcov hRj
  set t := tupleOf B with ht
  have hli' : LinearIndependent ℚ (fun i => Covers.vq (t i)) := tupleOf_li hli
  have hk := card_pivs hli'
  have hinv := (skel_mem hli').1
  set σ := Classical.choose (exists_perm_support (pattern t) hinv) with hσdef
  have hσ : ∀ j, pattern t (σ j) j ≠ 0 := Classical.choose_spec (exists_perm_support _ hinv)
  have hunf : cfgSkel D r₀ tl (C, B) =
      ⟨B.card, univ.filter (fun i => t (σ i) ∈ C),
        (univ.filter fun ℓ : Fin ((univ.filter (fun i => t (σ i) ∈ C)).card * D) =>
          ∃ j, lbl C (pivSlot t hk j) = ℓ.val,
         fun y i => if y ∈ univ.filter (fun i => t (σ i) ∈ C) then
           t (σ y) (pivSlot t hk i) else 0,
         fun y => if y ∈ univ.filter (fun i => t (σ i) ∈ C) then (0, 0) else
          (fun ℓ : Fin (r₀ * D) =>
            ∑ n ∈ (Covers.P C).filter (fun n => lbl C n = ℓ.val), t (σ y) n,
           tl (t (σ y))))⟩ := by
    unfold cfgSkel
    rw [dif_pos hli']
  rw [hunf] at hs
  obtain ⟨hr, hs1⟩ := Sigma.mk.inj_iff.mp hs
  subst hr
  obtain ⟨hC', hs2⟩ := Sigma.mk.inj_iff.mp (eq_of_heq hs1)
  subst hC'
  have hs3 := eq_of_heq hs2
  simp only [Prod.mk.injEq] at hs3
  obtain ⟨hlab, hex, hs4⟩ := hs3
  subst hlab hex hs4
  -- basic facts
  have hCB' : C ⊆ B := hcov.1
  have hPeq : C.biUnion Covers.supp = Covers.P B := hcov.2
  have hrB : B.card < r₀ := by
    have := Covers.rank_eq_card (S := B) (B := B) ⟨subset_rfl, hli, le_rfl⟩
    omega
  have hB1 : 0 < B.card := by
    have := Finset.card_le_card (Finset.sdiff_subset (s := B) (t := C)); omega
  have htσ_inj : Function.Injective fun i => t (σ i) :=
    (tupleOf_injective B).comp σ.injective
  have hC'img : (univ.filter fun i => t (σ i) ∈ C).image (fun i => t (σ i)) = C := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hv
      obtain ⟨i, hi⟩ := tupleOf_surj B (hCB' hv)
      refine ⟨σ.symm i, ?_, ?_⟩ <;> simp [ht, hi, hv]
  have hcardC' : (univ.filter fun i => t (σ i) ∈ C).card = C.card := by
    calc _ = ((univ.filter fun i => t (σ i) ∈ C).image (fun i => t (σ i))).card :=
          (Finset.card_image_of_injective _ htσ_inj).symm
      _ = C.card := by rw [hC'img]
  have hdegC : ∀ v ∈ C, Covers.deg v ≤ D := fun v hv => hD v (hBS (hCB' hv))
  have hPC_le : (Covers.P C).card ≤ C.card * D := card_P_le hdegC
  have hPCP : Covers.P C = Covers.P B := by
    unfold Covers.P at hPeq ⊢; rw [hPeq]
  have hpivP : ∀ i, pivSlot t hk i ∈ Covers.P C := by
    intro i
    have h := hσ i
    rw [pattern_eq t hk] at h
    rw [hPCP]
    exact Finset.mem_biUnion.mpr ⟨t (σ i), tupleOf_mem B _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hcol : ∀ g, g ∈ colSupp t ↔ g ∈ Covers.P C := by
    intro g
    rw [hPCP]
    simp only [colSupp, Finset.mem_filter, Finset.mem_univ, true_and, Covers.P,
      Finset.mem_biUnion, Covers.supp]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨t i, tupleOf_mem B i, hi⟩
    · rintro ⟨v, hv, hvg⟩
      obtain ⟨i, rfl⟩ := tupleOf_surj B hv
      exact ⟨i, hvg⟩
  obtain ⟨hpos, hsum⟩ := (mem_comps _ _).mp (skel_mem hli').2
  have hpat : (fun y i => t (σ y) (pivSlot t hk i) : Matrix (Fin B.card) (Fin B.card) ℕ) =
      (pattern t).submatrix σ id := by
    funext y i; simp [Matrix.submatrix, pattern_eq t hk]
  refine ⟨{
    T := fun y => t (σ y)
    p := pivSlot t hk
    lr := runList t
    hr0 := hrB
    hr1 := hB1
    inj := htσ_inj
    memS := fun y => hBS (tupleOf_mem B _)
    memB := fun v => ?_
    CsubB := hCB'
    memC := fun y => by simp
    mono := pivSlot_strictMono t hk
    pivP := hpivP
    suppP := fun y n h => ?_
    PCcard := by simpa only [hcardC'] using hPC_le
    labC := fun ℓ => by simp
    exC := fun y i => rfl
    s4C := fun y hy => by simp only [if_neg hy]
    cons := fun smax hsm => ?_
    lrpos := hpos
    lrsum := hsum
    same := fun j h1 h2 => ?_
    inv := ?_ }⟩
  · constructor
    · intro hv
      obtain ⟨i, hi⟩ := tupleOf_surj B hv
      exact ⟨σ.symm i, by simp [ht, hi]⟩
    · rintro ⟨y, rfl⟩; exact tupleOf_mem B _
  · rw [hPCP]
    exact Finset.mem_biUnion.mpr ⟨t (σ y), tupleOf_mem B _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  · have hC := cons_tuple t hk rfl rfl hsum hpos hB1 hsm tl
    have h2 := consM_perm σ hC
    rw [← hpat] at h2
    convert h2 using 2
    refine Prod.ext (funext fun n => ?_) rfl
    simp only [mem_pivSet t hk n]
  · rw [sameRun_iff t hk rfl hsum h1 h2]
    simp only [hcol]
  · show _ ≠ 0
    rw [hpat]
    have e : ((pattern t).submatrix σ id).map (Nat.cast : ℕ → ℚ) =
        ((pattern t).map (Nat.cast : ℕ → ℚ)).submatrix σ id := rfl
    rw [e, Matrix.det_permute]
    exact mul_ne_zero (by simp) hinv

section Unique

variable {S S' : Finset (Fin N → ℕ)} {tl tl' : (Fin N → ℕ) → ℕ} {D r₀ : ℕ}
  {CB CB' : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)} {r : ℕ} {Cs : Finset (Fin r)}
  {lab : Finset (Fin (Cs.card * D))} {ex : Fin r → Fin r → ℕ}
  {s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ}

lemma CfgRep.lbl_lt (R : CfgRep S tl D r₀ CB r Cs lab ex s4) (j : Fin r) :
    lbl CB.1 (R.p j) < Cs.card * D :=
  (RankFull.Config.lbl_lt (R.pivP j)).trans_le R.PCcard

lemma CfgRep.lbl_lt' (R : CfgRep S tl D r₀ CB r Cs lab ex s4) {n : Fin N}
    (hn : n ∈ Covers.P CB.1) : lbl CB.1 n < r₀ * D := by
  have h1 := (RankFull.Config.lbl_lt hn).trans_le R.PCcard
  have h2 : Cs.card ≤ r := by simpa using Finset.card_le_univ Cs
  have h3 := R.hr0
  calc lbl CB.1 n < Cs.card * D := h1
    _ ≤ r₀ * D := Nat.mul_le_mul_right _ (by omega)

lemma CfgRep.lbl_mono (R : CfgRep S tl D r₀ CB r Cs lab ex s4) :
    StrictMono fun j => lbl CB.1 (R.p j) :=
  fun _ _ hab => lbl_strictMono (R.pivP _) (R.mono hab)

/-- The row `y ∉ C` at a slot of `P(C)`: the (s4) monomial at its label. -/
lemma CfgRep.s4_at (R : CfgRep S tl D r₀ CB r Cs lab ex s4) {y : Fin r} (hy : y ∉ Cs)
    {n : Fin N} (hn : n ∈ Covers.P CB.1) :
    (s4 y).1 ⟨lbl CB.1 n, R.lbl_lt' hn⟩ = R.T y n := by
  rw [R.s4C y hy]
  exact sum_filter_lbl hn _

/-- **The labels, the pattern and the run list are determined by the skeleton.** -/
theorem rep_unique (R : CfgRep S tl D r₀ CB r Cs lab ex s4)
    (R' : CfgRep S' tl' D r₀ CB' r Cs lab ex s4) :
    (∀ j, lbl CB.1 (R.p j) = lbl CB'.1 (R'.p j)) ∧
      (∀ y i, R.T y (R.p i) = R'.T y (R'.p i)) ∧ R.lr = R'.lr := by
  have hL : (fun j => lbl CB.1 (R.p j)) = fun j => lbl CB'.1 (R'.p j) := by
    refine strictMono_eq_of_mem R.lbl_mono R'.lbl_mono fun i => ?_
    have hm : (⟨lbl CB'.1 (R'.p i), R'.lbl_lt i⟩ : Fin (Cs.card * D)) ∈ lab :=
      (R'.labC _).mpr ⟨i, rfl⟩
    exact (R.labC _).mp hm
  have hLj : ∀ j, lbl CB.1 (R.p j) = lbl CB'.1 (R'.p j) := fun j => congrFun hL j
  refine ⟨hLj, fun y i => ?_, ?_⟩
  · by_cases hy : y ∈ Cs
    · have h1 := R.exC y i
      have h2 := R'.exC y i
      rw [if_pos hy] at h1 h2
      rw [← h1, ← h2]
    · rw [← R.s4_at hy (R.pivP i), ← R'.s4_at hy (R'.pivP i)]
      exact congrArg (s4 y).1 (Fin.ext (hLj i))
  · refine list_eq_of_runNum R.lrpos R'.lrpos R.lrsum R'.lrsum
      (runNum_eq_of_same R.lrpos R'.lrpos R.lrsum R'.lrsum fun j h1 h2 => ?_)
    rw [R.same j h1 h2, R'.same j h1 h2]
    have hlt : (⟨j - 1, by omega⟩ : Fin r) < ⟨j, h2⟩ := Fin.mk_lt_mk.mpr (by omega)
    rw [lbl_gap (R.pivP _) (R.pivP _) (R.mono hlt), lbl_gap (R'.pivP _) (R'.pivP _)
      (R'.mono hlt), hLj, hLj]

end Unique

/-! ## The cover data of a skeleton and the realised terms -/

/-- The cover data of the recursion for a skeleton with pattern `E` and run list `lr`. -/
noncomputable def covData {r r₀ D : ℕ} (E : Matrix (Fin r) (Fin r) ℕ) (Cs : Finset (Fin r))
    (lr : List ℕ) (τ : Fin r → ℝ) (ex : Fin r → Fin r → ℕ)
    (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) : CovD r where
  Cd := Cs
  lg := joinC E Cs lr
  Wc := ∏ i, (τ i)⁻¹ ^ exExcess ex i
  mono := fun y ℓ => if h : ℓ < r₀ * D then (s4 y).1 ⟨ℓ, h⟩ else 0
  tailR := fun y => (s4 y).2

/-- The term of a realised tuple: `∏_j q_j^{-1} ∏_{y ∈ C} ∏_j q_j^{E_yj} ∏_j τ_j^{-e_j} ≥ 1`. -/
lemma term_ge_oneC {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (Cd : Finset (Fin K))
    (q τ : Fin K → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) (hqτ : ∀ j, τ j ≤ q j)
    (hs : ∀ j, 1 ≤ ∑ y ∈ Cd, E y j) :
    1 ≤ (∏ j, (q j)⁻¹) * (∏ y ∈ Cd, ∏ j, q j ^ E y j) *
      ∏ j, (τ j)⁻¹ ^ ((∑ y ∈ Cd, E y j) - 1) := by
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le (by linarith [hτ1 j]) (hqτ j)
  have h1 : (∏ y ∈ Cd, ∏ j, q j ^ E y j) = ∏ j, q j ^ (∑ y ∈ Cd, E y j) := by
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => Finset.prod_pow_eq_pow_sum _ _ _
  rw [h1, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have := Finset.prod_le_prod (s := univ) (f := fun _ => (1 : ℝ))
    (g := fun j => (q j)⁻¹ * q j ^ (∑ y ∈ Cd, E y j) * (τ j)⁻¹ ^ ((∑ y ∈ Cd, E y j) - 1))
    (fun _ _ => zero_le_one) (fun j _ => by
      have hsj := hs j
      have e : (q j)⁻¹ * q j ^ (∑ y ∈ Cd, E y j) * (τ j)⁻¹ ^ ((∑ y ∈ Cd, E y j) - 1) =
          (q j / τ j) ^ ((∑ y ∈ Cd, E y j) - 1) := by
        have : q j ^ (∑ y ∈ Cd, E y j) = q j * q j ^ ((∑ y ∈ Cd, E y j) - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hsj]
        rw [this, div_pow, inv_pow]
        field_simp [(hq0 j).ne']
      show (1 : ℝ) ≤ (q j)⁻¹ * q j ^ (∑ y ∈ Cd, E y j) * (τ j)⁻¹ ^ ((∑ y ∈ Cd, E y j) - 1)
      rw [e]
      exact one_le_pow₀ ((one_le_div (by linarith [hτ1 j])).mpr (hqτ j)))
  simpa using this

lemma prod_split_p {K : ℕ} (p : Fin K → Fin N) (hp : Function.Injective p) (q : Fin N → ℝ)
    (v : Fin N → ℕ) :
    ∏ n, q n ^ v n = (∏ n, q n ^ (if ∃ j, p j = n then 0 else v n)) *
      ∏ j, q (p j) ^ v (p j) := by
  have h1 : ∀ n, q n ^ v n = q n ^ (if ∃ j, p j = n then 0 else v n) *
      (if n ∈ univ.image p then q n ^ v n else 1) := by
    intro n
    by_cases h : ∃ j, p j = n
    · have hm : n ∈ univ.image p := by
        obtain ⟨j, rfl⟩ := h; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      rw [if_pos h, if_pos hm, pow_zero, one_mul]
    · have hm : n ∉ univ.image p := by
        intro hm; obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm; exact h ⟨j, hj⟩
      rw [if_neg h, if_neg hm, mul_one]
  rw [Finset.prod_congr rfl (fun n _ => h1 n), Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_image hp.injOn]

section Terms

variable {S : Finset (Fin N → ℕ)} {tl : (Fin N → ℕ) → ℕ} {D r₀ : ℕ}
  {CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)} {r : ℕ} {Cs : Finset (Fin r)}
  {lab : Finset (Fin (Cs.card * D))} {ex : Fin r → Fin r → ℕ}
  {s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ}

/-- The labels of the recursion: the pivot slots. -/
def CfgRep.labs (R : CfgRep S tl D r₀ CB r Cs lab ex s4) : Fin r → ℕ := fun j => (R.p j : ℕ)

/-- The content of the recursion: the free slots of the rows and their tails. -/
noncomputable def CfgRep.cont (R : CfgRep S tl D r₀ CB r Cs lab ex s4) :
    Fin r → (Fin N → ℕ) × ℕ :=
  fun y => (fun n => if ∃ j, R.p j = n then 0 else R.T y n, tl (R.T y))

lemma CfgRep.memC' (R : CfgRep S tl D r₀ CB r Cs lab ex s4) (v : Fin N → ℕ) :
    v ∈ CB.1 ↔ ∃ y ∈ Cs, R.T y = v := by
  constructor
  · intro hv
    obtain ⟨y, rfl⟩ := (R.memB v).mp (R.CsubB hv)
    exact ⟨y, (R.memC y).mpr hv, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact (R.memC y).mp hy

/-- A slot of `P(C)` occurs in a row of `C`. -/
lemma CfgRep.exists_C (R : CfgRep S tl D r₀ CB r Cs lab ex s4) {n : Fin N}
    (hn : n ∈ Covers.P CB.1) : ∃ y ∈ Cs, R.T y n ≠ 0 := by
  obtain ⟨v, hv, hvn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨y, hy, rfl⟩ := (R.memC' v).mp hv
  exact ⟨y, hy, (Finset.mem_filter.mp hvn).2⟩

lemma CfgRep.iffC (R : CfgRep S tl D r₀ CB r Cs lab ex s4) (g : Fin N) :
    (∃ y ∈ Cs, (R.cont y).1 g ≠ 0) ↔ (¬ ∃ j, R.p j = g) ∧ g ∈ Covers.P CB.1 := by
  constructor
  · rintro ⟨y, -, hy⟩
    simp only [CfgRep.cont] at hy
    split_ifs at hy with hpiv
    · exact absurd rfl hy
    · exact ⟨hpiv, R.suppP y g hy⟩
  · rintro ⟨hpiv, hg⟩
    obtain ⟨y, hy, hyg⟩ := R.exists_C hg
    exact ⟨y, hy, by simp only [CfgRep.cont, if_neg hpiv]; exact hyg⟩

lemma CfgRep.rankC_eq (R : CfgRep S tl D r₀ CB r Cs lab ex s4) (cd : CovD r)
    (hcd : cd.Cd = Cs) {g : Fin N} :
    rankC cd r R.labs R.cont g = lbl CB.1 g := by
  unfold rankC lbl
  conv_rhs => rw [← Finset.filter_card_add_filter_neg_card_eq_card (fun n => ∃ j, R.p j = n)]
  congr 1
  · rw [Finset.filter_filter]
    have himg : (univ.filter fun j : Fin r => R.labs j < (g : ℕ)).image R.p =
        (Covers.P CB.1).filter (fun n => n < g ∧ ∃ j, R.p j = n) := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, CfgRep.labs]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨R.pivP j, Fin.lt_def.mpr hj, j, rfl⟩
      · rintro ⟨-, hng, j, rfl⟩; exact ⟨j, Fin.lt_def.mp hng, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ R.mono.injective]
  · rw [Finset.filter_filter]
    congr 1
    ext g'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcd]
    rw [R.iffC g']
    tauto

/-- **The constraints of the cover recursion hold for a realised configuration.** -/
theorem CfgRep.consC (R : CfgRep S tl D r₀ CB r Cs lab ex s4)
    {E : Matrix (Fin r) (Fin r) ℕ} {lr : List ℕ} (τ : Fin r → ℝ)
    (hE : ∀ y i, R.T y (R.p i) = E y i) (hlr : R.lr = lr) {smax : ℕ}
    (hsm : ∀ j, (R.p j : ℕ) ≤ smax) :
    ConsC E lr smax (covData E Cs lr τ ex s4) r R.labs R.cont := by
  have hEf : (fun y i => R.T y (R.p i) : Matrix (Fin r) (Fin r) ℕ) = E := by
    funext y i; exact hE y i
  have hM := R.cons smax hsm
  rw [hEf, hlr] at hM
  refine ⟨hM, fun g ⟨y, hy⟩ => ?_, fun y hy g => ?_, fun y hy => ?_⟩
  · simp only [CfgRep.cont] at hy
    split_ifs at hy with hpiv
    · exact absurd rfl hy
    · exact (R.iffC g).mpr ⟨hpiv, R.suppP y g hy⟩
  · have hcd : (covData E Cs lr τ ex s4).Cd = Cs := rfl
    rw [hcd]
    by_cases hpiv : ∃ j, R.p j = g
    · rw [if_neg (fun h => ((R.iffC g).mp h).1 hpiv)]
      simp only [CfgRep.cont, if_pos hpiv]
    · by_cases hgP : g ∈ Covers.P CB.1
      · rw [if_pos ((R.iffC g).mpr ⟨hpiv, hgP⟩), R.rankC_eq _ hcd]
        simp only [CfgRep.cont, if_neg hpiv, covData, dif_pos (R.lbl_lt' hgP)]
        exact (R.s4_at hy hgP).symm
      · rw [if_neg (fun h => hgP ((R.iffC g).mp h).2)]
        simp only [CfgRep.cont, if_neg hpiv]
        by_contra h
        exact hgP (R.suppP y g h)
  · simp only [CfgRep.cont, covData]
    rw [R.s4C y hy]

/-- **A configuration is determined by its labels and its content** (for a fixed pattern). -/
theorem CfgRep.cfg_inj {CB' : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)} {tl' : (Fin N → ℕ) → ℕ}
    (R : CfgRep S tl D r₀ CB r Cs lab ex s4) (R' : CfgRep S tl' D r₀ CB' r Cs lab ex s4)
    {E : Matrix (Fin r) (Fin r) ℕ} (hE : ∀ y i, R.T y (R.p i) = E y i)
    (hE' : ∀ y i, R'.T y (R'.p i) = E y i) (h1 : R.labs = R'.labs)
    (h2 : ∀ y n, (R.cont y).1 n = (R'.cont y).1 n) : CB = CB' := by
  have hp : R.p = R'.p := funext fun j => Fin.ext (congrFun h1 j)
  have hT : R.T = R'.T := by
    funext y n
    by_cases hpiv : ∃ j, R.p j = n
    · obtain ⟨j, rfl⟩ := hpiv
      rw [hE y j, ← hE' y j, hp]
    · have hpiv' : ¬ ∃ j, R'.p j = n := by rw [← hp]; exact hpiv
      have := h2 y n
      simp only [CfgRep.cont, if_neg hpiv, if_neg hpiv'] at this
      exact this
  refine Prod.ext ?_ ?_
  · ext v; rw [R.memC', R'.memC', hT]
  · ext v; rw [R.memB, R'.memB, hT]

end Terms

section Count

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θE : ℝ≥0∞}

/-- **The term of a realised configuration is `≥ 1`** (the caps `τ_j ≤ q_{p_j}`, the windows,
and the weight `∏_j (q_j/τ_j)^{e_j}` with `e_j = s^C_j - 1`). -/
theorem CfgRep.one_le_term {k r₀ D Dmax X₀ smax : ℕ} (J : JitterLaw Ω P θE) (G : ℕ → Set Ω)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (Jw : Set ℝ) (A Eu : ℝ) {ω : Ω}
    {CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)} {Cs : Finset (Fin (k + 1))}
    {lab : Finset (Fin (Cs.card * D))} {ex : Fin (k + 1) → Fin (k + 1) → ℕ}
    {s4 : Fin (k + 1) → (Fin (r₀ * D) → ℕ) × ℕ}
    (R : CfgRep (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) D r₀ CB (k + 1) Cs lab ex s4)
    {E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ} {lr : List ℕ} (τ : Fin (k + 1) → ℝ)
    (hE : ∀ y i, R.T y (R.p i) = E y i) (hlr : R.lr = lr) (hτ1 : ∀ j, 1 ≤ τ j)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin (k + 1),
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (hω : ω ∈ G smax) :
    1 ≤ if ConsC E lr smax (covData E Cs lr τ ex s4) (k + 1) R.labs R.cont then
      (J.A (R.labs (Fin.last k))).indicator 1 ω *
        FfullC J E lr (covData E Cs lr τ ex s4) Jw G A Eu k ω (Fin.init R.labs)
          (R.labs (Fin.last k)) R.cont (J.q (R.labs (Fin.last k)) ω) else 0 := by
  set cd := covData E Cs lr τ ex s4 with hcd
  set p := R.p with hp
  have hpdec : ∀ j, ω ∈ J.A (p j) := by
    intro j
    obtain ⟨y, -, hy⟩ := R.exists_C (R.pivP j)
    exact (Finset.mem_filter.mp (windowVecs_supp (R.memS y) (p j) hy)).2
  have hsm : ∀ j, (p j : ℕ) ≤ smax := by
    intro j
    obtain ⟨y, -, hy⟩ := R.exists_C (R.pivP j)
    have hel := tailOf_mem (R.memS y)
    obtain ⟨hel1, hsupp, -, hval⟩ := Finset.mem_filter.mp hel
    refine hsmax ω (p j) (hpdec j) _ hval ?_
    refine elemVal_ge (q := qOf J ω)
      (x := (R.T y, tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw (R.T y))) ?_
      (fun n hn => ?_) hy
    · exact smooth_pos (Finset.mem_product.mp hel1).2
    · exact (hq ω n (Finset.mem_filter.mp (hsupp n hn)).2).le
  have hC := R.consC τ hE hlr hsm
  rw [if_pos hC, ZSC_term_eq]
  have hA1 : ∏ j, (J.A (R.labs j)).indicator (1 : Ω → ℝ≥0∞) ω = 1 :=
    Finset.prod_eq_one fun j _ => by
      rw [CfgRep.labs, Set.indicator_of_mem (hpdec j)]; rfl
  have hdec : ω ∈ decSet J R.cont := by
    intro y n hn
    simp only [CfgRep.cont] at hn
    split_ifs at hn with h
    · exact absurd rfl hn
    · exact (Finset.mem_filter.mp (windowVecs_supp (R.memS y) n hn)).2
  have hGl : ω ∈ G (R.labs (Fin.last k)) := hG _ _ (hsm _) hω
  have hlen : runNum lr k + 1 = cd.lg.length := by
    have := runNum_last (hlr ▸ R.lrpos) (hlr ▸ R.lrsum) (Nat.succ_pos k)
    simp only [hcd, covData, joinC_length]
    simpa using this
  have hphi := PhiC_top (N := N) J (A := A) (Eu := Eu) hlen ω
    (R.labs ⟨runFirst lr k, Nat.lt_succ_of_le (runFirst_le lr k)⟩)
  have hq0 : ∀ j, 0 < J.q (p j : ℕ) ω := fun j => by linarith [hq ω _ (hpdec j)]
  have hinv : ∏ j, invq (J.q (R.labs j) ω) = ENNReal.ofReal (∏ j, (J.q (p j : ℕ) ω)⁻¹) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (inv_pos.mpr (hq0 j)).le)]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold invq
    rw [CfgRep.labs, Set.indicator_of_mem (show J.q (p j : ℕ) ω ∈ Set.Ioi (0 : ℝ) from hq0 j)]
  have hwin : ∀ y, cvs J ω R.cont y * ∏ j, J.q (p j : ℕ) ω ^ E y j ∈ Jw := by
    intro y
    have hel := tailOf_mem (R.memS y)
    have hval := (Finset.mem_filter.mp hel).2.2.2
    convert hval using 1
    unfold cvs cval elemVal
    simp only [CfgRep.cont]
    rw [prod_split_p p R.mono.injective (qOf J ω) (R.T y)]
    have hre : ∏ j, J.q (p j : ℕ) ω ^ E y j = ∏ j, J.q (p j : ℕ) ω ^ R.T y (p j) :=
      Finset.prod_congr rfl fun j _ => by rw [hE]
    rw [hre]
    simp only [qOf]
    ring
  have hIz : IzMC J E cd Jw (k + 1) R.labs ω R.cont =
      ENNReal.ofReal (∏ y ∈ Cs, ∏ j, J.q (p j : ℕ) ω ^ E y j) := by
    unfold IzMC
    have hz : ∀ z : Fin (k + 1 - (k + 1)) → ℝ, mergeL (K := k + 1) (k + 1 - (k + 1)) z
        (uvec J (k + 1) R.labs ω) = fun j => Real.log (J.q (p j : ℕ) ω) := by
      intro z
      funext j
      unfold mergeL uvec
      rw [dif_neg (by omega), dif_pos j.isLt]
      rfl
    rw [lintegral_congr fun z => by rw [hz z], lintegral_const]
    have hvol : MeasureTheory.volume (Set.univ : Set (Fin (k + 1 - (k + 1)) → ℝ)) = 1 := by
      rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
      refine Finset.prod_eq_one fun i _ => ?_
      exact absurd i.isLt (by omega)
    rw [hvol, mul_one]
    unfold LcoreC
    have hind : ∏ y, Jw.indicator (1 : ℝ → ℝ≥0∞) (cvs J ω R.cont y *
        Real.exp (RankFull.rowLog E (fun j => Real.log (J.q (p j : ℕ) ω)) y)) = 1 :=
      Finset.prod_eq_one fun y _ => by
        rw [exp_rowLog E (fun j => J.q (p j : ℕ) ω) hq0 y, Set.indicator_of_mem (hwin y)]
        rfl
    rw [hind, mul_one, ENNReal.ofReal_prod_of_nonneg (fun y _ => Finset.prod_nonneg fun j _ =>
      pow_nonneg (hq0 j).le _)]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [exp_rowLog E (fun j => J.q (p j : ℕ) ω) hq0 y]
  rw [hA1, Set.indicator_of_mem hdec, Set.indicator_of_mem hGl, hphi, hinv, hIz]
  simp only [Pi.one_apply, one_mul, mul_one]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (inv_pos.mpr (hq0 j)).le),
    ← ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun j _ =>
      (inv_pos.mpr (hq0 j)).le) (Finset.prod_nonneg fun y _ => Finset.prod_nonneg fun j _ =>
        pow_nonneg (hq0 j).le _))]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexc : ∀ i, exExcess ex i = (∑ y ∈ Cs, E y i) - 1 := by
    intro i
    unfold exExcess
    congr 1
    simp_rw [R.exC]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun y _ => hE y i
  have hWc : cd.Wc = ∏ j, (τ j)⁻¹ ^ ((∑ y ∈ Cs, E y j) - 1) := by
    simp only [hcd, covData, hexc]
  rw [hWc]
  refine term_ge_oneC E Cs _ τ hτ1 (fun j => ?_) (fun j => ?_)
  · -- the caps
    refine hτ ω _ (hpdec j) j ?_
    have hsub : (Finset.Iio j).image p ⊆ (decOf J ω).filter (· < p j) := by
      intro n hn
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpdec j'⟩,
        R.mono (Finset.mem_Iio.mp hj')⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ R.mono.injective, Fin.card_Iio] at this
    exact this
  · obtain ⟨y, hy, hyp⟩ := R.exists_C (R.pivP j)
    rw [hE] at hyp
    exact le_trans (Nat.one_le_iff_ne_zero.mpr hyp)
      (Finset.single_le_sum (f := fun y => E y j) (fun _ _ => Nat.zero_le _) hy)

/-- **The realised count of a cover skeleton is dominated by the labelled sum of the cover
recursion** (pathwise, on `G_{<s_max}`). -/
theorem cfgCount_le_ZSC {k r₀ D Dmax X₀ smax : ℕ} (J : JitterLaw Ω P θE) (G : ℕ → Set Ω)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (Jw : Set ℝ) (A Eu : ℝ)
    {Cs : Finset (Fin (k + 1))} {lab : Finset (Fin (Cs.card * D))}
    {ex : Fin (k + 1) → Fin (k + 1) → ℕ} {s4 : Fin (k + 1) → (Fin (r₀ * D) → ℕ) × ℕ}
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ) (lr : List ℕ) (τ : Fin (k + 1) → ℝ)
    (hτ1 : ∀ j, 1 ≤ τ j) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin (k + 1),
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (ω : Ω) (hω : ω ∈ G smax)
    (hfix : ∀ CB, ∀ R : CfgRep (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) D r₀ CB (k + 1) Cs lab ex s4,
      (∀ y i, R.T y (R.p i) = E y i) ∧ R.lr = lr) :
    cfgSkelCount D r₀ 0 0 (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) (k + 1) Cs lab ex s4 ≤
      ZSC (N := N) J E lr (covData E Cs lr τ ex s4) Jw D Dmax X₀ smax G A Eu k ω := by
  set S := windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw with hS
  set tl := tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw with htl
  set cd := covData E Cs lr τ ex s4 with hcd
  set T := (configs r₀ 0 0 S).filter fun CB =>
    cfgSkel D r₀ tl CB = ⟨k + 1, Cs, lab, ex, s4⟩ with hT
  have hD : ∀ v ∈ S, Covers.deg v ≤ D := fun v hv => windowVecs_deg hv
  have hrep : ∀ CB ∈ T, Nonempty (CfgRep S tl D r₀ CB (k + 1) Cs lab ex s4) := fun CB h =>
    cfg_rep hD (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2
  set Rf : ∀ CB ∈ T, CfgRep S tl D r₀ CB (k + 1) Cs lab ex s4 := fun CB h =>
    Classical.choice (hrep CB h) with hRf
  set g : (Finset (Fin N → ℕ) × Finset (Fin N → ℕ)) →
      (Fin (k + 1) → ℕ) × (Fin (k + 1) → (Fin N → ℕ) × ℕ) := fun CB =>
    if h : CB ∈ T then ((Rf CB h).labs, (Rf CB h).cont) else (0, 0) with hg
  set F : (Fin (k + 1) → ℕ) × (Fin (k + 1) → (Fin N → ℕ) × ℕ) → ℝ≥0∞ := fun y =>
    if ConsC E lr smax cd (k + 1) y.1 y.2 then
      (J.A (y.1 (Fin.last k))).indicator 1 ω *
        FfullC J E lr cd Jw G A Eu k ω (Fin.init y.1) (y.1 (Fin.last k)) y.2
          (J.q (y.1 (Fin.last k)) ω) else 0 with hF
  have hgT : ∀ CB (h : CB ∈ T), g CB = ((Rf CB h).labs, (Rf CB h).cont) := fun CB h => by
    simp only [hg, dif_pos h]
  have hF1 : ∀ CB ∈ T, 1 ≤ F (g CB) := by
    intro CB hCB
    rw [hgT CB hCB]
    obtain ⟨hE, hlr⟩ := hfix CB (Rf CB hCB)
    exact CfgRep.one_le_term J G hG Jw A Eu (Rf CB hCB) τ hE hlr hτ1 hq hsmax hτ hω
  have hmemC : ∀ CB ∈ T, (g CB).2 ∈ contents (k + 1) N D Dmax X₀ := by
    intro CB hCB
    rw [hgT CB hCB, contents, Fintype.mem_piFinset]
    intro i
    have hel := tailOf_mem ((Rf CB hCB).memS i)
    obtain ⟨hel1, -⟩ := Finset.mem_filter.mp hel
    obtain ⟨hv, hd⟩ := Finset.mem_product.mp hel1
    refine Finset.mem_product.mpr ⟨?_, hd⟩
    rw [Fintype.mem_piFinset] at hv ⊢
    intro n
    have := hv n
    simp only [CfgRep.cont, Finset.mem_range] at this ⊢
    split_ifs
    · omega
    · exact this
  have hinj : Set.InjOn g T := by
    intro CB hCB CB' hCB' h
    rw [hgT CB hCB, hgT CB' hCB'] at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact CfgRep.cfg_inj (Rf CB hCB) (Rf CB' hCB') (hfix CB _).1 (hfix CB' _).1 h1
      (fun y n => by rw [h2])
  have hcount : cfgSkelCount D r₀ 0 0 tl S (k + 1) Cs lab ex s4 = ∑ CB ∈ T, (1 : ℝ≥0∞) := by
    simp [cfgSkelCount, hT]
  rw [hcount]
  unfold ZSC
  calc ∑ CB ∈ T, (1 : ℝ≥0∞) ≤ ∑ CB ∈ T, F (g CB) := Finset.sum_le_sum hF1
    _ = ∑ y ∈ T.image g, F y := (Finset.sum_image (f := F) hinj).symm
    _ ≤ ∑ y ∈ T.image (fun CB => (g CB).1) ×ˢ contents (k + 1) N D Dmax X₀, F y := by
        refine Finset.sum_le_sum_of_subset fun y hy => ?_
        obtain ⟨CB, hCB, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hCB, hmemC CB hCB⟩
    _ = ∑ lab ∈ T.image (fun CB => (g CB).1), ∑ c ∈ contents (k + 1) N D Dmax X₀,
          F (lab, c) := Finset.sum_product _ _ _
    _ ≤ ∑' lab, ∑ c ∈ contents (k + 1) N D Dmax X₀, F (lab, c) := ENNReal.sum_le_tsum _

end Count

section Bound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`CoverSkeletonBound` for every cover skeleton** (Proposition 6.19 via Lemma A.5 +
Theorem A.10 with the cover `C`), in the window model over a jitter process: for every
skeleton `(r, C, lab, ex, s4)` there is a join list `l` with `∑ l = |C|` and
`#{t : j_t = 0} ≤ |R|` such that `E[X; Good] ≤ θ^r δ^r ∏_i τ_i^{-e_i} z^{-|R|} Fin(A, l, Eu)`,
under the hypotheses of `skeletonBound_all` and the window bound `J ⊆ [z, ∞)` (the rows of
`R` cost `vol(J)/z` each). -/
theorem coverSkeletonBound_all {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) (r₀ : ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ)
    {z : ℝ} (hz : 0 < z) (hJz : Jw ⊆ Set.Ici z)
    (X₀ D Dmax : ℕ) {A Eu : ℝ} (hEu : 0 < Eu) (htail : tailSum Dmax X₀ ≤ Eu)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    {r : ℕ} (τ : Fin r → ℝ) (hτ1 : ∀ j, 1 ≤ τ j)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (Cs : Finset (Fin r)) (hCs : Cs.Nonempty) (lab : Finset (Fin (Cs.card * D)))
    (ex : Fin r → Fin r → ℕ) (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) :
    ∃ l : List ℕ, l.sum = Cs.card ∧ l.count 0 ≤ r - Cs.card ∧
      CoverSkeletonBound P Good r θ δ A Eu z τ (exExcess ex) (r - Cs.card) l
        (fun ω => cfgSkelCount D r₀ 0 0 (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
          (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) r Cs lab ex s4) := by
  by_cases href : ∃ ω, ∃ CB ∈ configs r₀ 0 0
      (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw),
      cfgSkel D r₀ (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) CB =
        ⟨r, Cs, lab, ex, s4⟩
  swap
  · -- no configuration has this skeleton: the count vanishes
    have h0 : ∀ ω, cfgSkelCount D r₀ 0 0 (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
        (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) r Cs lab ex s4 = 0 := by
      intro ω
      unfold cfgSkelCount
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun CB hCB hs =>
        href ⟨ω, CB, hCB, hs⟩)]
      simp
    have hc : Cs.card ≠ 0 := Finset.card_ne_zero.mpr hCs
    refine ⟨[Cs.card], by simp, by simp [hc], ?_⟩
    unfold CoverSkeletonBound
    simp only [h0, MeasureTheory.lintegral_zero]
    exact zero_le _
  obtain ⟨ω₀, CB₀, hCB₀, hs₀⟩ := href
  obtain ⟨R₀⟩ := cfg_rep (fun v hv => windowVecs_deg hv) hCB₀ hs₀
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by have := R₀.hr1; omega⟩
  set Ecov : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ := fun y i => R₀.T y (R₀.p i) with hEcov
  set lr := R₀.lr with hlr
  have hE : (Ereal Ecov).det ≠ 0 := ereal_det_ne R₀.inv
  set cd := covData Ecov Cs lr τ ex s4 with hcd
  have hfix : ∀ ω CB, ∀ R : CfgRep (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) D r₀ CB (k + 1) Cs lab ex s4,
      (∀ y i, R.T y (R.p i) = Ecov y i) ∧ R.lr = lr := fun ω CB R =>
    ⟨(rep_unique R R₀).2.1, (rep_unique R R₀).2.2⟩
  refine ⟨joinC Ecov Cs lr, joinC_sum Ecov hE Cs lr R₀.lrsum,
    joinC_count Ecov hE Cs lr R₀.lrpos R₀.lrsum, ?_⟩
  unfold CoverSkeletonBound
  have h1 : ∫⁻ ω in Good, cfgSkelCount D r₀ 0 0
      (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) (k + 1) Cs lab ex s4 ∂P ≤
      ∫⁻ ω, ZSC (N := N) J Ecov lr cd Jw D Dmax X₀ smax G A Eu k ω ∂P := by
    refine le_trans ?_ (setLIntegral_le_lintegral Good _)
    refine setLIntegral_mono' hGood fun ω hω => ?_
    exact cfgCount_le_ZSC J G hG Jw A Eu Ecov lr τ hτ1 hq hsmax hτ ω (hGoodG hω) (hfix ω)
  have hWc : 0 ≤ cd.Wc := by
    simp only [hcd, covData]
    exact Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (by linarith [hτ1 j])) _
  have h2 := multiRunC_chain (N := N) (J := J) (E := Ecov) (l := lr) (cd := cd) (Jw := Jw)
    (D := D) (Dmax := Dmax) (X₀ := X₀) (smax := smax) (G := G) (A := A) (Eu := Eu) hJw hq hEu
    hE R₀.lrpos R₀.lrsum (Nat.succ_pos k) rfl hGm hG hS3 hJ hδ hz hJz htail hWc
  calc _ ≤ ∫⁻ ω, ZSC (N := N) J Ecov lr cd Jw D Dmax X₀ smax G A Eu k ω ∂P := h1
    _ ≤ θE ^ (k + 1) * ENNReal.ofReal (finG A cd.lg Eu * δ ^ (k + 1) *
          z⁻¹ ^ (k + 1 - cd.Cd.card) * cd.Wc) := h2
    _ ≤ ENNReal.ofReal θ ^ (k + 1) * ENNReal.ofReal (finG A cd.lg Eu * δ ^ (k + 1) *
          z⁻¹ ^ (k + 1 - cd.Cd.card) * cd.Wc) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow hθ0, ← ENNReal.ofReal_mul (pow_nonneg hθ0 _)]
        congr 1
        simp only [hcd, covData]
        ring

/-- **The input `hcov` of `theorem_6_23a_model` / `prop_6_11_window`** for the window model over
a jitter process (`dec = decOf J`, `q = qOf J`): `CoverSkeletonBound` for every window, every
`r < r₀` and every skeleton `(C, lab, ex, s4)` with `C ∈ CSet r j`, from
`coverSkeletonBound_all`. -/
theorem hcov_window {ι : Type*} {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) (r₀ : ℕ)
    (W : Finset ι) (Jw : ι → Set ℝ) (hJw : ∀ Jx ∈ W, MeasurableSet (Jw Jx)) (aw : ι → ℝ)
    {δ : ℝ} (hJ : ∀ Jx ∈ W, Jw Jx ⊆ Set.Ico (aw Jx) (aw Jx + δ)) (hδ : 0 ≤ δ) {z : ℝ}
    (hz : 0 < z) (hJz : ∀ Jx ∈ W, Jw Jx ⊆ Set.Ici z) (X₀ D Dmax : ℕ) {A Eu : ℝ}
    (hEu : 0 < Eu) (htail : tailSum Dmax X₀ ≤ Eu)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ Jx ∈ W, ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw Jx, J.q n ω ≤ y →
      (n : ℕ) ≤ smax)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    (τ : (r : ℕ) → Fin r → ℝ) (hτ1 : ∀ r, ∀ i, 1 ≤ τ r i)
    (hτ : ∀ r < r₀, ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ r j ≤ J.q n ω) :
    ∀ j, ∀ Jx ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r θ δ A Eu z (τ r) (exExcess ex) (r - C.card) l
          (fun ω => cfgSkelCount D r₀ 0 0
            (tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax (Jw Jx))
            (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax (Jw Jx)) r C lab ex s4) :=
  fun _ Jx hJx r hr C hC lab ex s4 _ =>
    coverSkeletonBound_all J hθ0 hθ hGood G hGm hG smax hGoodG r₀ (hJw Jx hJx) (hJ Jx hJx) hδ
      hz (hJz Jx hJx) X₀ D Dmax hEu htail hq (hsmax Jx hJx) hS3 (τ r) (hτ1 r) (hτ r hr) C
      (Finset.mem_filter.mp hC).2.1 lab ex s4

end Bound

end RankFull.Config
