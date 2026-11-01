module

public import RequestProject.Beurling.RankFull.BlockBound
public import RequestProject.Beurling.RankFull.FacShift
public import RequestProject.Beurling.RankFull.EulerOneRun

/-!
# Lemma A.6 (S3)(a) for the realised slots: the block bound over the contents of a block

`BlockBound.lean` proves (S3)(a) for an abstract list `p 0, p 1, …` of the realised primes of the
block range, in slot order. Here it is transported to the realised slots `Fin N` of the window
model:
* the slot-indexed Euler product `EuS u = Eu ∏_{decided g < u} (1 - 1/q_g)^{-1}`;
* `RankFull.blockSets_le` : the sum over the non-empty sets `S` of decided slots `≥ b`
  (`χ(u_S) Φ_{t-1}(u_S) ∏_{g ∈ S} ((1 - 1/q_g)^{-K} - 1)`, `u_S` the first slot after the latest
  slot of `S`) is at most `Φ_t(b)`;
* `RankFull.blockSum_le` : **(S3)(a) with variable content**: the sum over every non-empty content
  of the block (the slots, and the exponent column of each slot in all `K` rows, the columns
  being in the span of the stage pivots), with weight `∏_g q_g^{-a_g}`, `a_g` the total exponent,
  is at most `Φ_t(b)`. The columns are determined by their entries in the stage rows `R≤t`
  (`exists_rows_inj`), so `K_t = |R≤t|` chain rows suffice.
-/

@[expose] public section

open Finset
open scoped Classical

namespace RankFull

variable {N : ℕ}

/-- The slot-indexed Euler product `Eu_s(u) = Eu ∏_{decided g < u} (1 - 1/q_g)^{-1}`. -/
noncomputable def EuS (ok : Fin N → Prop) (q : Fin N → ℝ) (Eu : ℝ) (u : ℕ) : ℝ :=
  Eu * ∏ g ∈ univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < u), (1 - (q g)⁻¹)⁻¹

/-- The block indicator `χ(u) = 1(u ≤ s_max) 1(G_{<u})`. -/
noncomputable def chiB (smax : ℕ) (Gp : ℕ → Prop) (u : ℕ) : ℝ :=
  if u ≤ smax ∧ Gp u then 1 else 0

lemma EuS_pos {ok : Fin N → Prop} {q : Fin N → ℝ} (hq : ∀ g, ok g → 1 < q g) {Eu : ℝ}
    (hEu : 0 < Eu) (u : ℕ) : 0 < EuS ok q Eu u :=
  mul_pos hEu (Finset.prod_pos fun g hg =>
    inv_pos.mpr (one_sub_inv_pos (hq g (Finset.mem_filter.mp hg).2.1)))

section Relabel

variable [NeZero N] (Dset : Finset (Fin N))

/-- The `n`-th slot of `Dset` (in slot order). -/
noncomputable def nth (n : ℕ) : Fin N :=
  if h : n < Dset.card then Dset.orderEmbOfFin rfl ⟨n, h⟩ else 0

lemma nth_mem {n : ℕ} (hn : n < Dset.card) : nth Dset n ∈ Dset := by
  simp only [nth, dif_pos hn]; exact Finset.orderEmbOfFin_mem _ _ _

lemma nth_strictMonoOn : StrictMonoOn (nth Dset) (Set.Iio Dset.card) := by
  intro a ha b hb hab
  simp only [nth, dif_pos (show a < Dset.card from ha), dif_pos (show b < Dset.card from hb)]
  exact (Dset.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hab)

lemma nth_surj {g : Fin N} (hg : g ∈ Dset) : ∃ n < Dset.card, nth Dset n = g := by
  have : g ∈ Set.range (Dset.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hg
  obtain ⟨i, hi⟩ := this
  exact ⟨i, i.isLt, by simp [nth, i.isLt, hi]⟩

/-- The elements of `Dset` below its `n`-th slot are its first `n` slots. -/
lemma filter_lt_nth {n : ℕ} (hn : n < Dset.card) :
    Dset.filter (· < nth Dset n) = (range n).image (nth Dset) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hg, hlt⟩
    obtain ⟨m, hm, rfl⟩ := nth_surj Dset hg
    refine ⟨m, ?_, rfl⟩
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with h | rfl
    · exact absurd hlt (not_lt.mpr (nth_strictMonoOn Dset hn hm h).le)
    · exact lt_irrefl _ hlt
  · rintro ⟨m, hm, rfl⟩
    exact ⟨nth_mem Dset (by omega), nth_strictMonoOn Dset (by simp; omega) hn hm⟩

lemma filter_le_nth {n : ℕ} (hn : n < Dset.card) :
    Dset.filter (fun g : Fin N => (g : ℕ) < (nth Dset n : ℕ) + 1) =
      (range (n + 1)).image (nth Dset) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hg, hlt⟩
    obtain ⟨m, hm, rfl⟩ := nth_surj Dset hg
    refine ⟨m, ?_, rfl⟩
    by_contra h
    push_neg at h
    have := nth_strictMonoOn Dset hn hm (by omega)
    have := Fin.lt_def.mp this
    omega
  · rintro ⟨m, hm, rfl⟩
    refine ⟨nth_mem Dset (by omega), ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | rfl
    · have := Fin.lt_def.mp (nth_strictMonoOn Dset (by simp; omega) hn h); omega
    · omega

lemma nth_injOn : Set.InjOn (nth Dset) (Set.Iio Dset.card) :=
  (nth_strictMonoOn Dset).injOn

end Relabel

section BlockSets

variable [NeZero N]

lemma EuS_nth_succ (ok : Fin N → Prop) (q : Fin N → ℝ) (Eu : ℝ) (b : ℕ) {n : ℕ}
    (hn : n < (univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ)).card) :
    EuS ok q Eu ((nth (univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ)) n : ℕ) + 1) =
      euAt (EuS ok q Eu b) (fun i => q (nth (univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ)) i))
        (n + 1) := by
  set Dset := univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ) with hD
  have hmem := nth_mem Dset hn
  have hb : b ≤ (nth Dset n : ℕ) := (Finset.mem_filter.mp hmem).2.2
  have hsplit : univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < (nth Dset n : ℕ) + 1) =
      univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < b) ∪
        Dset.filter (fun g : Fin N => (g : ℕ) < (nth Dset n : ℕ) + 1) := by
    ext g
    have hgD : g ∈ Dset ↔ ok g ∧ b ≤ (g : ℕ) := by simp [hD]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hgD]
    constructor
    · rintro ⟨hg, hlt⟩
      by_cases hgb : (g : ℕ) < b
      · exact Or.inl ⟨hg, hgb⟩
      · exact Or.inr ⟨⟨hg, by omega⟩, hlt⟩
    · rintro (⟨hg, hlt⟩ | ⟨⟨hg, -⟩, hlt⟩)
      · exact ⟨hg, by omega⟩
      · exact ⟨hg, hlt⟩
  have hdisj : Disjoint (univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < b))
      (Dset.filter (fun g : Fin N => (g : ℕ) < (nth Dset n : ℕ) + 1)) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  unfold EuS euAt
  rw [hsplit, Finset.prod_union hdisj, filter_le_nth Dset hn,
    Finset.prod_image (fun a ha b' hb' h => nth_injOn Dset
      (show a < Dset.card by simp at ha; omega) (show b' < Dset.card by simp at hb'; omega) h)]
  ring

lemma sup_image_nth (Dset : Finset (Fin N)) {S' : Finset ℕ} (hS' : S' ⊆ range Dset.card)
    (hne : S'.Nonempty) :
    (S'.image (nth Dset)).sup (fun g => (g : ℕ) + 1) = (nth Dset (S'.sup id) : ℕ) + 1 := by
  have hmax : S'.sup id ∈ S' := by
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S' id hne
    have : S'.sup id = m := le_antisymm (Finset.sup_le fun x hx => hmax x hx)
      (Finset.le_sup (f := id) hm)
    rw [this]; exact hm
  apply le_antisymm
  · refine Finset.sup_le fun g hg => ?_
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
    have h1 : n ≤ S'.sup id := Finset.le_sup (f := id) hn
    rcases h1.lt_or_eq with h1 | h1
    · have := Fin.lt_def.mp (nth_strictMonoOn Dset (by simpa using hS' hn)
        (by simpa using hS' hmax) h1)
      omega
    · rw [h1]
  · exact Finset.le_sup (f := fun g : Fin N => (g : ℕ) + 1) (Finset.mem_image_of_mem _ hmax)

/-- **(S3)(a) over the realised slots** (the sets of slots of a block content). -/
theorem blockSets_le (ok : Fin N → Prop) (q : Fin N → ℝ) (hq : ∀ g, ok g → 1 < q g) {Eu : ℝ}
    (hEu : 0 < Eu) (b smax : ℕ) (Gp : ℕ → Prop) {A : ℝ}
    (hS3 : ∀ u ≤ smax, Gp u → EuS ok q Eu u ≤ A) {K' m j : ℕ} (hK : K' = m + j)
    {Gf : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ Gf y) (hGanti : AntitoneOn Gf (Set.Ioi 0)) :
    ∑ S ∈ (univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ)).powerset with S.Nonempty,
        chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
          (∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ K' - 1)) *
          (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
            EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m) ≤
      Gnext A K' j Gf (EuS ok q Eu b) / EuS ok q Eu b ^ K' := by
  set Dset := univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ) with hD
  set M := Dset.card with hM
  set p : ℕ → ℝ := fun i => q (nth Dset i) with hp
  set χ : ℕ → ℝ := fun i => chiB smax Gp ((nth Dset i : ℕ) + 1) with hχ
  have hpq : ∀ i < M, 1 < p i := fun i hi =>
    hq _ (Finset.mem_filter.mp (nth_mem Dset hi)).2.1
  have hχ0 : ∀ i, 0 ≤ χ i := fun i => by simp only [hχ, chiB]; split_ifs <;> norm_num
  have hχ1 : ∀ i, χ i ≤ 1 := fun i => by simp only [hχ, chiB]; split_ifs <;> norm_num
  have hχA : ∀ i < M, 0 < χ i → euAt (EuS ok q Eu b) p (i + 1) ≤ A := by
    intro i hi hpos
    simp only [hχ, chiB] at hpos
    split_ifs at hpos with h
    · rw [hp, ← EuS_nth_succ ok q Eu b hi]
      exact hS3 _ h.1 h.2
    · exact absurd hpos (lt_irrefl 0)
  have hbb := block_bound hK (EuS_pos hq hEu b) hpq hχ0 hχ1 hχA hG0 hGanti
  refine le_of_eq_of_le ?_ hbb
  symm
  refine Finset.sum_nbij' (fun S' => S'.image (nth Dset))
    (fun S => (range M).filter fun n => nth Dset n ∈ S) ?_ ?_ ?_ ?_ ?_
  · intro S' hS'
    obtain ⟨hS'1, hS'2⟩ := Finset.mem_filter.mp hS'
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun g hg => ?_, hS'2.image _⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
    exact nth_mem Dset (by simpa using Finset.mem_powerset.mp hS'1 hn)
  · intro S hS
    obtain ⟨hS1, ⟨g, hg⟩⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    obtain ⟨n, hn, rfl⟩ := nth_surj Dset (Finset.mem_powerset.mp hS1 hg)
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hg⟩⟩
  · intro S' hS'
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, m, hm, hmn⟩
      have hmM : m < M := by simpa using hsub hm
      rw [← nth_injOn Dset hmM hn hmn]; exact hm
    · intro hn
      exact ⟨by simpa using hsub hn, n, hn, rfl⟩
  · intro S hS
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨n, ⟨-, hn⟩, rfl⟩; exact hn
    · intro hg
      obtain ⟨n, hn, rfl⟩ := nth_surj Dset (hsub hg)
      exact ⟨n, ⟨hn, hg⟩, rfl⟩
  · intro S' hS'
    obtain ⟨hS'1, hne⟩ := Finset.mem_filter.mp hS'
    have hsub := Finset.mem_powerset.mp hS'1
    have hsupM : S'.sup id < M := by
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S' id hne
      have : S'.sup id = m := le_antisymm (Finset.sup_le fun x hx => hmax x hx)
        (Finset.le_sup (f := id) hm)
      rw [this]; simpa using hsub hm
    rw [sup_image_nth Dset hsub hne, Finset.prod_image (fun a ha b' hb' h =>
      nth_injOn Dset (show a < M by simpa using hsub ha) (show b' < M by simpa using hsub hb') h),
      EuS_nth_succ ok q Eu b hsupM]

end BlockSets

section BlockSum

variable {K : ℕ}

/-- The exponent vectors of one slot in the stage rows `R` (entries `≤ D`). -/
noncomputable def VR (R : Finset (Fin K)) (D : ℕ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun y => if y ∈ R then range (D + 1) else {0}

lemma geomR_le (R : Finset (Fin K)) (D : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ v ∈ (VR R D).filter (· ≠ 0), x ^ (∑ y, v y) ≤ ((1 - x)⁻¹) ^ R.card - 1 := by
  have h0 : (0 : Fin K → ℕ) ∈ VR R D := by
    rw [VR, Fintype.mem_piFinset]; intro y; split_ifs <;> simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (VR R D) (· ≠ 0)
    (fun v => x ^ (∑ y, v y))
  have hzero : ∑ v ∈ (VR R D).filter (fun v => ¬ v ≠ 0), x ^ (∑ y, v y) = 1 := by
    have : (VR R D).filter (fun v => ¬ v ≠ 0) = {0} := by
      ext v; simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro rfl; exact ⟨h0, rfl⟩
    rw [this, Finset.sum_singleton]; simp
  have hall : ∑ v ∈ VR R D, x ^ (∑ y, v y) =
      ∏ y : Fin K, ∑ e ∈ (if y ∈ R then range (D + 1) else {0}), x ^ e := by
    rw [VR, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  have hprod : ∏ y : Fin K, ∑ e ∈ (if y ∈ R then range (D + 1) else {0}), x ^ e ≤
      ((1 - x)⁻¹) ^ R.card := by
    rw [← Finset.prod_const, ← Finset.prod_filter_mul_prod_filter_not univ (· ∈ R)]
    have h1 : ∏ y ∈ univ.filter (· ∈ R), ∑ e ∈ (if y ∈ R then range (D + 1) else {0}), x ^ e ≤
        ∏ y ∈ univ.filter (· ∈ R), (1 - x)⁻¹ := by
      refine Finset.prod_le_prod₀ (fun y _ => Finset.sum_nonneg fun e _ => pow_nonneg hx0 _)
        fun y hy => ?_
      rw [if_pos (Finset.mem_filter.mp hy).2]
      exact RankFull.Config.geom_le hx0 hx1 D
    have h2 : ∏ y ∈ univ.filter (fun y => ¬ y ∈ R),
        ∑ e ∈ (if y ∈ R then range (D + 1) else {0}), x ^ e = 1 := by
      refine Finset.prod_eq_one fun y hy => ?_
      rw [if_neg (Finset.mem_filter.mp hy).2]; simp
    rw [h2, mul_one]
    have hfilt : univ.filter (· ∈ R) = R := by ext; simp
    rw [hfilt] at h1
    rw [hfilt]
    simpa using h1
  linarith

/-- A sum through an injective map into a set with non-negative terms. -/
lemma sum_comp_le_of_injOn {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (φ : ι → κ) (hφ : ∀ i ∈ s, φ i ∈ t) (hinj : Set.InjOn φ s) (F : κ → ℝ)
    (hF : ∀ k ∈ t, 0 ≤ F k) : ∑ i ∈ s, F (φ i) ≤ ∑ k ∈ t, F k := by
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k hk _ => hF k hk)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  exact hφ i hi

/-- The contents of a block: the exponent of each slot in each row (entries `≤ D`). -/
noncomputable def Wset (K N D : ℕ) : Finset (Fin K → Fin N → ℕ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => range (D + 1)

/-- The slots of a block content. -/
noncomputable def suppW {K : ℕ} (W : Fin K → Fin N → ℕ) : Finset (Fin N) :=
  univ.filter fun g => ∃ y, W y g ≠ 0

/-- The first slot after the latest slot of a content (`u_t`). -/
noncomputable def uW {K : ℕ} (W : Fin K → Fin N → ℕ) : ℕ :=
  (suppW W).sup fun g => (g : ℕ) + 1

/-- The exponent column of a slot. -/
def colW {K : ℕ} (W : Fin K → Fin N → ℕ) (g : Fin N) : Fin K → ℕ := fun y => W y g

/-- An admissible non-empty block content: decided slots `≥ b`, columns in `Col`. -/
def BlockOK {K : ℕ} (ok : Fin N → Prop) (b : ℕ) (Col : Set (Fin K → ℕ))
    (W : Fin K → Fin N → ℕ) : Prop :=
  (suppW W).Nonempty ∧ ∀ g ∈ suppW W, ok g ∧ b ≤ (g : ℕ) ∧ colW W g ∈ Col

lemma mem_suppW {K : ℕ} {W : Fin K → Fin N → ℕ} {g : Fin N} :
    g ∈ suppW W ↔ ∃ y, W y g ≠ 0 := by simp [suppW]

/-- The contents with a given set of slots, through their stage-row entries. -/
theorem fiber_le {K : ℕ} (D : ℕ) (R : Finset (Fin K)) (Col : Set (Fin K → ℕ))
    (hinj : ∀ w ∈ Col, ∀ w' ∈ Col, (∀ y ∈ R, w y = w' y) → w = w') (h0 : (0 : Fin K → ℕ) ∈ Col)
    (S : Finset (Fin N)) (q : Fin N → ℝ) (hq : ∀ g ∈ S, 1 < q g) :
    ∑ W ∈ (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col),
        ∏ g, (q g)⁻¹ ^ (∑ y, W y g) ≤ ∏ g ∈ S, (((1 - (q g)⁻¹)⁻¹) ^ R.card - 1) := by
  set φ : (Fin K → Fin N → ℕ) → (Fin N → Fin K → ℕ) := fun W g =>
    if g ∈ S then (fun y => if y ∈ R then W y g else 0) else 0 with hφ
  set hfun : Fin N → (Fin K → ℕ) → ℝ := fun g v =>
    if g ∈ S then (q g)⁻¹ ^ (∑ y, v y) else 1 with hh
  set TS : Finset (Fin N → Fin K → ℕ) := Fintype.piFinset fun g =>
    if g ∈ S then (VR R D).filter (· ≠ 0) else {0} with hTS
  set fib := (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col) with hfib
  have hqinv : ∀ g ∈ S, 0 < (q g)⁻¹ ∧ (q g)⁻¹ ≤ 1 := fun g hg =>
    ⟨inv_pos.mpr (by linarith [hq g hg]), inv_le_one_of_one_le₀ (hq g hg).le⟩
  -- (i) the weight is at most the stage-row weight
  have hw : ∀ W ∈ fib, ∏ g, (q g)⁻¹ ^ (∑ y, W y g) ≤ ∏ g, hfun g (φ W g) := by
    intro W hW
    obtain ⟨-, hsupp, -⟩ := Finset.mem_filter.mp hW
    refine Finset.prod_le_prod₀ (fun g _ => ?_) (fun g _ => ?_)
    · by_cases hg : g ∈ S
      · exact pow_nonneg (hqinv g hg).1.le _
      · have : ∀ y, W y g = 0 := by
          intro y; by_contra h
          exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        simp [this]
    · by_cases hg : g ∈ S
      · simp only [hh, hφ, if_pos hg]
        refine pow_le_pow_of_le_one (hqinv g hg).1.le (hqinv g hg).2 ?_
        refine Finset.sum_le_sum fun y _ => ?_
        split_ifs <;> omega
      · have : ∀ y, W y g = 0 := by
          intro y; by_contra h
          exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        simp [hh, hg, this]
  -- (ii) the map to the stage-row entries is injective, into `TS`
  have hmaps : ∀ W ∈ fib, φ W ∈ TS := by
    intro W hW
    obtain ⟨hWs, hsupp, hcol⟩ := Finset.mem_filter.mp hW
    rw [hTS, Fintype.mem_piFinset]
    intro g
    by_cases hg : g ∈ S
    · simp only [hφ, if_pos hg]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [VR, Fintype.mem_piFinset]
        intro y
        split_ifs with hy
        · have := Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hWs y) g
          exact this
        · simp
      · intro h0'
        have hg' : g ∈ suppW W := hsupp ▸ hg
        obtain ⟨y, hy⟩ := mem_suppW.mp hg'
        have := hinj (colW W g) (hcol g hg) 0 h0 (fun y' hy' => by
          have := congrFun h0' y'
          simpa [colW, hy'] using this)
        exact hy (congrFun this y)
    · simp [hφ, hg]
  have hinjφ : Set.InjOn φ fib := by
    intro W hW W' hW' h
    obtain ⟨-, hsupp, hcol⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hW)
    obtain ⟨-, hsupp', hcol'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hW')
    funext y g
    by_cases hg : g ∈ S
    · have := hinj (colW W g) (hcol g hg) (colW W' g) (hcol' g hg) (fun y' hy' => by
        have := congrFun (congrFun h g) y'
        simpa [colW, hφ, hg, hy'] using this)
      exact congrFun this y
    · have h1 : W y g = 0 := by
        by_contra h1; exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h1⟩)
      have h2 : W' y g = 0 := by
        by_contra h2; exact hg (hsupp' ▸ mem_suppW.mpr ⟨y, h2⟩)
      rw [h1, h2]
  calc ∑ W ∈ fib, ∏ g, (q g)⁻¹ ^ (∑ y, W y g)
      ≤ ∑ W ∈ fib, ∏ g, hfun g (φ W g) := Finset.sum_le_sum hw
    _ ≤ ∑ V ∈ TS, ∏ g, hfun g (V g) := by
        refine sum_comp_le_of_injOn fib TS φ hmaps hinjφ (fun V => ∏ g, hfun g (V g))
          fun V _ => Finset.prod_nonneg fun g _ => ?_
        simp only [hh]; split_ifs with hg
        · exact pow_nonneg (hqinv g hg).1.le _
        · exact zero_le_one
    _ = ∏ g, ∑ v ∈ (if g ∈ S then (VR R D).filter (· ≠ 0) else {0}), hfun g v := by
        rw [hTS, Finset.prod_univ_sum]
    _ = ∏ g ∈ S, ∑ v ∈ (VR R D).filter (· ≠ 0), (q g)⁻¹ ^ (∑ y, v y) := by
        rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ S)]
        have h2 : ∏ g ∈ univ.filter (fun g => ¬ g ∈ S),
            ∑ v ∈ (if g ∈ S then (VR R D).filter (· ≠ 0) else {0}), hfun g v = 1 :=
          Finset.prod_eq_one fun g hg => by
            rw [if_neg (Finset.mem_filter.mp hg).2]; simp [hh, (Finset.mem_filter.mp hg).2]
        rw [h2, mul_one]
        have hfilt : univ.filter (· ∈ S) = S := by ext; simp
        rw [hfilt]
        refine Finset.prod_congr rfl fun g hg => ?_
        rw [if_pos hg]
        exact Finset.sum_congr rfl fun v _ => by simp [hh, hg]
    _ ≤ ∏ g ∈ S, (((1 - (q g)⁻¹)⁻¹) ^ R.card - 1) := by
        refine Finset.prod_le_prod₀ (fun g hg => Finset.sum_nonneg fun v _ =>
          pow_nonneg (hqinv g hg).1.le _) fun g hg => ?_
        exact geomR_le R D (hqinv g hg).1.le (inv_lt_one_of_one_lt₀ (hq g hg))

/-- **Lemma A.6 (S3)(a) with variable content over the realised slots**: the sum over every
non-empty content of the block (slots `≥ b`, decided, columns in `Col`) of
`χ(u_W) Φ_{t-1}(u_W) ∏_g q_g^{-a_g}` is at most `Φ_t(b)`, when `Col` is determined by the
stage rows `R` (`|R| = K_t = m + j`). -/
theorem blockSum_le [NeZero N] {K : ℕ} (D : ℕ) (R : Finset (Fin K)) (Col : Set (Fin K → ℕ))
    (hinj : ∀ w ∈ Col, ∀ w' ∈ Col, (∀ y ∈ R, w y = w' y) → w = w') (h0 : (0 : Fin K → ℕ) ∈ Col)
    (ok : Fin N → Prop) (q : Fin N → ℝ) (hq : ∀ g, ok g → 1 < q g) {Eu : ℝ} (hEu : 0 < Eu)
    (b smax : ℕ) (Gp : ℕ → Prop) {A : ℝ} (hS3 : ∀ u ≤ smax, Gp u → EuS ok q Eu u ≤ A)
    {m j : ℕ} (hK : R.card = m + j) {Gf : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ Gf y)
    (hGanti : AntitoneOn Gf (Set.Ioi 0)) :
    ∑ W ∈ Wset K N D, (if BlockOK ok b Col W then
        chiB smax Gp (uW W) * (Gf (EuS ok q Eu (uW W)) / EuS ok q Eu (uW W) ^ m) *
          ∏ g, (q g)⁻¹ ^ (∑ y, W y g) else 0) ≤
      Gnext A R.card j Gf (EuS ok q Eu b) / EuS ok q Eu b ^ R.card := by
  set Dset := univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ) with hD
  set T := Dset.powerset.filter (·.Nonempty) with hT
  set F : (Fin K → Fin N → ℕ) → ℝ := fun W =>
    chiB smax Gp (uW W) * (Gf (EuS ok q Eu (uW W)) / EuS ok q Eu (uW W) ^ m) *
      ∏ g, (q g)⁻¹ ^ (∑ y, W y g) with hF
  have hΦ0 : ∀ u, 0 ≤ chiB smax Gp u * (Gf (EuS ok q Eu u) / EuS ok q Eu u ^ m) := by
    intro u
    have hE := EuS_pos hq hEu u
    refine mul_nonneg (by unfold chiB; split_ifs <;> norm_num)
      (div_nonneg (hG0 _ hE) (pow_nonneg hE.le _))
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (g := suppW) (t := T) (fun W hW => by
    obtain ⟨-, hne, hall⟩ := Finset.mem_filter.mp hW
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun g hg => ?_, hne⟩
    obtain ⟨h1, h2, -⟩ := hall g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)]
  have hfib : ∀ S ∈ T, ∑ W ∈ ((Wset K N D).filter (BlockOK ok b Col)).filter
      (fun W => suppW W = S), F W ≤
      chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
        (∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1)) *
        (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
          EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m) := by
    intro S hS
    obtain ⟨hSD, hne⟩ := Finset.mem_filter.mp hS
    have hSq : ∀ g ∈ S, 1 < q g := fun g hg =>
      hq g (Finset.mem_filter.mp (Finset.mem_powerset.mp hSD hg)).2.1
    have hsub : ((Wset K N D).filter (BlockOK ok b Col)).filter (fun W => suppW W = S) ⊆
        (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col) := by
      intro W hW
      simp only [Finset.mem_filter] at hW ⊢
      obtain ⟨⟨hWs, -, hall⟩, hsupp⟩ := hW
      exact ⟨hWs, hsupp, fun g hg => (hall g (hsupp ▸ hg)).2.2⟩
    have hval : ∀ W ∈ ((Wset K N D).filter (BlockOK ok b Col)).filter (fun W => suppW W = S),
        F W = (chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
          (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
            EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m)) * ∏ g, (q g)⁻¹ ^ (∑ y, W y g) := by
      intro W hW
      have hsupp := (Finset.mem_filter.mp hW).2
      simp only [hF, uW, hsupp]
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
    have hfl := fiber_le D R Col hinj h0 S q hSq
    have hle : ∑ W ∈ ((Wset K N D).filter (BlockOK ok b Col)).filter (fun W => suppW W = S),
        ∏ g, (q g)⁻¹ ^ (∑ y, W y g) ≤ ∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun W hW _ =>
        Finset.prod_nonneg fun g _ => ?_) hfl
      by_cases hg : g ∈ S
      · exact pow_nonneg (inv_nonneg.mpr (by linarith [hSq g hg])) _
      · have hsupp := (Finset.mem_filter.mp hW).2.1
        have : ∑ y, W y g = 0 := Finset.sum_eq_zero fun y _ => by
          by_contra h; exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        rw [this, pow_zero]; exact zero_le_one
    calc _ ≤ (chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
          (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
            EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m)) *
          ∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1) :=
          mul_le_mul_of_nonneg_left hle (hΦ0 _)
      _ = _ := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  exact blockSets_le ok q hq hEu b smax Gp hS3 hK hG0 hGanti

end BlockSum

end RankFull
