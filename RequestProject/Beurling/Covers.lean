module

public import Mathlib

/-!
# Covers, capacity and thin supports (Sections 6.5–6.6)

Exponent vectors are elements of `Fin m → ℕ` (the paper's `ℤ^m_{≥0}`). Rank and span are taken
over `ℚ` after casting (`vq`). For a finite set `S` of such vectors:

* `supp v` is the support of `v`, `P S` the union of the supports;
* a *cover* is a subset `C ⊆ S` whose supports have union `P S`; `kappa S` is the least size of
  a cover;
* `rank S` is the rank, and `cap S = |S| - rank S` the capacity;
* `IsBasisOf S B` : `B ⊆ S` is linearly independent and spans `S`;
* `deg v = ‖v‖₁`.

Main results:

* `Covers.basis_isCover` (Lemma 6.15(a)), `Covers.kappa_le_of_extra` (Lemma 6.15(b)),
  `Covers.minimal_cover_linearIndependent` (Lemma 6.15(c));
* `Covers.coefficient_support` (Lemma 6.16);
* `Covers.capacity_thin_covers` (Theorem 6.17);
* `Covers.heavy_subspace` (Lemma 6.14), with `φ(u) = c + uQ + u(u+1)/2`;
* `Covers.kappa_le_of_cap_gt`, `Covers.capBound_le` (the remarks after Theorem 6.17);
* `Covers.extras_drop_out` (Lemma 6.21(i)) and `Covers.union_bound_le` (the arithmetic of
  Lemma 6.21(iii)).
-/

@[expose] public section

open Finset

namespace Covers

variable {m : ℕ}

/-- The rational vector of an exponent vector. -/
def vq (v : Fin m → ℕ) : Fin m → ℚ := fun i => (v i : ℚ)

/-- Support of an exponent vector. -/
def supp (v : Fin m → ℕ) : Finset (Fin m) := univ.filter (fun i => v i ≠ 0)

/-- The degree `‖v‖₁`. -/
def deg (v : Fin m → ℕ) : ℕ := ∑ i, v i

/-- `P(S)`, the union of the supports. -/
def P (S : Finset (Fin m → ℕ)) : Finset (Fin m) := S.biUnion supp

/-- `C` is a cover of `S`. -/
def IsCover (S C : Finset (Fin m → ℕ)) : Prop := C ⊆ S ∧ C.biUnion supp = P S

/-- `κ(S)`, the least size of a cover. -/
noncomputable def kappa (S : Finset (Fin m → ℕ)) : ℕ :=
  sInf {k | ∃ C, IsCover S C ∧ C.card = k}

/-- The rank of `S` (over `ℚ`). -/
noncomputable def rank (S : Finset (Fin m → ℕ)) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))))

/-- The capacity `Cap(S) = |S| - rank S`. -/
noncomputable def cap (S : Finset (Fin m → ℕ)) : ℤ := (S.card : ℤ) - rank S

/-- `B ⊆ S` is a basis of `S`: linearly independent, and every element of `S` is in its span. -/
def IsBasisOf (S B : Finset (Fin m → ℕ)) : Prop :=
  B ⊆ S ∧ LinearIndepOn ℚ vq (B : Set (Fin m → ℕ)) ∧
    Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) ≤ Submodule.span ℚ (vq '' (B : Set _))

/-- The bound `N(r, D, j) = ∑_{s=1}^{2j+1} C(r,s) C(D+s,s)` of Theorem 6.17. -/
def capBound (r D j : ℕ) : ℕ := ∑ s ∈ Icc 1 (2 * j + 1), r.choose s * (D + s).choose s

/-- The function `φ(u) = c + uQ + u(u+1)/2` of Section 6. -/
noncomputable def phi (c Q u : ℝ) : ℝ := c + u * Q + u * (u + 1) / 2


/-! ### Basic facts -/

lemma vq_injective : Function.Injective (vq (m := m)) := by
  intro v w h; funext i; have := congrFun h i; simpa [vq] using this

lemma mem_supp {v : Fin m → ℕ} {i : Fin m} : i ∈ supp v ↔ v i ≠ 0 := by simp [supp]

lemma exists_coeffs {B : Finset (Fin m → ℕ)} {x : Fin m → ℚ}
    (h : x ∈ Submodule.span ℚ (vq '' (B : Set (Fin m → ℕ)))) :
    ∃ α : (Fin m → ℕ) → ℚ, x = ∑ b ∈ B, α b • vq b := by
  rw [Submodule.mem_span_image_iff_exists_fun] at h
  obtain ⟨t, htB, c, hc⟩ := h
  classical
  refine ⟨fun b => if hb : b ∈ t then c ⟨b, hb⟩ else 0, ?_⟩
  rw [← hc, ← Finset.sum_subset htB (f := fun b => (if hb : b ∈ t then c ⟨b, hb⟩ else 0) • vq b)]
  · rw [← Finset.sum_attach t]
    simp
  · intro x _ hx; simp [hx]

lemma comb_apply (B : Finset (Fin m → ℕ)) (α : (Fin m → ℕ) → ℚ) (p : Fin m) :
    (∑ b ∈ B, α b • vq b) p = ∑ b ∈ B, α b * (b p : ℚ) := by
  simp [vq, Finset.sum_apply]

lemma kappa_le_card {S C : Finset (Fin m → ℕ)} (h : IsCover S C) : kappa S ≤ C.card :=
  Nat.sInf_le ⟨C, h, rfl⟩

lemma rank_eq_card {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) : rank S = B.card := by
  have hspan : Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) =
      Submodule.span ℚ (vq '' (B : Set (Fin m → ℕ))) :=
    le_antisymm hB.2.2 (Submodule.span_mono (Set.image_mono hB.1))
  unfold rank
  rw [hspan, Set.image_eq_range]
  rw [finrank_span_eq_card hB.2.1]
  simp

/-- If every element of `S` lies in the span of `B ⊆ S`, then `B` covers `S`. -/
lemma isCover_of_span {S B : Finset (Fin m → ℕ)} (hBS : B ⊆ S)
    (hspan : Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) ≤
      Submodule.span ℚ (vq '' (B : Set _))) : IsCover S B := by
  refine ⟨hBS, ?_⟩
  apply le_antisymm (Finset.biUnion_subset_biUnion_of_subset_left _ hBS)
  intro p hp
  simp only [P, Finset.mem_biUnion] at hp ⊢
  obtain ⟨y, hyS, hpy⟩ := hp
  obtain ⟨α, hα⟩ := exists_coeffs (hspan (Submodule.subset_span ⟨y, hyS, rfl⟩))
  have h1 := congrFun hα p
  rw [comb_apply] at h1
  by_contra hcon
  push_neg at hcon
  rw [Finset.sum_eq_zero (fun b hb => by
    have := hcon b hb; rw [mem_supp, not_not] at this; simp [this])] at h1
  rw [mem_supp] at hpy
  exact hpy (by simpa [vq] using h1)

section Signs

variable {B : Finset (Fin m → ℕ)} {y : Fin m → ℕ} {α : (Fin m → ℕ) → ℚ}

lemma sign_neg (hα : vq y = ∑ b ∈ B, α b • vq b) {b : Fin m → ℕ} (hb : b ∈ B) (hαb : α b < 0)
    {p : Fin m} (hp : p ∈ supp b) : ∃ b' ∈ B, 0 < α b' ∧ p ∈ supp b' := by
  by_contra hcon
  push_neg at hcon
  have h1 := congrFun hα p
  rw [comb_apply] at h1
  have hpos : 0 < ∑ b ∈ B, -(α b * (b p : ℚ)) := by
    apply Finset.sum_pos'
    · intro b' hb'
      by_cases h : 0 < α b'
      · have := hcon b' hb' h; rw [mem_supp, not_not] at this; simp [this]
      · push_neg at h; have : (0:ℚ) ≤ b' p := by positivity
        nlinarith
    · refine ⟨b, hb, ?_⟩
      rw [mem_supp] at hp
      have : (0:ℚ) < b p := by exact_mod_cast Nat.pos_of_ne_zero hp
      nlinarith
  rw [Finset.sum_neg_distrib, ← h1] at hpos
  have : (0:ℚ) ≤ vq y p := by simp [vq]
  linarith

lemma sign_pos (hα : vq y = ∑ b ∈ B, α b • vq b) {b : Fin m → ℕ} (hb : b ∈ B) (hαb : 0 < α b)
    {p : Fin m} (hp : p ∈ supp b) : p ∈ supp y ∨ ∃ l ∈ B, α l < 0 ∧ p ∈ supp l := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hy, hl⟩ := hcon
  have h1 := congrFun hα p
  rw [comb_apply] at h1
  have hpos : 0 < ∑ b ∈ B, α b * (b p : ℚ) := by
    apply Finset.sum_pos'
    · intro b' hb'
      by_cases h : α b' < 0
      · have := hl b' hb' h; rw [mem_supp, not_not] at this; simp [this]
      · push_neg at h; positivity
    · refine ⟨b, hb, ?_⟩
      rw [mem_supp] at hp
      have : (0:ℚ) < b p := by exact_mod_cast Nat.pos_of_ne_zero hp
      positivity
  rw [← h1] at hpos
  rw [mem_supp, not_not] at hy
  simp [vq, hy] at hpos

end Signs

/-- The cover `B \ I₋` (from (77)). -/
lemma cover_nonneg {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) {y : Fin m → ℕ}
    {α : (Fin m → ℕ) → ℚ} (hα : vq y = ∑ b ∈ B, α b • vq b) :
    IsCover S (B.filter (fun b => 0 ≤ α b)) := by
  have hcov := isCover_of_span hB.1 hB.2.2
  refine ⟨(Finset.filter_subset _ _).trans hB.1, ?_⟩
  apply le_antisymm
  · exact (Finset.biUnion_subset_biUnion_of_subset_left _
      ((Finset.filter_subset _ _).trans hB.1))
  · rw [← hcov.2]
    intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hp ⊢
    obtain ⟨b, hb, hpb⟩ := hp
    by_cases h : 0 ≤ α b
    · exact ⟨b, ⟨hb, h⟩, hpb⟩
    · obtain ⟨b', hb', h', hpb'⟩ := sign_neg hα hb (lt_of_not_ge h) hpb
      exact ⟨b', ⟨hb', h'.le⟩, hpb'⟩

/-- The cover `{y} ∪ I₋ ∪ (B \ (I₊ ∪ I₋))` (from (77)). -/
lemma cover_insert {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) {y : Fin m → ℕ} (hyS : y ∈ S)
    {α : (Fin m → ℕ) → ℚ} (hα : vq y = ∑ b ∈ B, α b • vq b) :
    IsCover S (insert y (B.filter (fun b => α b ≤ 0))) := by
  classical
  have hcov := isCover_of_span hB.1 hB.2.2
  have hsub : insert y (B.filter (fun b => α b ≤ 0)) ⊆ S :=
    Finset.insert_subset hyS ((Finset.filter_subset _ _).trans hB.1)
  refine ⟨hsub, ?_⟩
  apply le_antisymm
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ hsub
  · rw [← hcov.2]
    intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert] at hp ⊢
    obtain ⟨b, hb, hpb⟩ := hp
    by_cases h : α b ≤ 0
    · exact ⟨b, Or.inr ⟨hb, h⟩, hpb⟩
    · rcases sign_pos hα hb (lt_of_not_ge h) hpb with hy | ⟨l, hl, hl', hpl⟩
      · exact ⟨y, Or.inl rfl, hy⟩
      · exact ⟨l, Or.inr ⟨hl, hl'.le⟩, hpl⟩

/-- Lemma 6.15(a): every basis is a cover. -/
theorem basis_isCover {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) : IsCover S B :=
  isCover_of_span hB.1 hB.2.2

/-- Lemma 6.15(b): an extra that is not proportional to a basis vector forces `κ(S) ≤ r - 1`.
(The paper asks for `y ∉ B`; this is implied, since a basis vector is proportional to itself.) -/
theorem kappa_le_of_extra {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) (h0 : 0 ∉ S)
    {y : Fin m → ℕ} (hyS : y ∈ S)
    (hprop : ¬ ∃ b ∈ B, ∃ a : ℚ, vq y = a • vq b) : kappa S + 1 ≤ rank S := by
  classical
  obtain ⟨α, hα⟩ := exists_coeffs (hB.2.2 (Submodule.subset_span ⟨y, hyS, rfl⟩))
  have hr := rank_eq_card hB
  have h1 := kappa_le_card (cover_nonneg hB hα)
  have h2 := kappa_le_card (cover_insert hB hyS hα)
  have h3 := Finset.card_insert_le y (B.filter (fun b => α b ≤ 0))
  have e1 := Finset.card_filter_add_card_filter_not (s := B) (fun b => 0 ≤ α b)
  have e2 := Finset.card_filter_add_card_filter_not (s := B) (fun b => α b ≤ 0)
  simp only [not_le] at e1 e2
  have key : 1 ≤ (B.filter (fun b => α b < 0)).card ∨
      2 ≤ (B.filter (fun b => 0 < α b)).card := by
    by_contra hcon
    push_neg at hcon
    have hneg : ∀ b ∈ B, ¬ α b < 0 := by
      intro b hb h
      have : b ∈ B.filter (fun b => α b < 0) := Finset.mem_filter.mpr ⟨hb, h⟩
      have := Finset.card_pos.mpr ⟨b, this⟩
      omega
    rcases Nat.lt_succ_iff.mp hcon.2 |>.lt_or_eq with hlt | heq
    · have hpos : ∀ b ∈ B, ¬ 0 < α b := by
        intro b hb h
        have : b ∈ B.filter (fun b => 0 < α b) := Finset.mem_filter.mpr ⟨hb, h⟩
        have := Finset.card_pos.mpr ⟨b, this⟩
        omega
      have hy0 : vq y = 0 := by
        rw [hα]
        refine Finset.sum_eq_zero (fun b hb => ?_)
        have : α b = 0 := le_antisymm (not_lt.mp (hpos b hb)) (not_lt.mp (hneg b hb))
        simp [this]
      have : y = 0 := vq_injective (by rw [hy0]; funext i; simp [vq])
      exact h0 (this ▸ hyS)
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp heq
      have hb0B : b0 ∈ B := (Finset.mem_filter.mp (hb0 ▸ Finset.mem_singleton_self b0)).1
      apply hprop
      refine ⟨b0, hb0B, α b0, ?_⟩
      rw [hα, Finset.sum_eq_single b0]
      · intro b hb hne
        have hnp : ¬ 0 < α b := by
          intro h
          have : b ∈ B.filter (fun b => 0 < α b) := Finset.mem_filter.mpr ⟨hb, h⟩
          rw [hb0] at this; exact hne (Finset.mem_singleton.mp this)
        have : α b = 0 := le_antisymm (not_lt.mp hnp) (not_lt.mp (hneg b hb))
        simp [this]
      · intro h; exact absurd hb0B h
  omega

/-- Lemma 6.15(c): a minimal cover is linearly independent. -/
theorem minimal_cover_linearIndependent {S C : Finset (Fin m → ℕ)} (hC : IsCover S C)
    (hmin : ∀ C' ⊂ C, ¬ IsCover S C') : LinearIndepOn ℚ vq (C : Set (Fin m → ℕ)) := by
  classical
  rw [linearIndepOn_finset_iff]
  intro f hf c hc
  -- `c` has a private coordinate `p`
  have hnot := hmin (C.erase c) (Finset.erase_ssubset hc)
  have hne : (C.erase c).biUnion supp ≠ P S := fun h =>
    hnot ⟨(Finset.erase_subset c C).trans hC.1, h⟩
  have hsub : (C.erase c).biUnion supp ⊆ P S :=
    Finset.biUnion_subset_biUnion_of_subset_left _ ((Finset.erase_subset c C).trans hC.1)
  obtain ⟨p, hpP, hpn⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
  rw [← hC.2] at hpP
  simp only [Finset.mem_biUnion, Finset.mem_erase, not_exists, not_and] at hpP hpn
  obtain ⟨c', hc', hpc'⟩ := hpP
  have hcc : c' = c := by
    by_contra h; exact hpn c' ⟨h, hc'⟩ hpc'
  subst hcc
  have h1 := congrFun hf p
  rw [comb_apply] at h1
  rw [Finset.sum_eq_single c'] at h1
  · rw [mem_supp] at hpc'
    simpa [hpc'] using h1
  · intro b hb hne
    have : p ∉ supp b := fun h => hpn b ⟨hne, hb⟩ h
    rw [mem_supp, not_not] at this; simp [this]
  · intro h; exact absurd hc' h

/-- Lemma 6.16 (coefficient support): if `κ(S) ≥ r - j`, then for every basis `B` and every
extra `y = ∑_{b ∈ B} α_b b`, at most `j` coefficients are negative and at most `j + 1` are
positive. -/
theorem coefficient_support {S B : Finset (Fin m → ℕ)} (hB : IsBasisOf S B) {j : ℕ}
    (hκ : rank S ≤ kappa S + j) {y : Fin m → ℕ} (hyS : y ∈ S)
    (α : (Fin m → ℕ) → ℚ) (hα : vq y = ∑ b ∈ B, α b • vq b) :
    (B.filter (fun b => α b < 0)).card ≤ j ∧ (B.filter (fun b => 0 < α b)).card ≤ j + 1 := by
  classical
  have hr := rank_eq_card hB
  have h1 := kappa_le_card (cover_nonneg hB hα)
  have h2 := kappa_le_card (cover_insert hB hyS hα)
  have h3 := Finset.card_insert_le y (B.filter (fun b => α b ≤ 0))
  have e1 := Finset.card_filter_add_card_filter_not (s := B) (fun b => 0 ≤ α b)
  have e2 := Finset.card_filter_add_card_filter_not (s := B) (fun b => α b ≤ 0)
  simp only [not_le] at e1 e2
  omega

/-- A finite-dimensional subspace `W` of `ℚ^m` is determined, inside `W`, by at most `dim W`
coordinates. -/
lemma exists_separating_coords (W : Submodule ℚ (Fin m → ℚ)) :
    ∃ T : Finset (Fin m), T.card ≤ Module.finrank ℚ W ∧
      ∀ w ∈ W, (∀ i ∈ T, w i = 0) → w = 0 := by
  classical
  let good : Finset (Fin m) → Prop := fun T => ∀ w ∈ W, (∀ i ∈ T, w i = 0) → w = 0
  have huniv : good Finset.univ := fun w _ h => funext fun i => h i (Finset.mem_univ i)
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset (Fin m))).filter good) Finset.card
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huniv⟩⟩
  have hTg : good T := (Finset.mem_filter.mp hT).2
  refine ⟨T, ?_, hTg⟩
  by_contra hlt
  push_neg at hlt
  let f : T → Module.Dual ℚ W := fun i =>
    (LinearMap.proj (R := ℚ) (φ := fun _ : Fin m => ℚ) (i : Fin m)).comp W.subtype
  have hnli : ¬ LinearIndependent ℚ f := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Subspace.dual_finrank_eq] at this
    simp at this
    omega
  rw [linearIndependent_iff_notMem_span] at hnli
  push_neg at hnli
  obtain ⟨i0, hi0⟩ := hnli
  have hg : good (T.erase i0) := by
    intro w hw hz
    apply hTg w hw
    intro i hi
    by_cases hii : i = i0
    · subst hii
      have key : ∀ g ∈ Submodule.span ℚ (f '' (Set.univ \ {i0})), g ⟨w, hw⟩ = 0 := by
        intro g hg
        induction hg using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨j, hj, rfl⟩ := hx
          have hj' : j ≠ i0 := by simpa using hj
          simp [f]
          exact hz j (Finset.mem_erase.mpr ⟨fun h => hj' (Subtype.ext h), j.2⟩)
        | zero => simp
        | add x y _ _ hx hy => simp [hx, hy]
        | smul a x _ hx => simp [hx]
      have := key _ hi0
      simpa [f] using this
    · exact hz i (Finset.mem_erase.mpr ⟨hii, hi⟩)
  have := hmin (T.erase i0) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  have := Finset.card_erase_lt_of_mem i0.2
  omega

/-- Vectors of degree `≤ D` lying in a subspace of dimension `s` number at most
`C(s + D, D) = C(D + s, s)`. -/
lemma card_le_of_mem_subspace (W : Submodule ℚ (Fin m → ℚ)) (A : Finset (Fin m → ℕ)) (D : ℕ)
    (hA : ∀ v ∈ A, vq v ∈ W) (hD : ∀ v ∈ A, deg v ≤ D) :
    A.card ≤ (Module.finrank ℚ W + D).choose D := by
  classical
  obtain ⟨T, hTcard, hT⟩ := exists_separating_coords W
  let g : (Fin m → ℕ) → Multiset (Option T) := fun v =>
    (∑ i : T, v i • ({some i} : Multiset (Option T))) + (D - ∑ i : T, v i) • {none}
  have hsumT : ∀ v ∈ A, ∑ i : T, v i ≤ D := by
    intro v hv
    calc ∑ i : T, v i = ∑ i ∈ T, v i := Finset.sum_coe_sort T v
      _ ≤ ∑ i, v i := Finset.sum_le_sum_of_subset (Finset.subset_univ T)
      _ ≤ D := hD v hv
  have hgcard : ∀ v ∈ A, Multiset.card (g v) = D := by
    intro v hv
    simp only [g, Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
    simp only [Multiset.card_sum, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
    have := hsumT v hv
    omega
  have hcount : ∀ v (i : T), Multiset.count (some i) (g v) = v i := by
    intro v i
    simp only [g, Multiset.count_add, Multiset.count_nsmul, Multiset.count_sum',
      Multiset.count_singleton]
    simp
  let G : A → Sym (Option T) D := fun v => ⟨g v, hgcard v v.2⟩
  have hinj : Function.Injective G := by
    intro v v' h
    have hc : ∀ i : T, v.1 i = v'.1 i := by
      intro i
      rw [← hcount v.1 i, ← hcount v'.1 i]
      have : g v.1 = g v'.1 := congrArg Subtype.val h
      rw [this]
    have hw := hT (vq v.1 - vq v'.1) (W.sub_mem (hA _ v.2) (hA _ v'.2)) (by
      intro i hi; have := hc ⟨i, hi⟩; simp [vq, this])
    exact Subtype.ext (vq_injective (sub_eq_zero.mp hw))
  calc A.card = Fintype.card A := (Fintype.card_coe A).symm
   _ ≤ Fintype.card (Sym (Option T) D) := Fintype.card_le_of_injective G hinj
   _ = (T.card + D).choose D := by
      rw [Sym.card_sym_eq_choose]; simp
   _ ≤ (Module.finrank ℚ W + D).choose D := Nat.choose_le_choose D (by omega)

/-- Every finite `S` has a basis `B ⊆ S`. -/
lemma exists_basisOf (S : Finset (Fin m → ℕ)) : ∃ B, IsBasisOf S B := by
  classical
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent ℚ (vq '' (S : Set (Fin m → ℕ)))
  have himg : vq '' ((S.filter (fun v => vq v ∈ b) : Finset _) : Set (Fin m → ℕ)) = b := by
    ext x
    simp only [Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩; exact hv
    · intro hx; obtain ⟨v, hv, rfl⟩ := hbt hx; exact ⟨v, ⟨hv, hx⟩, rfl⟩
  refine ⟨S.filter (fun v => vq v ∈ b), Finset.filter_subset _ _, ?_, ?_⟩
  · rw [linearIndepOn_iff_image (vq_injective.injOn), himg]; exact hli
  · rw [himg, hspan]

/-- Theorem 6.17 (capacity forces thin covers): if `κ(S) ≥ r - j` and every vector of `S` has
degree at most `D`, then `Cap(S) ≤ N(r, D, j)`. -/
theorem capacity_thin_covers {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) (hκ : rank S ≤ kappa S + j) :
    cap S ≤ capBound (rank S) D j := by
  classical
  obtain ⟨B, hB⟩ := exists_basisOf S
  have hr := rank_eq_card hB
  have hco : ∀ y ∈ S, ∃ α : (Fin m → ℕ) → ℚ, vq y = ∑ b ∈ B, α b • vq b := fun y hy =>
    exists_coeffs (hB.2.2 (Submodule.subset_span ⟨y, hy, rfl⟩))
  choose! α hα using hco
  let I : (Fin m → ℕ) → Finset (Fin m → ℕ) := fun y => B.filter (fun b => α y b ≠ 0)
  have hIcard : ∀ y ∈ S, (I y).card ∈ Icc 1 (2 * j + 1) := by
    intro y hy
    rw [Finset.mem_Icc]
    constructor
    · by_contra hlt
      push_neg at hlt
      have hemp : I y = ∅ := Finset.card_eq_zero.mp (by omega)
      have hy0 : vq y = 0 := by
        rw [hα y hy]
        refine Finset.sum_eq_zero (fun b hb => ?_)
        have : α y b = 0 := by
          by_contra hne
          have : b ∈ I y := Finset.mem_filter.mpr ⟨hb, hne⟩
          rw [hemp] at this; simp at this
        simp [this]
      have : y = 0 := vq_injective (by rw [hy0]; funext i; simp [vq])
      exact h0 (this ▸ hy)
    · have hsplit : I y ⊆ B.filter (fun b => α y b < 0) ∪ B.filter (fun b => 0 < α y b) := by
        intro b hb
        obtain ⟨hbB, hne⟩ := Finset.mem_filter.mp hb
        rcases lt_or_gt_of_ne hne with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbB, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbB, h⟩)
      have h1 := Finset.card_le_card hsplit
      have h2 := Finset.card_union_le (B.filter (fun b => α y b < 0))
        (B.filter (fun b => 0 < α y b))
      have h3 := coefficient_support hB hκ hy (α y) (hα y hy)
      omega
  have hfiber : ∀ J ∈ B.powerset, ((S \ B).filter (fun y => I y = J)).card ≤
      (J.card + D).choose D := by
    intro J hJ
    have hW := card_le_of_mem_subspace (Submodule.span ℚ (vq '' (J : Set (Fin m → ℕ))))
      ((S \ B).filter (fun y => I y = J)) D ?_ ?_
    · refine hW.trans (Nat.choose_le_choose D ?_)
      have := finrank_span_finset_le_card (R := ℚ) (J.image vq)
      rw [Finset.coe_image] at this
      have := Finset.card_image_le (s := J) (f := vq)
      have : Set.finrank ℚ (vq '' (J : Set (Fin m → ℕ))) =
        Module.finrank ℚ (Submodule.span ℚ (vq '' (J : Set (Fin m → ℕ)))) := rfl
      omega
    · intro y hy
      obtain ⟨hyS, hIJ⟩ := Finset.mem_filter.mp hy
      have hyS' := (Finset.mem_sdiff.mp hyS).1
      rw [hα y hyS']
      rw [← Finset.sum_subset (Finset.mem_powerset.mp hJ) (f := fun b => α y b • vq b)]
      · exact Submodule.sum_mem _ (fun b hb =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩))
      · intro b hb hbJ
        have : α y b = 0 := by
          by_contra hne
          exact hbJ (hIJ ▸ Finset.mem_filter.mpr ⟨hb, hne⟩)
        simp [this]
    · intro y hy
      exact hD y (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1
  have hcount : (S \ B).card ≤ capBound B.card D j := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y => (I y).card) (t := Icc 1 (2 * j + 1))
      (fun y hy => hIcard y (Finset.mem_sdiff.mp hy).1)]
    unfold capBound
    apply Finset.sum_le_sum
    intro s hs
    have := Finset.card_le_mul_card_image_of_maps_to
      (s := (S \ B).filter (fun y => (I y).card = s)) (t := B.powersetCard s) (f := I)
      (fun y hy => Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _,
        (Finset.mem_filter.mp hy).2⟩) ((D + s).choose s) (by
        intro J hJ
        obtain ⟨hJB, hJs⟩ := Finset.mem_powersetCard.mp hJ
        refine (Finset.card_le_card ?_).trans
          ((hfiber J (Finset.mem_powerset.mpr hJB)).trans_eq ?_)
        · intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1.1, hy.2⟩
        · rw [hJs, add_comm, Nat.choose_symm_add])
    rw [Finset.card_powersetCard] at this
    linarith [mul_comm ((D + s).choose s) (B.card.choose s)]
  unfold cap
  rw [hr]
  have := Finset.card_sdiff_add_card_eq_card hB.1
  omega


/-- The contrapositive form of Theorem 6.17: `Cap(S) > N(r, D, j)` forces `κ(S) ≤ r - 1 - j`. -/
theorem kappa_le_of_cap_gt {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) (hcap : (capBound (rank S) D j : ℤ) < cap S) :
    kappa S + j + 1 ≤ rank S := by
  by_contra h
  push_neg at h
  have := capacity_thin_covers (j := j) h0 hD (by omega)
  omega

lemma choose_add_le_pow (D s : ℕ) : (D + s).choose s ≤ (D + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h := Nat.add_one_mul_choose_eq (D + s) s
    have h2 : (D + s + 1) * (D + s).choose s ≤ (s + 1) * ((D + 1) * (D + s).choose s) := by
      have : D + s + 1 ≤ (s + 1) * (D + 1) := by nlinarith
      calc (D + s + 1) * (D + s).choose s ≤ ((s + 1) * (D + 1)) * (D + s).choose s :=
            Nat.mul_le_mul_right _ this
        _ = _ := by ring
    rw [h, mul_comm _ (s+1)] at h2
    have h3 := Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos s)
    calc (D + (s + 1)).choose (s + 1) ≤ (D + 1) * (D + s).choose s := by
          rw [← add_assoc]; exact h3
      _ ≤ (D + 1) * (D + 1) ^ s := Nat.mul_le_mul_left _ ih
      _ = (D + 1) ^ (s + 1) := by ring

/-- The estimate `N(r, D, j) ≤ e (r(D+1))^{2j+1}` stated after Theorem 6.17. -/
theorem capBound_le (r D j : ℕ) :
    (capBound r D j : ℝ) ≤ Real.exp 1 * ((r : ℝ) * (D + 1)) ^ (2 * j + 1) := by
  set X : ℝ := (r : ℝ) * (D + 1) with hX
  have hXcases : X = 0 ∨ 1 ≤ X := by
    rcases Nat.eq_zero_or_pos r with h | h
    · left; simp [hX, h]
    · right; have : (1:ℝ) ≤ r := by exact_mod_cast h
      nlinarith
  unfold capBound
  push_cast
  have hterm : ∀ s ∈ Icc 1 (2 * j + 1), ((r.choose s : ℕ) : ℝ) * (((D + s).choose s : ℕ) : ℝ) ≤
      X ^ (2 * j + 1) * (1 / (s.factorial : ℝ)) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hs
    have h1 : ((r.choose s : ℕ) : ℝ) ≤ (r : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s r
    have h2 : (((D + s).choose s : ℕ) : ℝ) ≤ ((D : ℝ) + 1) ^ s := by
      exact_mod_cast choose_add_le_pow D s
    have h3 : X ^ s ≤ X ^ (2 * j + 1) := by
      rcases hXcases with h | h
      · rw [h, zero_pow (by omega), zero_pow (by omega)]
      · exact pow_le_pow_right₀ h hs2
    calc ((r.choose s : ℕ) : ℝ) * (((D + s).choose s : ℕ) : ℝ)
        ≤ ((r : ℝ) ^ s / s.factorial) * ((D : ℝ) + 1) ^ s := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = X ^ s * (1 / (s.factorial : ℝ)) := by rw [hX, mul_pow]; ring
      _ ≤ X ^ (2 * j + 1) * (1 / (s.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
  calc ∑ s ∈ Icc 1 (2 * j + 1), ((r.choose s : ℕ) : ℝ) * (((D + s).choose s : ℕ) : ℝ)
      ≤ ∑ s ∈ Icc 1 (2 * j + 1), X ^ (2 * j + 1) * (1 / (s.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = X ^ (2 * j + 1) * ∑ s ∈ Icc 1 (2 * j + 1), (1 / (s.factorial : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ X ^ (2 * j + 1) * Real.exp 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : Icc 1 (2 * j + 1) ⊆ range (2 * j + 2) := by
          intro s hs; simp at hs ⊢; omega
        calc ∑ s ∈ Icc 1 (2 * j + 1), (1 / (s.factorial : ℝ))
            ≤ ∑ s ∈ range (2 * j + 2), (1 / (s.factorial : ℝ)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = ∑ s ∈ range (2 * j + 2), (1:ℝ) ^ s / (s.factorial : ℝ) := by simp
          _ ≤ Real.exp 1 := Real.sum_le_exp_of_nonneg zero_le_one _
    _ = _ := by ring


/-! ### Lemma 6.21(i): extras drop out -/

lemma exists_min_cover (S : Finset (Fin m → ℕ)) : ∃ C, IsCover S C ∧ C.card = kappa S :=
  Nat.sInf_mem (s := {k | ∃ C, IsCover S C ∧ C.card = k}) ⟨S.card, S, ⟨subset_refl _, rfl⟩, rfl⟩

lemma min_cover_minimal {S C : Finset (Fin m → ℕ)} (hcard : C.card = kappa S) :
    ∀ C' ⊂ C, ¬ IsCover S C' := fun C' hlt h => by
  have := kappa_le_card h
  have := Finset.card_lt_card hlt
  omega

lemma exists_basis_extending {S C : Finset (Fin m → ℕ)} (hCS : C ⊆ S)
    (hli : LinearIndepOn ℚ vq (C : Set (Fin m → ℕ))) : ∃ B, IsBasisOf S B ∧ C ⊆ B := by
  classical
  obtain ⟨b, hbS, hCb, hspan, hlib⟩ :=
    exists_linearIndepOn_extension hli (Finset.coe_subset.mpr hCS)
  have hcoe : ((S.filter (fun v => v ∈ b) : Finset _) : Set (Fin m → ℕ)) = b := by
    ext v
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hbS h, h⟩⟩
  refine ⟨S.filter (fun v => v ∈ b), ⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
  · rw [hcoe]; exact hlib
  · rw [hcoe, Submodule.span_le]; exact hspan
  · intro v hv
    exact Finset.mem_filter.mpr ⟨hCS hv, hCb hv⟩

/-- Lemma 6.21(i) (extras drop out): if `Cap(S) ≥ c > e (r(D+1))^{2j+1}`, then
`κ(S) ≤ r - 1 - j`; a minimum cover `C` extends to a basis `B ⊆ S` (which covers `S`, by
Lemma 6.15(a)), and the rows `R = B \ C` outside the cover number at least `1 + j`. -/
theorem extras_drop_out {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) {c : ℝ}
    (hc : Real.exp 1 * ((rank S : ℝ) * (D + 1)) ^ (2 * j + 1) < c) (hcap : c ≤ cap S) :
    kappa S + j + 1 ≤ rank S ∧
      ∃ C B, IsCover S C ∧ C.card = kappa S ∧ IsBasisOf S B ∧ C ⊆ B ∧
        j + 1 ≤ (B \ C).card := by
  have hlt : (capBound (rank S) D j : ℤ) < cap S := by
    have h1 := capBound_le (rank S) D j
    have : ((capBound (rank S) D j : ℤ) : ℝ) < (cap S : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hκ := kappa_le_of_cap_gt h0 hD hlt
  refine ⟨hκ, ?_⟩
  obtain ⟨C, hC, hCcard⟩ := exists_min_cover S
  have hli := minimal_cover_linearIndependent hC (min_cover_minimal hCcard)
  obtain ⟨B, hB, hCB⟩ := exists_basis_extending hC.1 hli
  refine ⟨C, B, hC, hCcard, hB, hCB, ?_⟩
  rw [Finset.card_sdiff_of_subset hCB, ← rank_eq_card hB, hCcard]
  omega

/-- Lemma 6.21(iii), the arithmetic step: with `z = e^L`, `L ≥ 60`, `r₀ ≤ L` and `0 < w`,
condition (80), `(1 + j) log(1/w) ≥ L + 10 log L + 10`, gives `r₀ · 13 L^{5.1} z w^{1+j} ≤ L^{-3}`. -/
theorem union_bound_le {L w r0 : ℝ} (hL : 60 ≤ L) (hw0 : 0 < w) (hr0 : r0 ≤ L) (j : ℕ)
    (h : L + 10 * Real.log L + 10 ≤ (1 + j) * Real.log (1 / w)) :
    r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) * w ^ (1 + j) ≤ L ^ (-3 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hw : w ^ (1 + j) ≤ Real.exp (-(L + 10 * Real.log L + 10)) := by
    have : w ^ (1 + j) = Real.exp (-((1 + j) * Real.log (1 / w))) := by
      rw [one_div, Real.log_inv, mul_neg, neg_neg, ← Real.log_rpow hw0,
        Real.exp_log (by positivity)]
      norm_cast
    rw [this]; exact Real.exp_le_exp.mpr (by linarith)
  have e1 : Real.exp (-(L + 10 * Real.log L + 10)) =
      Real.exp (-L) * L ^ (-10 : ℝ) * Real.exp (-10) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have he10 : Real.exp (-10) * 13 ≤ 1 / 60 := by
    have := Real.exp_one_gt_d9
    have h10 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg, h10]
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 10]
  calc r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) * w ^ (1 + j)
      ≤ L * (13 * L ^ (5.1 : ℝ) * Real.exp L) *
          (Real.exp (-L) * L ^ (-10 : ℝ) * Real.exp (-10)) := by
        rw [← e1]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hr0 (by positivity)) hw (by positivity)
          (by positivity)
    _ = (Real.exp (-10) * 13) * (L ^ (1 : ℝ) * L ^ (5.1 : ℝ) * L ^ (-10 : ℝ)) *
          (Real.exp L * Real.exp (-L)) := by
        rw [Real.rpow_one]; ring
    _ = (Real.exp (-10) * 13) * L ^ (-3.9 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.exp_add]; norm_num
    _ ≤ (1 / 60) * L ^ (-3.9 : ℝ) := mul_le_mul_of_nonneg_right he10 (by positivity)
    _ ≤ L ^ (-3 : ℝ) := by
        have : L ^ (-3.9 : ℝ) = L ^ (-3 : ℝ) * L ^ (-0.9 : ℝ) := by
          rw [← Real.rpow_add hL0]; norm_num
        rw [this]
        have h1 : L ^ (-0.9 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        have h2 : 0 < L ^ (-3 : ℝ) := by positivity
        nlinarith

/-- A subspace spanned by elements of `S`. -/
def ElemSpanned (S : Finset (Fin m → ℕ)) (W : Submodule ℚ (Fin m → ℚ)) : Prop :=
  ∃ T ⊆ S, W = Submodule.span ℚ (vq '' (T : Set (Fin m → ℕ)))

/-- `S ∩ W`. -/
noncomputable def inter (S : Finset (Fin m → ℕ)) (W : Submodule ℚ (Fin m → ℚ)) :
    Finset (Fin m → ℕ) := by
  classical exact S.filter (fun y => vq y ∈ W)

/-- `W` is heavy: `#(S ∩ W) ≥ φ(dim W)`. -/
def Heavy (c Q : ℝ) (S : Finset (Fin m → ℕ)) (W : Submodule ℚ (Fin m → ℚ)) : Prop :=
  phi c Q (Module.finrank ℚ W) ≤ (inter S W).card

open scoped Classical in
/-- Lemma 6.14 (heavy subspace). Let `S` have rank `< r₀` and `|S| ≥ r₀ + φ(r₀)`, with
`Q ≥ 0`. Then there is a heavy element-spanned subspace `V` of least dimension `r`, and
(i) `Cap(S ∩ V) ≥ φ(r) - r ≥ c`;
(ii) every proper element-spanned `W' < V` has `#(S ∩ V \ W') > Q + r`;
(iii) if at most `Q` elements of `S ∩ V` have degree `≤ k`, the elements of degree `≥ k + 1`
span `V`. -/
theorem heavy_subspace {S : Finset (Fin m → ℕ)} {c Q : ℝ} (hQ : 0 ≤ Q) {r₀ : ℕ}
    (hrank : rank S < r₀) (hcard : (r₀ : ℝ) + phi c Q r₀ ≤ S.card) :
    ∃ V : Submodule ℚ (Fin m → ℚ), ElemSpanned S V ∧ Heavy c Q S V ∧
      (∀ W, ElemSpanned S W → Heavy c Q S W → Module.finrank ℚ V ≤ Module.finrank ℚ W) ∧
      (phi c Q (Module.finrank ℚ V) - Module.finrank ℚ V ≤ (cap (inter S V) : ℝ) ∧
        c ≤ phi c Q (Module.finrank ℚ V) - Module.finrank ℚ V) ∧
      (∀ W', ElemSpanned S W' → W' < V →
        Q + Module.finrank ℚ V < ((inter S V).filter (fun y => vq y ∉ W')).card) ∧
      (∀ k : ℕ, (((inter S V).filter (fun y => deg y ≤ k)).card : ℝ) ≤ Q →
        Submodule.span ℚ (vq '' (((inter S V).filter (fun y => k + 1 ≤ deg y) :
          Finset (Fin m → ℕ)) : Set (Fin m → ℕ))) = V) := by
  classical
  have phi_mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → phi c Q a ≤ phi c Q b := by
    intro a b ha hab; unfold phi; nlinarith
  let cands : Finset (Finset (Fin m → ℕ)) := S.powerset.filter
    (fun T : Finset (Fin m → ℕ) => Heavy c Q S (Submodule.span ℚ (vq '' (T : Set (Fin m → ℕ)))))
  have hSmem : S ∈ cands := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset_self S, ?_⟩
    have hinter : inter S (Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ)))) = S := by
      unfold inter
      exact Finset.filter_true_of_mem (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)
    unfold Heavy
    rw [hinter]
    have h1 : (rank S : ℝ) ≤ r₀ := by exact_mod_cast hrank.le
    have h2 := phi_mono (rank S) r₀ (by positivity) h1
    have h3 : 0 ≤ (r₀ : ℝ) := by positivity
    unfold rank at h2
    linarith
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image cands
    (fun T : Finset (Fin m → ℕ) =>
      Module.finrank ℚ (Submodule.span ℚ (vq '' (T : Set (Fin m → ℕ))))) ⟨S, hSmem⟩
  obtain ⟨hTS, hVh⟩ := Finset.mem_filter.mp hT
  rw [Finset.mem_powerset] at hTS
  set V := Submodule.span ℚ (vq '' (T : Set (Fin m → ℕ))) with hV
  set r := Module.finrank ℚ V with hr
  have hVes : ElemSpanned S V := ⟨T, hTS, rfl⟩
  have hminW : ∀ W, ElemSpanned S W → Heavy c Q S W → r ≤ Module.finrank ℚ W := by
    rintro W ⟨T', hT', rfl⟩ hW
    exact hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT', hW⟩)
  have hsp : Submodule.span ℚ (vq '' ((inter S V : Finset _) : Set (Fin m → ℕ))) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      unfold inter at hy
      exact (Finset.mem_filter.mp hy).2
    · apply Submodule.span_mono
      apply Set.image_mono
      intro t ht
      unfold inter
      exact Finset.mem_filter.mpr ⟨hTS ht, Submodule.subset_span ⟨t, ht, rfl⟩⟩
  have hrank : rank (inter S V) = r := by
    unfold rank; rw [hsp]
  have hcardV : phi c Q r ≤ (inter S V).card := hVh
  -- (ii)
  have hii : ∀ W', ElemSpanned S W' → W' < V →
      Q + r < ((inter S V).filter (fun y => vq y ∉ W')).card := by
    intro W' hW' hlt
    have hdim : Module.finrank ℚ W' < r := Submodule.finrank_lt_finrank_of_lt hlt
    have hnot : ¬ Heavy c Q S W' := fun h => absurd (hminW W' hW' h) (not_le.mpr hdim)
    unfold Heavy at hnot
    push_neg at hnot
    have hr1 : 1 ≤ r := by omega
    have hphi : phi c Q (Module.finrank ℚ W') ≤ phi c Q ((r : ℝ) - 1) := by
      apply phi_mono _ _ (by positivity)
      have : ((Module.finrank ℚ W' : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      rw [Nat.cast_sub hr1] at this
      simpa using this
    have hsplit := Finset.card_filter_add_card_filter_not (s := inter S V) (fun y => vq y ∈ W')
    have heq : (inter S V).filter (fun y => vq y ∈ W') = inter S W' := by
      unfold inter
      rw [Finset.filter_filter]
      congr 1
      funext y
      apply propext
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hlt.le h, h⟩
    rw [heq] at hsplit
    have hdiff : phi c Q r - phi c Q ((r : ℝ) - 1) = Q + r := by unfold phi; ring
    have : (((inter S V).filter (fun y => vq y ∉ W')).card : ℝ) =
        (inter S V).card - (inter S W').card := by
      rw [← hsplit]; push_cast; ring
    rw [this]
    linarith
  refine ⟨V, hVes, hVh, hminW, ⟨?_, ?_⟩, hii, ?_⟩
  · unfold cap
    rw [hrank]
    push_cast
    linarith
  · rw [← hr]
    unfold phi
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ r := by exact_mod_cast h
      have : 0 ≤ (r : ℝ) * Q := by positivity
      nlinarith
  · intro k hlow
    set H := (inter S V).filter (fun y => k + 1 ≤ deg y)
    have hHS : H ⊆ S := fun y hy => by
      simp only [H, inter, Finset.mem_filter] at hy
      exact hy.1.1
    have hle : Submodule.span ℚ (vq '' (H : Set (Fin m → ℕ))) ≤ V := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have := (Finset.mem_filter.mp hy).1
      unfold inter at this
      exact (Finset.mem_filter.mp this).2
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have h1 := hii _ ⟨H, hHS, rfl⟩ hlt
    have hsub : (inter S V).filter (fun y => vq y ∉ Submodule.span ℚ (vq '' (H : Set _))) ⊆
        (inter S V).filter (fun y => deg y ≤ k) := by
      intro y hy
      obtain ⟨hyV, hyW⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨hyV, ?_⟩
      by_contra hdeg
      push_neg at hdeg
      exact hyW (Submodule.subset_span ⟨y, Finset.mem_filter.mpr ⟨hyV, hdeg⟩, rfl⟩)
    have h2 : (((inter S V).filter
        (fun y => vq y ∉ Submodule.span ℚ (vq '' (H : Set _)))).card : ℝ) ≤
        ((inter S V).filter (fun y => deg y ≤ k)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have : (0 : ℝ) ≤ r := by positivity
    linarith

end Covers
