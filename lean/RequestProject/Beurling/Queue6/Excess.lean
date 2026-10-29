module

public import RequestProject.Beurling.Model.Top

/-!
# The excess identity (Lemma 3.9) and the sandwich of Theorem 6.6(ii), for the constructed model

For the constructed slot model `M` (with its prime data `D = DM M U`), off the null event `𝒩₌`
(`TieFree`):

* `Queue6.cjitSet`, `Queue6.Cjit` : the composites in `[a, b)` with a jittered prime (not
  `RatOnly`) whose value is not in the absorbed set `𝒜` (`C_jit` of Lemma 3.9);
* `Queue6.ContSlot` : relative slot `l ≥ 1` is a *continuous slot*: `T(s_l-) = l + ϑ_s`, i.e.
  `X₀ + J(s_l-) + C(s_l) = level l` (§3.4);
* `Queue6.ellW i j` : `ℓ_jit((i, j])`, the continuous slots among `i + 1, …, j`;
* `Queue6.ellI a b` : `ℓ_jit([a, b))`, the continuous slots whose start lies in `[a, b)`;
* `Queue6.comp_eq` : the composites in `[a, b)` (`a > X₀`) are the rigid ones (one per
  `X₀`-smooth integer), the absorbed ones (one per value of `𝒜`) and `C_jit`:
  `#comp([a, b)) = C_jit([a, b)) + J(b-) - J(a-)`;
* `Queue6.exc_le` : **Lemma 3.9** (the upper bound used in §6): for the slot window
  `W = (i, j]`, `exc(W) ≤ C_jit(W) - ℓ_jit(W) + 2`;
* `Queue6.sandwich` : with the integer hull `I = [⌊s_{i+1}⌋, ⌈s_{j+1}⌉)`,
  `exc(W) ≤ C_jit(I) - ℓ_jit(I) + 6`, `ℓ_jit(I) ≤ ℓ_jit(W) + 4` and `ℓ_jit(W) ≤ ℓ_jit(I) + 1`
  (the "Sandwich" step of the proof of Theorem 6.6(ii)).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono BModel QueueDet

namespace Queue6

variable {X₀ : ℕ}

section Defs

variable (θ : ℝ) (M : SlotModel X₀) (U : ℕ → ℝ)

/-- The slots of the jittered primes of `e`. -/
def jitIdx (e : RealisedIdx M →₀ ℕ) : Set ℕ := {k | ∃ hk : placedAt M k, e (Sum.inr ⟨k, hk⟩) ≠ 0}

/-- The latest jittered prime of `e` (its largest slot, the decision order of §3.4). -/
noncomputable def latk (e : RealisedIdx M →₀ ℕ) : ℕ := sSup (jitIdx M e)

/-- **`e ∈ 𝒜`** (definition (5)): `log e ≥ L*`, and the latest prime of `e` is jittered and below
`y(e)`. -/
def OwnAbs (e : RealisedIdx M →₀ ℕ) : Prop :=
  10 ^ 7 ≤ Real.log (idxVal M (capH X₀) U e) ∧ ¬ RatOnly e ∧
    primeValueOf M (capH X₀) U (latk M e) < absorbY X₀ (idxVal M (capH X₀) U e)

/-- **`C_jit([a, b))`**: composites with value in `[a, b)` having a jittered prime, not in `𝒜`. -/
def cjitSet (a b : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | e ∈ compositeSet M (capH X₀) U a b ∧ ¬ RatOnly e ∧ ¬ OwnAbs M U e}

/-- The number `C_jit([a, b))`. -/
noncomputable def Cjit (a b : ℝ) : ℝ := ((cjitSet M U a b).ncard : ℝ)

/-- **A continuous slot** (§3.4): relative slot `l ≥ 1` with `T(s_l-) = l + ϑ_s`. -/
def ContSlot (l : ℕ) : Prop :=
  1 ≤ l ∧ (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) + contD θ X₀ (DM M U) (M.slot l) = M.level l

open Classical in
/-- **`ℓ_jit(W)`** for the slot window `W = (i, j]`. -/
noncomputable def ellW (i j : ℕ) : ℕ := ((Finset.Ioc i j).filter (ContSlot θ M U)).card

/-- **`ℓ_jit([a, b))`**: the continuous slots whose start lies in `[a, b)`. -/
noncomputable def ellI (a b : ℝ) : ℕ :=
  {l | ContSlot θ M U l ∧ a ≤ M.slot l ∧ M.slot l < b}.ncard

end Defs

section Latest

variable {M : SlotModel X₀}

lemma jitIdx_finite (e : RealisedIdx M →₀ ℕ) : (jitIdx M e).Finite := by
  classical
  refine ((e.support.image fun i => match i with
    | Sum.inl _ => 0
    | Sum.inr k => k.1).finite_toSet).subset fun k ⟨hk, hne⟩ => ?_
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff]
  exact ⟨Sum.inr ⟨k, hk⟩, hne, rfl⟩

lemma jitIdx_nonempty {e : RealisedIdx M →₀ ℕ} (he : ¬ RatOnly e) : (jitIdx M e).Nonempty := by
  unfold RatOnly at he
  push_neg at he
  obtain ⟨⟨k, hk⟩, hne⟩ := he
  exact ⟨k, hk, hne⟩

lemma latk_mem {e : RealisedIdx M →₀ ℕ} (he : ¬ RatOnly e) : latk M e ∈ jitIdx M e :=
  Nat.sSup_mem (jitIdx_nonempty he) (jitIdx_finite e).bddAbove

lemma le_latk (e : RealisedIdx M →₀ ℕ) {k : ℕ} (hk : k ∈ jitIdx M e) : k ≤ latk M e :=
  le_csSup (jitIdx_finite e).bddAbove hk

end Latest

/-! ### The facts about the constructed model used here -/

/-- The facts used for the excess identity: the window facts of Model/Window.lean, unit jumps
and no ties (off `𝒩₌`), the strict increase of the continuous part, and `X₀ < s_1`. -/
structure ExcFacts (θ : ℝ) (M : SlotModel X₀) (U : ℕ → ℝ) : Prop where
  win : WinFacts θ M U
  unit : UnitJumps X₀ (DM M U)
  tie : TieFree M U
  strict : ∀ x x', (X₀ : ℝ) ≤ x → x < x' → contD θ X₀ (DM M U) x < contD θ X₀ (DM M U) x'
  lower : ∀ x x', (X₀ : ℝ) ≤ x → x ≤ x' →
    0.08 * (x' - x) / Real.log x' ≤ contD θ X₀ (DM M U) x' - contD θ X₀ (DM M U) x
  slot1 : (X₀ : ℝ) < M.slot 1

/-- **The constructed model satisfies `ExcFacts`** off `𝒩₌`. -/
theorem excFacts_of {θ : ℝ} {U : ℕ → ℝ} (h : Std θ X₀ U) (hev : Even X₀)
    (ht : TieFree h.limModel U) : ExcFacts θ h.limModel U where
  win := winFacts h
  unit := unitJumps_of_tieFree ht
  tie := ht
  strict x x' hx hxx := by
    have hX1 := one_lt_of_logX (Nat.cast_nonneg _) h.hX
    have h1 := contD_lower h.hθ h.hX h.hHB (DM h.limModel U) (locFinD_DM h.hX h.hU _) hx hxx.le
    have hl : 0 < Real.log x' := Real.log_pos (by linarith)
    have : 0 < 0.08 * (x' - x) / Real.log x' := div_pos (by linarith) hl
    linarith
  lower x x' hx hxx := contD_lower h.hθ h.hX h.hHB (DM h.limModel U) (locFinD_DM h.hX h.hU _) hx hxx
  slot1 := (limModel_slot_one h hev).1

section Facts

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

lemma slot_gt {l : ℕ} (hl : 1 ≤ l) : (X₀ : ℝ) < M.slot l :=
  lt_of_lt_of_le F.slot1 (M.slot_mono hl)

/-- `X₀ + J(s_l-) + C(s_l) ≤ level l`. -/
lemma level_lower {l : ℕ} (hl : 1 ≤ l) :
    (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) + contD θ X₀ (DM M U) (M.slot l) ≤ M.level l := by
  have W := F.win
  have hs := slot_gt F hl
  have hs0 : 0 < M.slot l := by have := W.big; linarith
  obtain ⟨ℓ, hℓ, hJ⟩ := jumpD_lconst (X₀ := X₀) (DM M U) W.fin hs0
  by_contra hgt
  push_neg at hgt
  set δ := ((X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) + contD θ X₀ (DM M U) (M.slot l) -
    M.level l) / 2.02 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  set x := max (max ℓ X₀) (M.slot l - δ) with hxdef
  have hxs : x < M.slot l := max_lt (max_lt hℓ hs) (by linarith)
  have hxX : (X₀ : ℝ) ≤ x := (le_max_right _ _).trans (le_max_left _ _)
  have hxc : ℓ ≤ x := (le_max_left _ _).trans (le_max_left _ _)
  have hxd : M.slot l - δ ≤ x := le_max_right _ _
  have hT := M.T_lt_level (by have := W.big; linarith) hxs
  rw [W.split _ hxX, hJ x hxc hxs] at hT
  have hC := W.cup _ _ hxX hxs.le
  have h2 : 2.02 * δ = (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) +
      contD θ X₀ (DM M U) (M.slot l) - M.level l := by rw [hδ]; ring
  linarith

/-- `level l ≤ X₀ + J(s_l-) + C(s_l) + 1` (unit jumps). -/
lemma level_upper {l : ℕ} (hl : 1 ≤ l) :
    M.level l ≤ (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) + contD θ X₀ (DM M U) (M.slot l) + 1 := by
  classical
  have W := F.win
  have hs := slot_gt F hl
  have hs0 : 0 < M.slot l := by have := W.big; linarith
  have hTs := M.level_le_T_slot l
  rw [W.split _ hs.le] at hTs
  have hdiff := jumpD_sub_jumpL (X₀ := X₀) (DM M U) W.fin hs0
  have hle1 : jumpD X₀ (DM M U) (M.slot l) - jumpL X₀ (DM M U) (M.slot l) ≤ 1 := by
    rw [hdiff]
    by_cases h1 : ∃ n : ℕ, (n : ℝ) = M.slot l ∧ n ∈ Nat.smoothNumbers X₀
    · obtain ⟨n, hn, hsm⟩ := h1
      have hnX : (X₀ : ℝ) < n := by rw [hn]; exact hs
      have hnA := F.unit n hnX hsm
      rw [hn] at hnA
      rw [if_pos ⟨n, hn, hsm⟩, if_neg hnA]; norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  linarith

/-- Two continuous slots `l < l'` gain at least one unit of continuous mass. -/
lemma cont_gap {l l' : ℕ} (hll : l < l') (hc : ContSlot θ M U l) (hc' : ContSlot θ M U l') :
    1 ≤ contD θ X₀ (DM M U) (M.slot l') - contD θ X₀ (DM M U) (M.slot l) := by
  have hs := slot_gt F hc.1
  have hss : M.slot l ≤ M.slot l' := M.slot_mono hll.le
  have hL := hc.2
  have hL' := hc'.2
  obtain ⟨z, hz⟩ := jumpL_int (X₀ := X₀) (DM M U) (M.slot l)
  obtain ⟨z', hz'⟩ := jumpL_int (X₀ := X₀) (DM M U) (M.slot l')
  rw [hz] at hL
  rw [hz'] at hL'
  unfold SlotModel.level at hL hL'
  have hmm : (l : ℝ) + 1 ≤ l' := by exact_mod_cast hll
  have hdiff : contD θ X₀ (DM M U) (M.slot l') - contD θ X₀ (DM M U) (M.slot l) =
      ((l' : ℝ) - l) - ((z' : ℝ) - z) := by linarith
  rcases hss.lt_or_eq with hlt | heq
  · have hpos := F.strict _ _ hs.le hlt
    -- the difference is a positive integer
    have hint : (0 : ℝ) < ((l' : ℤ) - l - (z' - z) : ℤ) := by push_cast; linarith
    have hint' : (1 : ℤ) ≤ (l' : ℤ) - l - (z' - z) := by exact_mod_cast hint
    have : (1 : ℝ) ≤ ((l' : ℤ) - l - (z' - z) : ℤ) := by exact_mod_cast hint'
    push_cast at this
    linarith
  · exfalso
    rw [← heq] at hz' hL'
    rw [hz] at hz'
    have : (z : ℝ) = z' := hz'
    linarith

/-- Distinct continuous slots have distinct starts. -/
lemma cont_slot_ne {l l' : ℕ} (hll : l < l') (hc : ContSlot θ M U l)
    (hc' : ContSlot θ M U l') : M.slot l < M.slot l' := by
  have := cont_gap F hll hc hc'
  rcases (M.slot_mono hll.le).lt_or_eq with h | h
  · exact h
  · rw [h] at this; linarith

/-- The continuous mass between the first and last of `n + 1` continuous slots is at least `n`. -/
lemma cont_mass_card (S : Finset ℕ) (hS : ∀ l ∈ S, ContSlot θ M U l) (hne : S.Nonempty) :
    (S.card : ℝ) - 1 ≤ contD θ X₀ (DM M U) (M.slot (S.max' hne)) -
      contD θ X₀ (DM M U) (M.slot (S.min' hne)) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases h1 : S.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      simp
    · have hc2 : 2 ≤ S.card := by
        have := Finset.card_pos.mpr hne; omega
      set m := S.max' hne
      set S' := S.erase m
      have hS'ne : S'.Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (S.max'_mem hne)]; omega
      have hsub : S' ⊂ S := Finset.erase_ssubset (S.max'_mem hne)
      have hih := ih S' hsub (fun l hl => hS l (Finset.mem_of_mem_erase hl)) hS'ne
      have hcard : S'.card = S.card - 1 := Finset.card_erase_of_mem (S.max'_mem hne)
      have hm' : S'.max' hS'ne < m := by
        have hmem := S'.max'_mem hS'ne
        exact lt_of_le_of_ne (S.le_max' _ (Finset.mem_of_mem_erase hmem))
          (Finset.ne_of_mem_erase hmem)
      have hmin : S'.min' hS'ne = S.min' hne := by
        apply le_antisymm
        · apply Finset.min'_le
          refine Finset.mem_erase.mpr ⟨?_, S.min'_mem hne⟩
          intro heq
          have : S.min' hne < S.max' hne := Finset.min'_lt_max'_of_card S hc2
          rw [heq] at this; exact lt_irrefl _ this
        · exact Finset.min'_le _ _ (Finset.mem_of_mem_erase (S'.min'_mem hS'ne))
      have hgap := cont_gap F hm' (hS _ (Finset.mem_of_mem_erase (S'.max'_mem hS'ne)))
        (hS _ (S.max'_mem hne))
      rw [hmin] at hih
      have : (S'.card : ℝ) = S.card - 1 := by
        rw [hcard, Nat.cast_sub (by omega : 1 ≤ S.card)]; simp
      rw [this] at hih
      change (S.card : ℝ) - 1 ≤ contD θ X₀ (DM M U) (M.slot m) -
        contD θ X₀ (DM M U) (M.slot (S.min' hne))
      linarith

/-- At most two continuous-slot starts lie in an interval of length at most `1`. -/
lemma cont_starts_le_two {u v : ℝ} (hu : (X₀ : ℝ) ≤ u) (huv : v ≤ u + 1) :
    {l | ContSlot θ M U l ∧ u ≤ M.slot l ∧ M.slot l ≤ v}.ncard ≤ 2 := by
  classical
  by_contra hgt
  push_neg at hgt
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq (s := {l | ContSlot θ M U l ∧ u ≤ M.slot l ∧
    M.slot l ≤ v}) (n := 3) (by omega)
  have hTfin : T.Finite := Set.finite_of_ncard_pos (by omega)
  set S := hTfin.toFinset
  have hScard : S.card = 3 := by rw [← Set.ncard_eq_toFinset_card _ hTfin]; exact hT
  have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
  have hSmem : ∀ l ∈ S, ContSlot θ M U l ∧ u ≤ M.slot l ∧ M.slot l ≤ v := fun l hl =>
    hTS ((Set.Finite.mem_toFinset hTfin).mp hl)
  have hm := cont_mass_card F S (fun l hl => (hSmem l hl).1) hne
  rw [hScard] at hm
  have h1 := hSmem _ (S.max'_mem hne)
  have h2 := hSmem _ (S.min'_mem hne)
  have hcup := F.win.cup _ _ (hu.trans h2.2.1) (M.slot_mono (S.min'_le_max' hne))
  push_cast at hm
  linarith

end Facts

/-! ### Counting the composites of a window -/

section Count

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- The rigid composites in `[a, b)` (all primes rational). -/
def rigidSet (M : SlotModel X₀) (U : ℕ → ℝ) (a b : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | e ∈ compositeSet M (capH X₀) U a b ∧ RatOnly e}

/-- The absorbed composites in `[a, b)` (elements of `𝒜`). -/
def absPart (M : SlotModel X₀) (U : ℕ → ℝ) (a b : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | e ∈ compositeSet M (capH X₀) U a b ∧ OwnAbs M U e}

/-- The `X₀`-smooth integers in `[a, b)`. -/
def smoothIn (X₀ : ℕ) (a b : ℝ) : Set ℕ := {n | n ∈ Nat.smoothNumbers X₀ ∧ a ≤ n ∧ (n : ℝ) < b}

variable (F : ExcFacts θ M U)
include F

lemma comp_finite (a b : ℝ) : (compositeSet M (capH X₀) U a b).Finite :=
  (finite_compLt F.win.ok b).subset fun _ he => ⟨he.1, he.2.2⟩

omit F in
lemma compositeSet_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    compositeSet M (capH X₀) U a c =
      compositeSet M (capH X₀) U a b ∪ compositeSet M (capH X₀) U b c := by
  ext e
  simp only [compositeSet, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨h2, h1, h3⟩
    rcases lt_or_ge (idxVal M (capH X₀) U e) b with h | h
    · exact Or.inl ⟨h2, h1, h⟩
    · exact Or.inr ⟨h2, h, h3⟩
  · rintro (⟨h2, h1, h3⟩ | ⟨h2, h1, h3⟩)
    · exact ⟨h2, h1, by linarith⟩
    · exact ⟨h2, by linarith, h3⟩

omit F in
lemma compositeSet_disj (a b c : ℝ) :
    Disjoint (compositeSet M (capH X₀) U a b) (compositeSet M (capH X₀) U b c) := by
  rw [Set.disjoint_left]
  rintro e ⟨-, -, h1⟩ ⟨-, h2, -⟩
  linarith

/-- **The arrivals of a slot window** are the composites in `[s_{i+1}, s_{j+1})`. -/
theorem sum_arr {i j : ℕ} (hij : i ≤ j) :
    ((∑ l ∈ Finset.Ioc i j, M.arr l : ℤ) : ℝ) =
      ((compositeSet M (capH X₀) U (M.slot (i + 1)) (M.slot (j + 1))).ncard : ℝ) := by
  induction j, hij using Nat.le_induction with
  | base =>
    simp only [Finset.Ioc_self, Finset.sum_empty, Int.cast_zero]
    have : compositeSet M (capH X₀) U (M.slot (i + 1)) (M.slot (i + 1)) = ∅ := by
      ext e; simp only [compositeSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, h1, h2⟩; linarith
    rw [this, Set.ncard_empty]; simp
  | succ j hij ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Int.cast_add, ih]
    have hlink := F.win.linked j
    rw [hlink]
    unfold compositeArr
    rw [compositeSet_union (M.slot_mono (by omega : i + 1 ≤ j + 1))
      (M.slot_mono (by omega : j + 1 ≤ j + 1 + 1)),
      Set.ncard_union_eq (compositeSet_disj _ _ _) (comp_finite F _ _) (comp_finite F _ _)]
    push_cast; ring

omit F in
lemma num_gt {e : RealisedIdx M →₀ ℕ} {a b : ℝ} (ha : (X₀ : ℝ) < a)
    (he : e ∈ rigidSet M U a b) : X₀ < num e := by
  have h1 := he.1.2.1
  rw [idxVal_ratOnly _ _ he.2] at h1
  exact_mod_cast lt_of_lt_of_le ha h1

/-- The rigid composites in `[a, b)` are counted by the smooth integers (`a > X₀`). -/
lemma ncard_rigidSet {a b : ℝ} (ha : (X₀ : ℝ) < a) :
    (rigidSet M U a b).ncard = (smoothIn X₀ a b).ncard := by
  rw [← Set.InjOn.ncard_image (f := num) (fun e he e' he' h => num_inj he.2 he'.2 h)]
  congr 1
  ext n
  simp only [mem_image, smoothIn, mem_setOf_eq]
  constructor
  · rintro ⟨e, he, rfl⟩
    have h1 := he.1.2.1
    have h2 := he.1.2.2
    rw [idxVal_ratOnly _ _ he.2] at h1 h2
    exact ⟨Std.num_smooth he.2, h1, h2⟩
  · rintro ⟨hsm, h1, h2⟩
    obtain ⟨e, hv, hrat⟩ := exists_rat_elem M U hsm
    have hr : RatOnly e := fun k => by
      by_contra hk
      obtain ⟨p, hp⟩ := hrat _ (Finsupp.mem_support_iff.mpr hk)
      cases hp
    have hnum : num e = n := by
      rw [idxVal_ratOnly _ _ hr] at hv; exact_mod_cast hv
    refine ⟨e, ⟨⟨?_, by rw [hv]; exact h1, by rw [hv]; exact h2⟩, hr⟩, hnum⟩
    rw [composite_iff hr, hnum]
    have hnX : X₀ < n := by exact_mod_cast lt_of_lt_of_le ha h1
    have hX2 : 2 ≤ X₀ := by
      have := F.win.big
      have : (2 : ℝ) ≤ X₀ := by linarith
      exact_mod_cast this
    refine ⟨by omega, fun hpr => ?_⟩
    have := (Nat.mem_smoothNumbers.mp hsm).2 n (by simp [Nat.primeFactorsList_prime hpr])
    omega

omit F in
/-- An element of `𝒜` (definition (5)) has its value in `absSet`. -/
lemma mem_absSet_of_ownAbs (hok : RealisedOK M (capH X₀) U) {e : RealisedIdx M →₀ ℕ}
    (he : OwnAbs M U e) : idxVal M (capH X₀) U e ∈ absSet X₀ (DM M U) := by
  classical
  obtain ⟨hlog, hr, hlt⟩ := he
  refine ⟨hlog, mapE M e, live_mapE M U e, ?_, eval_mapE M U e, ?_⟩
  · intro i hi
    have hsub := Finsupp.mapDomain_support hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsub
    rw [pval_toPIdx]
    exact hok.one_lt j
  · obtain ⟨hk, hne⟩ := latk_mem (M := M) hr
    refine ⟨latk M e, ?_, fun k' hk' => ?_, hlt⟩
    · rw [mapE_apply_inr, dif_pos hk]; exact hne
    · rw [mapE_apply_inr] at hk'
      split_ifs at hk' with h
      · exact le_latk e ⟨h, hk'⟩
      · exact absurd rfl hk'

/-- The absorbed composites in `[a, b)` are counted by `𝒜 ∩ [a, b)` (`a > X₀`). -/
lemma ncard_absPart {a b : ℝ} (ha : (X₀ : ℝ) < a) :
    (absPart M U a b).ncard = (absSet X₀ (DM M U) ∩ Set.Ico a b).ncard := by
  classical
  rw [← Set.InjOn.ncard_image (f := idxVal M (capH X₀) U) (fun e _ e' _ h => F.tie e e' h)]
  congr 1
  ext s
  simp only [mem_image, absPart, compositeSet, mem_setOf_eq, mem_inter_iff, mem_Ico]
  constructor
  · rintro ⟨e, ⟨⟨-, h1, h2⟩, hA⟩, rfl⟩
    exact ⟨mem_absSet_of_ownAbs F.win.ok hA, h1, h2⟩
  · rintro ⟨hA, h1, h2⟩
    obtain ⟨e, he2, hv⟩ := F.win.comp s (lt_of_lt_of_le ha h1) (Or.inr hA)
    refine ⟨e, ⟨⟨he2, by rw [hv]; exact h1, by rw [hv]; exact h2⟩, ?_⟩, hv⟩
    -- `e` is the witness of `s ∈ 𝒜` (no ties)
    obtain ⟨hlog, e', he', -, hval, k, hk, hkmax, hy⟩ := hA
    obtain ⟨f, rfl⟩ := exists_mapE (U := U) he'
    rw [eval_mapE] at hval
    have hfe : f = e := F.tie f e (by rw [hval, hv])
    subst hfe
    have hkp : placedAt M k := he' k hk
    rw [mapE_apply_inr, dif_pos hkp] at hk
    have hr : ¬ RatOnly f := fun h => hk (h ⟨k, hkp⟩)
    have hlat : latk M f = k := by
      apply le_antisymm
      · apply csSup_le (jitIdx_nonempty hr)
        rintro k' ⟨hk', hne⟩
        apply hkmax
        rw [mapE_apply_inr, dif_pos hk']; exact hne
      · exact le_latk f ⟨hkp, hk⟩
    refine ⟨by rw [hval]; exact hlog, hr, ?_⟩
    rw [hlat, hval]; exact hy

/-- **The partition of the composites of a window** (proof of Lemma 3.9): rigid, absorbed, and
`C_jit`. -/
lemma ncard_comp_split {a b : ℝ} (ha : (X₀ : ℝ) < a) :
    ((compositeSet M (capH X₀) U a b).ncard : ℝ) =
      (smoothIn X₀ a b).ncard + (absSet X₀ (DM M U) ∩ Set.Ico a b).ncard + Cjit M U a b := by
  classical
  have hfin := comp_finite F a b
  have e1 : compositeSet M (capH X₀) U a b =
      (rigidSet M U a b ∪ absPart M U a b) ∪ cjitSet M U a b := by
    ext e
    simp only [rigidSet, absPart, cjitSet, mem_union, mem_setOf_eq]
    constructor
    · intro he
      by_cases hr : RatOnly e
      · exact Or.inl (Or.inl ⟨he, hr⟩)
      · by_cases hA : OwnAbs M U e
        · exact Or.inl (Or.inr ⟨he, hA⟩)
        · exact Or.inr ⟨he, hr, hA⟩
    · rintro ((⟨he, -⟩ | ⟨he, -⟩) | ⟨he, -, -⟩) <;> exact he
  have hd1 : Disjoint (rigidSet M U a b) (absPart M U a b) := by
    rw [Set.disjoint_left]
    rintro e ⟨-, hr⟩ ⟨-, hA⟩
    exact hA.2.1 hr
  have hd2 : Disjoint (rigidSet M U a b ∪ absPart M U a b) (cjitSet M U a b) := by
    rw [Set.disjoint_left]
    rintro e (⟨-, hr⟩ | ⟨-, hA⟩) ⟨-, hr', hA'⟩
    · exact hr' hr
    · exact hA' hA
  have hf1 : (rigidSet M U a b).Finite := hfin.subset fun e he => he.1
  have hf2 : (absPart M U a b).Finite := hfin.subset fun e he => he.1
  have hf3 : (cjitSet M U a b).Finite := hfin.subset fun e he => he.1
  rw [e1, Set.ncard_union_eq hd2 (hf1.union hf2) hf3, Set.ncard_union_eq hd1 hf1 hf2,
    ncard_rigidSet F ha, ncard_absPart F ha]
  unfold Cjit
  push_cast; ring

end Count

/-! ### The jump part between two heights -/

section JumpCount

lemma smoothCount_ceil (X₀ : ℕ) {s : ℝ} (hs : 0 < s) :
    Rankin.smoothCount X₀ ((⌈s⌉₊ : ℝ) - 1) = (Nat.smoothNumbersUpTo (⌈s⌉₊ - 1) X₀).card := by
  unfold Rankin.smoothCount
  rw [ceil_sub_one_cast hs, Nat.floor_natCast]

lemma mem_upTo_iff {s : ℝ} (hs : 0 < s) (n : ℕ) :
    n ∈ Nat.smoothNumbersUpTo (⌈s⌉₊ - 1) X₀ ↔ n ∈ Nat.smoothNumbers X₀ ∧ (n : ℝ) < s := by
  rw [Nat.mem_smoothNumbersUpTo]
  have h1 := one_le_ceil hs
  constructor
  · rintro ⟨hn, hsm⟩
    refine ⟨hsm, ?_⟩
    have : (n : ℝ) ≤ ((⌈s⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    rw [← ceil_sub_one_cast hs] at this
    linarith [ceil_sub_one_lt hs]
  · rintro ⟨hsm, hn⟩
    refine ⟨?_, hsm⟩
    have : n < ⌈s⌉₊ := by
      by_contra hc; push_neg at hc
      have := Nat.ceil_le.mp hc
      linarith
    omega

/-- `#(smooth ∩ [a, b)) = S(⌈b⌉ - 1) - S(⌈a⌉ - 1)`. -/
lemma smoothIn_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ((smoothIn X₀ a b).ncard : ℝ) = (Rankin.smoothCount X₀ ((⌈b⌉₊ : ℝ) - 1) : ℝ) -
      Rankin.smoothCount X₀ ((⌈a⌉₊ : ℝ) - 1) := by
  classical
  have hb : 0 < b := by linarith
  rw [smoothCount_ceil X₀ ha, smoothCount_ceil X₀ hb]
  set A := Nat.smoothNumbersUpTo (⌈a⌉₊ - 1) X₀
  set B := Nat.smoothNumbersUpTo (⌈b⌉₊ - 1) X₀
  have hsub : A ⊆ B := fun n hn => by
    rw [mem_upTo_iff ha] at hn; rw [mem_upTo_iff hb]; exact ⟨hn.1, by linarith [hn.2]⟩
  have heq : smoothIn X₀ a b = ↑(B \ A) := by
    ext n
    simp only [smoothIn, mem_setOf_eq, Finset.coe_sdiff, mem_diff, Finset.mem_coe, B, A,
      mem_upTo_iff ha, mem_upTo_iff hb, not_and, not_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun _ => h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2 h1, h3⟩
  rw [heq, Set.ncard_coe_finset, Finset.card_sdiff_of_subset hsub, Nat.cast_sub
    (Finset.card_le_card hsub)]

lemma countAlt_sub {A : Set ℝ} (hA : LocFin A) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    countAlt A b - countAlt A a = ((A ∩ Set.Ico a b).ncard : ℝ) := by
  unfold countAlt
  have e : A ∩ Set.Ico 1 b = (A ∩ Set.Ico 1 a) ∪ (A ∩ Set.Ico a b) := by
    ext x; simp only [mem_inter_iff, mem_Ico, mem_union]
    constructor
    · rintro ⟨hx, h1, h2⟩
      rcases lt_or_ge x a with h | h
      · exact Or.inl ⟨hx, h1, h⟩
      · exact Or.inr ⟨hx, h, h2⟩
    · rintro (⟨hx, h1, h2⟩ | ⟨hx, h1, h2⟩)
      · exact ⟨hx, h1, by linarith⟩
      · exact ⟨hx, by linarith, h2⟩
  have hd : Disjoint (A ∩ Set.Ico 1 a) (A ∩ Set.Ico a b) := by
    rw [Set.disjoint_left]; rintro x ⟨-, -, h1⟩ ⟨-, h2, -⟩; linarith
  have hf1 : (A ∩ Set.Ico 1 a).Finite :=
    (hA b).subset fun x hx => ⟨hx.1, by simp only [mem_Iic]; linarith [hx.2.2]⟩
  have hf2 : (A ∩ Set.Ico a b).Finite :=
    (hA b).subset fun x hx => ⟨hx.1, by simp only [mem_Iic]; linarith [hx.2.2]⟩
  rw [e, Set.ncard_union_eq hd hf1 hf2]; push_cast; ring

end JumpCount

/-! ### Lemma 3.9 -/

section Excess

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

/-- **`#comp([a, b)) = C_jit([a, b)) + J(b-) - J(a-)`** for `X₀ < a ≤ b`. -/
theorem comp_eq {a b : ℝ} (ha : (X₀ : ℝ) < a) (hab : a ≤ b) :
    ((compositeSet M (capH X₀) U a b).ncard : ℝ) =
      Cjit M U a b + (jumpL X₀ (DM M U) b - jumpL X₀ (DM M U) a) := by
  have h16 := F.win.big
  have ha0 : 0 < a := by linarith
  rw [ncard_comp_split F ha, smoothIn_eq ha0 hab,
    ← countAlt_sub (absSet_locFin F.win.fin) (by linarith) hab]
  unfold jumpL
  ring

/-- **Lemma 3.9 (excess identity), upper bound**: for the slot window `W = (i, j]`,
`exc(W) ≤ C_jit(W) - ℓ_jit(W) + 2`, with `W` read as `[s_{i+1}, s_{j+1})`. -/
theorem exc_le {i j : ℕ} (hij : i ≤ j) :
    (exc M.arr i j : ℝ) ≤ Cjit M U (M.slot (i + 1)) (M.slot (j + 1)) - ellW θ M U i j + 2 := by
  classical
  have hs1 := slot_gt F (Nat.le_add_left 1 i)
  have hs2 := slot_gt F (Nat.le_add_left 1 j)
  have hss : M.slot (i + 1) ≤ M.slot (j + 1) := M.slot_mono (by omega)
  have hexc : (exc M.arr i j : ℝ) =
      ((compositeSet M (capH X₀) U (M.slot (i + 1)) (M.slot (j + 1))).ncard : ℝ) -
        ((j : ℝ) - i) := by
    unfold exc; push_cast; rw [← sum_arr F hij]; push_cast; ring
  rw [hexc, comp_eq F hs1 hss]
  have hlo := level_lower F (Nat.le_add_left 1 j)
  have hup := level_upper F (Nat.le_add_left 1 i)
  have hlev : M.level (j + 1) - M.level (i + 1) = (j : ℝ) - i := by
    unfold SlotModel.level; push_cast; ring
  -- the continuous mass of `W` is at least `ℓ_jit(W) - 1`
  have hmass : (ellW θ M U i j : ℝ) - 1 ≤
      contD θ X₀ (DM M U) (M.slot (j + 1)) - contD θ X₀ (DM M U) (M.slot (i + 1)) := by
    set S := (Finset.Ioc i j).filter (ContSlot θ M U)
    have hcm : contD θ X₀ (DM M U) (M.slot (i + 1)) ≤ contD θ X₀ (DM M U) (M.slot (j + 1)) :=
      F.win.cmono _ _ hs1.le hss
    rcases S.eq_empty_or_nonempty with hS | hne
    · have : ellW θ M U i j = 0 := by
        unfold ellW; exact Finset.card_eq_zero.mpr hS
      rw [this]; push_cast; linarith
    · have hm := cont_mass_card F S (fun l hl => (Finset.mem_filter.mp hl).2) hne
      have hmin := Finset.mem_Ioc.mp (Finset.mem_filter.mp (S.min'_mem hne)).1
      have hmax := Finset.mem_Ioc.mp (Finset.mem_filter.mp (S.max'_mem hne)).1
      have h1 : M.slot (i + 1) ≤ M.slot (S.min' hne) := M.slot_mono (by omega)
      have h2 : M.slot (S.max' hne) ≤ M.slot (j + 1) := M.slot_mono (by omega)
      have c1 := F.win.cmono _ _ hs1.le h1
      have c2 := F.win.cmono _ _ (hs1.le.trans (h1.trans (M.slot_mono
        (S.min'_le_max' hne)))) h2
      change (S.card : ℝ) - 1 ≤ _
      linarith
  linarith

end Excess

/-! ### The sandwich of the proof of Theorem 6.6(ii) -/

section Sandwich

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ}

lemma slots_below_finite (M : SlotModel X₀) (b : ℝ) : {l | M.slot l < b}.Finite := by
  obtain ⟨k, hk⟩ := slots_unbounded M b
  refine (Set.finite_lt_nat (k + 1)).subset fun l hl => ?_
  simp only [mem_setOf_eq] at hl ⊢
  by_contra hc; push_neg at hc
  have := M.slot_mono hc
  linarith

lemma ellI_finite (θ : ℝ) (M : SlotModel X₀) (U : ℕ → ℝ) (a b : ℝ) :
    {l | ContSlot θ M U l ∧ a ≤ M.slot l ∧ M.slot l < b}.Finite :=
  (slots_below_finite M b).subset fun _ hl => hl.2.2

variable (F : ExcFacts θ M U)
include F

lemma cjit_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    Cjit M U a b ≤ Cjit M U a' b' := by
  unfold Cjit
  have hfin : (cjitSet M U a' b').Finite := (comp_finite F a' b').subset fun _ he => he.1
  have hsub : cjitSet M U a b ⊆ cjitSet M U a' b' := by
    rintro e ⟨⟨h2, h1, h3⟩, hr, hA⟩
    exact ⟨⟨h2, by linarith, by linarith⟩, hr, hA⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- **The sandwich** (proof of Theorem 6.6(ii)): for `W = (i, j]` with integer hull
`I = [⌊s_{i+1}⌋, ⌈s_{j+1}⌉)`, `ℓ_jit(I) ≤ ℓ_jit(W) + 4`, `ℓ_jit(W) ≤ ℓ_jit(I) + 1` and
`exc(W) ≤ C_jit(I) - ℓ_jit(I) + 6`. -/
theorem sandwich {i j : ℕ} (hij : i ≤ j) :
    ellI θ M U (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) ≤ ellW θ M U i j + 4 ∧
    ellW θ M U i j ≤ ellI θ M U (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) + 1 ∧
    (exc M.arr i j : ℝ) ≤ Cjit M U (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) -
      ellI θ M U (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) + 6 := by
  classical
  set a' := M.slot (i + 1)
  set b' := M.slot (j + 1)
  set aI : ℝ := (⌊a'⌋₊ : ℝ)
  set bI : ℝ := (⌈b'⌉₊ : ℝ)
  have hs1 : (X₀ : ℝ) < a' := slot_gt F (Nat.le_add_left 1 i)
  have hss : a' ≤ b' := M.slot_mono (by omega)
  have ha0 : 0 ≤ a' := by have := F.win.big; linarith
  have haI : aI ≤ a' := Nat.floor_le ha0
  have haI' : a' < aI + 1 := Nat.lt_floor_add_one a'
  have hbI : b' ≤ bI := Nat.le_ceil b'
  have hbI' : bI < b' + 1 := Nat.ceil_lt_add_one (ha0.trans hss)
  have hXa : (X₀ : ℝ) ≤ aI := by
    have : X₀ ≤ ⌊a'⌋₊ := Nat.le_floor hs1.le
    show (X₀ : ℝ) ≤ (⌊a'⌋₊ : ℝ)
    exact_mod_cast this
  set S := {l | ContSlot θ M U l ∧ aI ≤ M.slot l ∧ M.slot l < bI}
  set Fw := (Finset.Ioc i j).filter (ContSlot θ M U)
  have hSfin : S.Finite := ellI_finite θ M U aI bI
  have hSI : ellI θ M U aI bI = S.ncard := rfl
  have hFw : ((Fw : Set ℕ)).ncard = ellW θ M U i j := by rw [Set.ncard_coe_finset]; rfl
  -- `ℓ_jit(I) ≤ ℓ_jit(W) + 4`
  have h1 : ellI θ M U aI bI ≤ ellW θ M U i j + 4 := by
    set A := {l | ContSlot θ M U l ∧ aI ≤ M.slot l ∧ M.slot l ≤ a'}
    set B := {l | ContSlot θ M U l ∧ b' ≤ M.slot l ∧ M.slot l ≤ bI}
    have hA : A.ncard ≤ 2 := cont_starts_le_two F hXa haI'.le
    have hB : B.ncard ≤ 2 := cont_starts_le_two F (hXa.trans (haI.trans hss)) hbI'.le
    have hsub : S ⊆ (A ∪ ↑Fw) ∪ B := by
      rintro l ⟨hc, hl1, hl2⟩
      rcases Nat.lt_or_ge i l with h | h
      · rcases Nat.lt_or_ge j l with h' | h'
        · right
          exact ⟨hc, M.slot_mono (by omega), hl2.le⟩
        · left; right
          simp only [Fw, Finset.coe_filter, Finset.mem_Ioc, mem_setOf_eq]
          exact ⟨⟨h, h'⟩, hc⟩
      · left; left
        exact ⟨hc, hl1, M.slot_mono (by omega)⟩
    have := (Set.ncard_le_ncard hsub ((((ellI_finite θ M U aI (a' + 1)).subset
      fun l hl => ⟨hl.1, hl.2.1, by linarith [hl.2.2]⟩).union (Finset.finite_toSet Fw)).union
      ((ellI_finite θ M U b' (bI + 1)).subset fun l hl => ⟨hl.1, hl.2.1, by linarith [hl.2.2]⟩)))
    have h3 := Set.ncard_union_le (A ∪ ↑Fw) B
    have h4 := Set.ncard_union_le A ↑Fw
    rw [hSI]
    omega
  -- `ℓ_jit(W) ≤ ℓ_jit(I) + 1`
  have h2 : ellW θ M U i j ≤ ellI θ M U aI bI + 1 := by
    set E := {l | l ∈ Fw ∧ M.slot l = bI}
    have hEfin : E.Finite := (Finset.finite_toSet Fw).subset fun l hl => hl.1
    have hE : E.ncard ≤ 1 := by
      rw [Set.ncard_le_one (hs := hEfin)]
      rintro l ⟨hl, hl'⟩ l' ⟨hm, hm'⟩
      have hcl := (Finset.mem_filter.mp hl).2
      have hcm := (Finset.mem_filter.mp hm).2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := cont_slot_ne F h hcl hcm; linarith
      · have := cont_slot_ne F h hcm hcl; linarith
    have hsub : (↑Fw : Set ℕ) ⊆ S ∪ E := by
      intro l hl
      have hl' := hl
      simp only [Fw, Finset.coe_filter, Finset.mem_Ioc, mem_setOf_eq] at hl'
      have hlo : a' ≤ M.slot l := M.slot_mono (by omega)
      have hhi : M.slot l ≤ b' := M.slot_mono (by omega)
      rcases lt_or_eq_of_le (hhi.trans hbI) with h | h
      · left; exact ⟨hl'.2, haI.trans hlo, h⟩
      · right; exact ⟨hl, h⟩
    have := (Set.ncard_le_ncard hsub (hSfin.union hEfin)).trans (Set.ncard_union_le S E)
    rw [hFw] at this
    rw [hSI]
    omega
  refine ⟨h1, h2, ?_⟩
  have hexc := exc_le F hij
  have hC := cjit_mono F haI hbI
  have h1' : (ellI θ M U aI bI : ℝ) ≤ ellW θ M U i j + 4 := by exact_mod_cast h1
  linarith

end Sandwich

/-! ### The continuous mass of a slot window is at most `ℓ_jit(W) + 1` -/

section Mass

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

/-- The jump points of `T` in `[a, b)`: rigid integers and values of `𝒜`. -/
def jumpPts (X₀ : ℕ) (D : PrimeData) (a b : ℝ) : Set ℝ :=
  ((fun n : ℕ => (n : ℝ)) '' smoothIn X₀ a b) ∪ (absSet X₀ D ∩ Set.Ico a b)

omit F in
lemma smoothIn_finite (a b : ℝ) : (smoothIn X₀ a b).Finite :=
  (Set.finite_lt_nat ⌈b⌉₊).subset fun n hn => by
    simp only [mem_setOf_eq]
    have := hn.2.2
    exact_mod_cast lt_of_lt_of_le this (Nat.le_ceil b)

lemma ncard_jumpPts {a b : ℝ} (ha : (X₀ : ℝ) < a) (hab : a ≤ b) :
    ((jumpPts X₀ (DM M U) a b).ncard : ℝ) = jumpL X₀ (DM M U) b - jumpL X₀ (DM M U) a := by
  have h16 := F.win.big
  have ha0 : 0 < a := by linarith
  have hfA : (absSet X₀ (DM M U) ∩ Set.Ico a b).Finite :=
    ((absSet_locFin F.win.fin) b).subset fun x hx =>
      ⟨hx.1, by simp only [mem_Iic]; linarith [hx.2.2]⟩
  have hd : Disjoint ((fun n : ℕ => (n : ℝ)) '' smoothIn X₀ a b)
      (absSet X₀ (DM M U) ∩ Set.Ico a b) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, ⟨hsm, h1, -⟩, rfl⟩ ⟨hA, -⟩
    exact F.unit n (lt_of_lt_of_le ha h1) hsm hA
  unfold jumpPts
  rw [Set.ncard_union_eq hd ((smoothIn_finite a b).image _) hfA,
    Set.ncard_image_of_injective _ Nat.cast_injective]
  have e1 := smoothIn_eq (X₀ := X₀) ha0 hab
  have e2 := countAlt_sub (A := absSet X₀ (DM M U)) (absSet_locFin F.win.fin)
    (by linarith : (1 : ℝ) ≤ a) hab
  unfold jumpL
  push_cast
  linarith

/-- A slot that is not continuous starts at a jump point, strictly below any later level's
start: if `l ≤ l'`, `l ≠ l'` and `s_l = s_{l'}` then `l` is continuous. -/
lemma noncont_start {l l' : ℕ} (hl : 1 ≤ l) (hll : l < l') (hnc : ¬ ContSlot θ M U l) :
    M.slot l < M.slot l' ∧ M.slot l ∈ jumpPts X₀ (DM M U) (M.slot l) (M.slot l') := by
  classical
  have W := F.win
  have hs := slot_gt F hl
  have hs0 : 0 < M.slot l := by have := W.big; linarith
  have hlo := level_lower F hl
  have hlt : (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot l) + contD θ X₀ (DM M U) (M.slot l) <
      M.level l := lt_of_le_of_ne hlo fun h => hnc ⟨hl, h⟩
  have hTs := M.level_le_T_slot l
  rw [W.split _ hs.le] at hTs
  have hdiff := jumpD_sub_jumpL (X₀ := X₀) (DM M U) W.fin hs0
  -- the jump at `s_l` is exactly `1`
  have hle1 : jumpD X₀ (DM M U) (M.slot l) - jumpL X₀ (DM M U) (M.slot l) ≤ 1 := by
    rw [hdiff]
    by_cases h1 : ∃ n : ℕ, (n : ℝ) = M.slot l ∧ n ∈ Nat.smoothNumbers X₀
    · obtain ⟨n, hn, hsm⟩ := h1
      have hnA := F.unit n (by rw [hn]; exact hs) hsm
      rw [hn] at hnA
      rw [if_pos ⟨n, hn, hsm⟩, if_neg hnA]; norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hlt' : M.slot l < M.slot l' := by
    rcases (M.slot_mono hll.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := M.level_le_T_slot l'
      rw [← h, W.split _ hs.le] at h2
      have : M.level l + 1 ≤ M.level l' := by
        unfold SlotModel.level
        have : (l : ℝ) + 1 ≤ l' := by exact_mod_cast hll
        linarith
      linarith
  refine ⟨hlt', ?_⟩
  have hpos : 0 < jumpD X₀ (DM M U) (M.slot l) - jumpL X₀ (DM M U) (M.slot l) := by linarith
  rw [hdiff] at hpos
  by_cases h1 : ∃ n : ℕ, (n : ℝ) = M.slot l ∧ n ∈ Nat.smoothNumbers X₀
  · obtain ⟨n, hn, hsm⟩ := h1
    left
    exact ⟨n, ⟨hsm, by rw [hn], by rw [hn]; exact hlt'⟩, hn⟩
  · rw [if_neg h1] at hpos
    by_cases hA : M.slot l ∈ absSet X₀ (DM M U)
    · right; exact ⟨hA, le_rfl, hlt'⟩
    · rw [if_neg hA] at hpos; norm_num at hpos

/-- **The continuous mass of `W = (i, j]` is at most `ℓ_jit(W) + 1`.** -/
theorem mass_le {i j : ℕ} (hij : i ≤ j) :
    contD θ X₀ (DM M U) (M.slot (j + 1)) - contD θ X₀ (DM M U) (M.slot (i + 1)) ≤
      ellW θ M U i j + 1 := by
  classical
  set a' := M.slot (i + 1)
  set b' := M.slot (j + 1)
  have hs1 : (X₀ : ℝ) < a' := slot_gt F (Nat.le_add_left 1 i)
  have hss : a' ≤ b' := M.slot_mono (by omega)
  have hlo := level_lower F (Nat.le_add_left 1 j)
  have hup := level_upper F (Nat.le_add_left 1 i)
  have hlo' := level_lower F (Nat.le_add_left 1 i)
  have hup' := level_upper F (Nat.le_add_left 1 j)
  have hlev : M.level (j + 1) - M.level (i + 1) = (j : ℝ) - i := by
    unfold SlotModel.level; push_cast; ring
  -- the non-continuous slots of `W` inject into the jump points of `[a', b')`
  set N := (Finset.Ioc i j).filter (fun l => ¬ ContSlot θ M U l)
  have hinj : (N.card : ℝ) ≤ jumpL X₀ (DM M U) b' - jumpL X₀ (DM M U) a' := by
    rw [← ncard_jumpPts F hs1 hss]
    have hfin : (jumpPts X₀ (DM M U) a' b').Finite := by
      unfold jumpPts
      exact ((smoothIn_finite a' b').image _).union (((absSet_locFin F.win.fin) b').subset
        fun x hx => ⟨hx.1, by simp only [mem_Iic]; linarith [hx.2.2]⟩)
    have := Set.ncard_le_ncard_of_injOn (fun l => M.slot l) (s := (N : Set ℕ))
      (t := jumpPts X₀ (DM M U) a' b') ?_ ?_ hfin
    · rw [Set.ncard_coe_finset] at this; exact_mod_cast this
    · intro l hl
      have hl' := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      have hI := Finset.mem_Ioc.mp hl'.1
      obtain ⟨hlt, hmem⟩ := noncont_start F (by omega) (by omega : l < j + 1) hl'.2
      have hal : a' ≤ M.slot l := M.slot_mono (by omega)
      rcases hmem with ⟨n, ⟨hsm, h1, h2⟩, hn⟩ | ⟨hA, h1, h2⟩
      · left
        simp only at hn
        exact ⟨n, ⟨hsm, by rw [hn]; exact hal, by rw [hn]; exact hlt⟩, hn⟩
      · right; exact ⟨hA, hal, hlt⟩
    · intro l hl l' hl' heq
      have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hl')
      have hI1 := Finset.mem_Ioc.mp h1.1
      have hI2 := Finset.mem_Ioc.mp h2.1
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := (noncont_start F (by omega) h h1.2).1
        simp only at heq; linarith
      · have := (noncont_start F (by omega) h h2.2).1
        simp only at heq; linarith
  have hcard : (N.card : ℝ) + ellW θ M U i j = (j : ℝ) - i := by
    unfold ellW
    have := Finset.card_filter_add_card_filter_not (s := Finset.Ioc i j)
      (ContSlot θ M U)
    rw [Nat.card_Ioc] at this
    have h' : (((Finset.Ioc i j).filter (ContSlot θ M U)).card : ℝ) + N.card = j - i := by
      rw [← Nat.cast_sub hij]; exact_mod_cast this
    linarith
  linarith

end Mass

end Queue6

end
