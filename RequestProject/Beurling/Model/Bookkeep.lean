module

public import RequestProject.Beurling.Queue6.Excess
public import RequestProject.Beurling.Model.T0Mono

/-!
# The bookkeeping identity of §5.3 for physical windows

"Every level crossing of `T` is either a jump slot or a continuous slot, so on every window `W`,
`#{continuous slots in W} = ∫_W T'_cont ± 2`" (§5.3, *Bookkeeping*). For the constructed model
(off `𝒩₌`, `Queue6.ExcFacts`) and a physical window `[a, b)` with `b ≥ X₀`:

* `ellI_le_mass` : `ℓ_jit([a, b)) ≤ C(b) - C(max(a, X₀)) + 1` (`cont_mass_card`);
* `mass_le_ellI` : `C(b) - C(max(a, X₀)) ≤ ℓ_jit([a, b)) + 2` (`mass_le` on the slot window
  covering `[a, b)`, whose end slots add at most one continuous slot; below `s_1`,
  `C(s_1) ≤ ϑ ≤ 1/2`);
* `bookkeeping` : `|ℓ_jit([a, b)) - (C(b) - C(max(a, X₀)))| ≤ 2`.

Here `C = contD` is the continuous part of the target (6) and `ℓ_jit = Queue6.ellI`.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono BModel QueueDet Queue6

namespace BModel

variable {X₀ : ℕ} {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

lemma ellI_eq_max (a b : ℝ) : ellI θ M U a b = ellI θ M U (max a X₀) b := by
  unfold ellI
  congr 1
  ext l
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hc, h1, h2⟩
    exact ⟨hc, max_le h1 (slot_gt F hc.1).le, h2⟩
  · rintro ⟨hc, h1, h2⟩
    exact ⟨hc, (le_max_left _ _).trans h1, h2⟩

/-- `ℓ_jit([a, b)) ≤ C(b) - C(max(a, X₀)) + 1`. -/
theorem ellI_le_mass {a b : ℝ} (hab : a ≤ b) (hb : (X₀ : ℝ) ≤ b) :
    (ellI θ M U a b : ℝ) ≤
      contD θ X₀ (DM M U) b - contD θ X₀ (DM M U) (max a X₀) + 1 := by
  classical
  set a' := max a (X₀ : ℝ)
  rw [ellI_eq_max F]
  set S := {l | ContSlot θ M U l ∧ a' ≤ M.slot l ∧ M.slot l < b}
  have hfin : S.Finite := ellI_finite θ M U a' b
  rcases S.eq_empty_or_nonempty with h0 | hne
  · have : ellI θ M U a' b = 0 := by
      unfold ellI; rw [show {l | ContSlot θ M U l ∧ a' ≤ M.slot l ∧ M.slot l < b} = S from rfl,
        h0, Set.ncard_empty]
    rw [this]
    have := F.win.cmono _ _ (le_max_right _ _) (max_le hab hb); push_cast; linarith
  · set T := hfin.toFinset
    have hTne : T.Nonempty := by
      obtain ⟨l, hl⟩ := hne; exact ⟨l, hfin.mem_toFinset.mpr hl⟩
    have hmem : ∀ l ∈ T, ContSlot θ M U l ∧ a' ≤ M.slot l ∧ M.slot l < b := fun l hl =>
      hfin.mem_toFinset.mp hl
    have hm := cont_mass_card F T (fun l hl => (hmem l hl).1) hTne
    have h1 := hmem _ (T.max'_mem hTne)
    have h2 := hmem _ (T.min'_mem hTne)
    have hc1 := F.win.cmono _ _ (le_max_right _ _) h2.2.1
    have hc2 := F.win.cmono _ _ ((le_max_right _ _).trans (h2.2.1.trans
      (M.slot_mono (T.min'_le_max' hTne)))) h1.2.2.le
    have hcard : ellI θ M U a' b = T.card := by
      unfold ellI; exact Set.ncard_eq_toFinset_card _ hfin
    rw [hcard]
    linarith

lemma jumpL_nonneg {s : ℝ} (hs : (X₀ : ℝ) < s) : 0 ≤ jumpL X₀ (DM M U) s := by
  unfold jumpL countAlt
  have h1 : (X₀ : ℝ) ≤ (⌈s⌉₊ : ℝ) - 1 := by
    have : X₀ < ⌈s⌉₊ := Nat.lt_ceil.mpr hs
    have : (X₀ : ℝ) + 1 ≤ ⌈s⌉₊ := by exact_mod_cast this
    linarith
  have := smoothCount_mono X₀ h1
  have : (0 : ℝ) ≤ ((absSet X₀ (DM M U) ∩ Set.Ico 1 s).ncard : ℝ) := Nat.cast_nonneg _
  linarith

/-- Below the first slot, the continuous mass is at most `ϑ ≤ 1/2`. -/
lemma contD_slot_one_le : contD θ X₀ (DM M U) (M.slot 1) ≤ 1 / 2 := by
  have hlo := level_lower F (le_refl 1)
  have hj := jumpL_nonneg F (slot_gt F (le_refl 1))
  have hϑ := M.hϑ
  unfold SlotModel.level at hlo
  push_cast at hlo
  linarith

/-- **`C(b) - C(max(a, X₀)) ≤ ℓ_jit([a, b)) + 2`.** -/
theorem mass_le_ellI {a b : ℝ} (hab : a ≤ b) (hb : (X₀ : ℝ) ≤ b) :
    contD θ X₀ (DM M U) b - contD θ X₀ (DM M U) (max a X₀) ≤ (ellI θ M U a b : ℝ) + 2 := by
  classical
  set a' := max a (X₀ : ℝ) with ha'
  have hXa : (X₀ : ℝ) ≤ a' := le_max_right _ _
  have hab' : a' ≤ b := max_le hab hb
  rw [ellI_eq_max F]
  have W := F.win
  have hC0 : contD θ X₀ (DM M U) X₀ = 0 := contD_at θ _
  rcases hab'.lt_or_eq with hlt | heq
  swap
  · rw [heq]; have : (0 : ℝ) ≤ ellI θ M U b b := Nat.cast_nonneg _; linarith
  -- the first slot at or above `b`
  have hex : ∃ l, b ≤ M.slot l := by
    obtain ⟨k, hk⟩ := slots_unbounded M b
    exact ⟨k + 1, hk.le⟩
  set j1 := Nat.find hex with hj1
  have hj1b : b ≤ M.slot j1 := Nat.find_spec hex
  have hj1min : ∀ l < j1, M.slot l < b := fun l hl => lt_of_not_ge (Nat.find_min hex hl)
  have hC1 := contD_slot_one_le F
  by_cases hj0 : j1 = 0
  · -- `b ≤ s_0 ≤ s_1`
    rw [hj0] at hj1b
    have hb1 : b ≤ M.slot 1 := hj1b.trans (M.slot_mono (Nat.zero_le 1))
    have h1 := W.cmono _ _ hb hb1
    have h2 := W.cmono _ _ le_rfl hXa
    have : (0 : ℝ) ≤ ellI θ M U a' b := Nat.cast_nonneg _
    linarith
  obtain ⟨j, hj⟩ : ∃ j, j1 = j + 1 := ⟨j1 - 1, by omega⟩
  rw [hj] at hj1b hj1min
  -- the continuous slots of `(i, j]` lie in `[a', b)`, except possibly `i + 1`
  have hcmono := W.cmono
  by_cases hs1 : a' < M.slot 1
  · have hm := mass_le F (Nat.zero_le j)
    have hsub : ((Finset.Ioc 0 j).filter (ContSlot θ M U) : Set ℕ) ⊆
        {l | ContSlot θ M U l ∧ a' ≤ M.slot l ∧ M.slot l < b} := by
      intro l hl
      rw [Finset.coe_filter, mem_setOf_eq, Finset.mem_Ioc] at hl
      exact ⟨hl.2, hs1.le.trans (M.slot_mono hl.1.1), hj1min l (by omega)⟩
    have hcard := Set.ncard_le_ncard hsub (ellI_finite θ M U a' b)
    rw [Set.ncard_coe_finset] at hcard
    have hW : (ellW θ M U 0 j : ℝ) ≤ ellI θ M U a' b := by
      unfold ellW ellI; exact_mod_cast hcard
    have h1 := hcmono _ _ hb hj1b
    have h2 := hcmono _ _ le_rfl hXa
    push_cast at hm
    linarith
  · push_neg at hs1
    -- the last slot at or below `a'`
    have hfin : {l | M.slot l ≤ a'}.Finite :=
      (slots_below_finite M (a' + 1)).subset fun l hl => by
        simp only [mem_setOf_eq] at hl ⊢; linarith
    have hne : (hfin.toFinset).Nonempty := ⟨1, hfin.mem_toFinset.mpr hs1⟩
    set i1 := hfin.toFinset.max' hne with hi1
    have hi1a : M.slot i1 ≤ a' := hfin.mem_toFinset.mp (hfin.toFinset.max'_mem hne)
    have hi1max : ∀ l, M.slot l ≤ a' → l ≤ i1 := fun l hl =>
      hfin.toFinset.le_max' _ (hfin.mem_toFinset.mpr hl)
    have hi1pos : 1 ≤ i1 := hi1max 1 hs1
    have hi1j : i1 ≤ j := by
      by_contra h; push_neg at h
      have := M.slot_mono (show j + 1 ≤ i1 by omega)
      linarith
    obtain ⟨i, hi⟩ : ∃ i, i1 = i + 1 := ⟨i1 - 1, by omega⟩
    rw [hi] at hi1a hi1max hi1pos hi1j
    have hij : i ≤ j := by omega
    have hm := mass_le F hij
    have hsub : ((Finset.Ioc i j).filter (ContSlot θ M U) : Set ℕ) ⊆
        insert (i + 1) {l | ContSlot θ M U l ∧ a' ≤ M.slot l ∧ M.slot l < b} := by
      intro l hl
      rw [Finset.coe_filter, mem_setOf_eq, Finset.mem_Ioc] at hl
      by_cases hli : l = i + 1
      · exact Or.inl hli
      · right
        refine ⟨hl.2, ?_, hj1min l (by omega)⟩
        by_contra hla; push_neg at hla
        have := hi1max l hla.le
        omega
    have hcard := Set.ncard_le_ncard hsub ((ellI_finite θ M U a' b).insert _)
    rw [Set.ncard_coe_finset] at hcard
    have hins := Set.ncard_insert_le (i + 1) {l | ContSlot θ M U l ∧ a' ≤ M.slot l ∧
      M.slot l < b}
    have hW : (ellW θ M U i j : ℝ) ≤ ellI θ M U a' b + 1 := by
      unfold ellW ellI; exact_mod_cast hcard.trans hins
    have hs := slot_gt F hi1pos
    have h1 := hcmono _ _ hb hj1b
    have h2 := hcmono _ _ hs.le hi1a
    push_cast at hm
    linarith

/-- **The bookkeeping identity of §5.3** for a physical window `[a, b)`, `b ≥ X₀`:
`|ℓ_jit([a, b)) - (C(b) - C(max(a, X₀)))| ≤ 2`. -/
theorem bookkeeping {a b : ℝ} (hab : a ≤ b) (hb : (X₀ : ℝ) ≤ b) :
    |(ellI θ M U a b : ℝ) - (contD θ X₀ (DM M U) b - contD θ X₀ (DM M U) (max a X₀))| ≤ 2 := by
  have h1 := ellI_le_mass F hab hb
  have h2 := mass_le_ellI F hab hb
  rw [abs_le]; constructor <;> linarith

end BModel
