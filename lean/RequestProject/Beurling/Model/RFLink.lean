module

public import RequestProject.Beurling.Model.WinLink
public import RequestProject.Beurling.Model.JLaw2
public import RequestProject.Beurling.RankFull.ModelJitter

/-!
# The construction in the RankFull window model, slot-indexed (Prop 6.11, Theorem 6.23(a),
Lemma A.5)

With `J = constructionLaw2` (decided slots `lawB`, values `valF`, `θ = 1 + 1/Λ`), the window model
of `RankFull` is used with `dec = decOf J` (the decided slots `n < N`, slot-indexed) and
`q = qOf J`. Here the model hypotheses of `prop_6_11_window`, `theorem_6_23a_model` and
`skeletonBound_jitter` are proved for the construction:

* `law2_hq` : decided values `> 1` (`hq`, `hq1`);
* `law2_hsmax` : a decided value `≤ V` has slot index `≤ 24V/7` (`hsmax`; the stopped law has
  `T(s) ≤ 3s` at its decided slots);
* `law2_hτ` : `τ_j ≤ q_n` when `j` decided slots precede `n`, `τ_j = max(X₀⁻, (j+1)/2)`
  (`hτ`, `hτq`);
* `meas_windowElems_dec` : every function of the window elements is measurable (the counts
  `skelCount`, `rankFullCount`, `configCount`, `cfgSkelCount`);
* the good events `G = goodLt` are nested and `F`-adapted (`good_meas`, `good_anti`);
* `winCount_le_windowElems2` : on the good event (all stages good, jitters in `[0, 1]`, `T ≤ 3x`
  up to `8b/7`), the realised elements with value in `[a, b)` inject into `windowElems`;
* `clusterUpTo_of_windows2` : `ClusterUpTo` from the window-model cluster bounds;
* `S3dHyp` : the (S3)(d) Euler-product bound of Lemma A.6, isolated (it needs Lemma 5.1 for the
  realised system, (F3′)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono RankFull.Config
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section RF

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`hq`: decided values are `> 1`.** -/
theorem law2_hq {N : ℕ} (ω : JitterΩ) (n : Fin N) (_ : ω ∈ (constructionLaw2 hc hev).A n) :
    1 < (constructionLaw2 hc hev).q n ω := by
  show 1 < valF θ X₀ n ω
  have := valF_ge_78 hc n ω
  have := slotF_ge hc n ω
  linarith [X₀_ge_two_pow hc.hX]

/-- **`hsmax`: a decided value below `V` has slot index `≤ 24V/7`.** -/
theorem law2_hsmax {N : ℕ} {V : ℝ} {Jw : Set ℝ} (hJw : Jw ⊆ Iic V) :
    ∀ ω, ∀ n : Fin N, ω ∈ (constructionLaw2 hc hev).A n → ∀ y ∈ Jw,
      (constructionLaw2 hc hev).q n ω ≤ y → (n : ℕ) ≤ ⌊24 * V / 7⌋₊ := by
  intro ω n hn y hy hqy
  have hB : ω ∈ lawB θ X₀ n := hn
  have hT := hB.2
  simp only [tStage, mem_setOf_eq] at hT
  have hq : valF θ X₀ n ω ≤ y := hqy
  have hyV : y ≤ V := hJw hy
  have h78 := valF_ge_78 hc n ω
  have hlev := (Mcl θ X₀ ω).level_le_T_slot (n + 1)
  unfold SlotModel.level at hlev
  rw [show (Mcl θ X₀ ω).ϑ = 1 / 2 from Mcl_ϑ hc ω] at hlev
  have hs : slotF θ X₀ n ω = (Mcl θ X₀ ω).slot (n + 1) := rfl
  rw [← hs] at hlev
  apply Nat.le_floor
  push_cast at hlev
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  linarith

omit hev in
/-- The label thresholds are `≥ 1`. -/
lemma tauL_ge_one {k : ℕ} (j : Fin k) : 1 ≤ tauL X₀ j := by
  unfold tauL Xm
  have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  exact le_max_of_le_left (by linarith [X₀_ge_two_pow hc.hX])

/-- **`hτ`: the label bound** `τ_j ≤ q_n` when `j` decided slots precede `n`. -/
theorem law2_hτ {N k : ℕ} :
    ∀ ω, ∀ n : Fin N, ω ∈ (constructionLaw2 hc hev).A n → ∀ j : Fin k,
      (j : ℕ) ≤ ((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card →
        tauL X₀ j ≤ (constructionLaw2 hc hev).q n ω := by
  classical
  intro ω n hn j hj
  show tauL X₀ j ≤ valF θ X₀ n ω
  have hcard : ((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card ≤
      lawRank θ X₀ ω n := by
    unfold lawRank
    rw [Nat.count_eq_card_filter_range]
    refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_)
      (fun i _ i' _ h => Fin.ext h)
    simp only [decOf, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_setOf_eq] at hi
    simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq]
    exact ⟨hi.2, hi.1.1⟩
  have hr := lawRank_le hc hev (ω := ω) (m := n)
  have hjn : ((j : ℕ) : ℝ) ≤ lawRank θ X₀ ω n := by exact_mod_cast hj.trans hcard
  have h78 := valF_ge_78 hc n ω
  have hsX := slotF_ge hc n ω
  have h16 := X₀_ge_two_pow hc.hX
  unfold tauL
  exact max_le (valF_ge_Xm hc n ω) (by linarith)

/-- The decided slots before `n` number at most `(1 + 0.02/Λ)(s_{n+1} - X₀) + 1`. -/
lemma decided_before_le {N : ℕ} (ω : JitterΩ) (n : Fin N) :
    (((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card : ℝ) ≤
      (1 + 0.02 / Real.log X₀) * (slotF θ X₀ n ω - X₀) + 1 := by
  classical
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set S₀ := {m | ω ∈ lawB θ X₀ m}
  have hS₀ : ∀ m ∈ S₀, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1)) := by
    intro m hm
    have h1 := hm.1.1
    have h2 := hm.1.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨h1, h2⟩
  have hsX := slotF_ge hc n ω
  have hwin := window_count_sharp h S₀ hS₀ (a := X₀) (b := slotF θ X₀ n ω) le_rfl hsX
  have hslot1 := (limModel_slot_one h hev).1
  have hsub : (((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).image
      (fun i : Fin N => (i : ℕ)) : Set ℕ) ⊆ {m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
        h.limModel.slot (m + 1) ≤ slotF θ X₀ n ω} := by
    intro m hm
    simp only [Finset.coe_image, Finset.coe_filter, mem_image, mem_setOf_eq] at hm
    obtain ⟨i, ⟨hi, hin⟩, rfl⟩ := hm
    simp only [decOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨hi, lt_of_lt_of_le hslot1 (h.limModel.slot_mono (by omega)), ?_⟩
    have : h.limModel.slot (i + 1) ≤ h.limModel.slot (n + 1) :=
      h.limModel.slot_mono (by have : (i : ℕ) < n := hin; omega)
    unfold slotF; rw [hMe]; exact this
  have hfin : {m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ slotF θ X₀ n ω}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hc1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Fin.val_injective] at hc1
  have : (((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card : ℝ) ≤
      ({m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
        h.limModel.slot (m + 1) ≤ slotF θ X₀ n ω}.ncard : ℝ) := by exact_mod_cast hc1
  exact this.trans hwin

/-- **`hτ` with the paper's thresholds** `τ_j = max(X₀⁻, X₀ + 0.99 j - 2H(X₀ + 0.99 j))`
(`tauSlot`, used by `SkeletonBound` in Proposition 6.11). -/
theorem law2_hτSlot {N k : ℕ} :
    ∀ ω, ∀ n : Fin N, ω ∈ (constructionLaw2 hc hev).A n → ∀ j : Fin k,
      (j : ℕ) ≤ ((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card →
        tauSlot (capH X₀) X₀ j ≤ (constructionLaw2 hc hev).q n ω := by
  intro ω n hn j hj
  show tauSlot (capH X₀) X₀ j ≤ valF θ X₀ n ω
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hc.hX
  have hΛ := hc.hX
  have hcount := decided_before_le hc hev ω n
  have hjc : ((j : ℕ) : ℝ) ≤ (((decOf (N := N) (constructionLaw2 hc hev) ω).filter
      (· < n)).card : ℝ) := by exact_mod_cast hj
  have hsX := slotF_ge hc n ω
  have hq1 := valF_ge_slot hc n ω
  have hXm := valF_ge_Xm hc n ω
  unfold tauSlot
  refine max_le (by unfold Xm at hXm; linarith) ?_
  set y := (X₀ : ℝ) + 0.99 * (j : ℕ) with hydef
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
  have hyX : (X₀ : ℝ) ≤ y := by rw [hydef]; linarith
  have hHy := log_le_capH hX0 hc.hX hyX
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hHX := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr le_rfl) (mem_Ici.mpr hyX) hyX
  have hε : 0.02 / Real.log X₀ ≤ 0.0001 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rcases le_or_gt y (slotF θ X₀ n ω) with hys | hys
  · have hq := floor_quasi_mono hX0 hc.hX hyX hys
    unfold HF at hq1
    linarith
  · -- few decided slots: the first branch dominates
    have hj100 : ((j : ℕ) : ℝ) < 102 := by
      have h1 : (1 + 0.02 / Real.log X₀) * (slotF θ X₀ n ω - X₀) ≤
          (1 + 0.0001) * (0.99 * (j : ℕ)) :=
        mul_le_mul (by linarith) (by linarith) (by linarith)
          (by norm_num)
      nlinarith
    unfold Xm at hXm
    have : (X₀ : ℝ) - capH X₀ X₀ / 2 ≥ y - 2 * capH X₀ y := by nlinarith
    linarith

/-- The window-model counts of the decided slots are measurable. -/
theorem meas_windowElems_dec {N D Dmax : ℕ} {J : Set ℝ} (hJ : MeasurableSet J)
    {β : Type*} [MeasurableSpace β] (f : Finset ((Fin N → ℕ) × ℕ) → β) :
    Measurable fun ω => f (windowElems (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax J) := by
  classical
  set C := (Fintype.piFinset fun _ : Fin N => Finset.range (D + 1)) ×ˢ
    Nat.smoothNumbersUpTo Dmax X₀
  set P : (Fin N → ℕ) × ℕ → JitterΩ → Prop := fun p ω =>
    (∀ n, p.1 n ≠ 0 → n ∈ decOf (N := N) (constructionLaw2 hc hev) ω) ∧ ∑ n, p.1 n ≤ D ∧
      elemVal (qOf (constructionLaw2 hc hev) ω) p ∈ J
  have hdec : ∀ n : Fin N, MeasurableSet {ω | n ∈ decOf (N := N) (constructionLaw2 hc hev) ω} := by
    intro n
    have : {ω | n ∈ decOf (N := N) (constructionLaw2 hc hev) ω} = lawB θ X₀ n := by
      ext ω; simp only [Set.mem_setOf_eq, decOf, Finset.mem_filter, Finset.mem_univ, true_and]; simp [constructionLaw2]
    rw [this]; exact jitterFiltration.le n _ (lawB_adapted hc n)
  have hP : ∀ p, MeasurableSet {ω | P p ω} := by
    intro p
    have hv : Measurable fun ω => elemVal (qOf (constructionLaw2 hc hev) ω) p := by
      unfold elemVal qOf
      exact measurable_const.mul (Finset.measurable_prod _ fun n _ =>
        (valF_measurable hc (stageMeas hc) n).pow_const _)
    refine MeasurableSet.inter ?_ ((MeasurableSet.const _).inter (hv hJ))
    have : {ω | ∀ n, p.1 n ≠ 0 → n ∈ decOf (N := N) (constructionLaw2 hc hev) ω} =
        ⋂ n, ({_ω | p.1 n = 0} ∪ {ω | n ∈ decOf (N := N) (constructionLaw2 hc hev) ω}) := by
      ext ω
      simp only [mem_setOf_eq, mem_iInter, mem_union]
      exact ⟨fun h n => by by_cases hn : p.1 n = 0 <;> simp_all, fun h n hn =>
        (h n).resolve_left hn⟩
    show MeasurableSet {ω | ∀ n, p.1 n ≠ 0 → n ∈ decOf (N := N) (constructionLaw2 hc hev) ω}
    rw [this]
    exact MeasurableSet.iInter fun n => (MeasurableSet.const _).union (hdec n)
  have he : ∀ ω, windowElems (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax J = C.filter fun p => P p ω := fun ω => rfl
  simp_rw [he]
  intro B _
  have : (fun ω => f (C.filter fun p => P p ω)) ⁻¹' B =
      ⋃ T ∈ C.powerset.filter (fun T => f T ∈ B),
        ⋂ p ∈ C, ({ω | P p ω} ∩ {_ω | p ∈ T}) ∪ ({ω | ¬ P p ω} ∩ {_ω | p ∉ T}) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro hω
      refine ⟨C.filter fun p => P p ω, ⟨Finset.filter_subset _ _, hω⟩, ?_⟩
      simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq, Finset.mem_filter]
      intro p hp
      by_cases h : P p ω
      · exact Or.inl ⟨h, hp, h⟩
      · exact Or.inr ⟨h, fun h' => h h'.2⟩
    · rintro ⟨T, ⟨hTC, hfT⟩, hT⟩
      have : (C.filter fun p => P p ω) = T := by
        ext p
        simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq] at hT
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hP'⟩
          rcases hT p hp with h | h
          · exact h.2
          · exact absurd hP' h.1
        · intro hpT
          have hp := hTC hpT
          rcases hT p hp with h | h
          · exact ⟨hp, h.1⟩
          · exact absurd hpT h.2
      rw [this]; exact hfT
  rw [this]
  refine Finset.measurableSet_biUnion _ fun T _ => ?_
  refine Finset.measurableSet_biInter _ fun p _ => ?_
  exact ((hP p).inter (MeasurableSet.const _)).union ((hP p).compl.inter (MeasurableSet.const _))

/-! ### The realised window counts, slot-indexed -/

/-- The target is controlled up to `X`: `T(x) ≤ 3x` on `[X₀, X]` (the good event of the target
error, Lemma 3.4). -/
def tBound (θ : ℝ) (X₀ : ℕ) (X : ℝ) : Set JitterΩ :=
  {ω | ∀ x, (X₀ : ℝ) ≤ x → x ≤ X → (Mcl θ X₀ ω).T x ≤ 3 * x}

/-- The slot-indexed exponent vector of an element. -/
def slotVec (N : ℕ) (e : PIdx X₀ →₀ ℕ) : Fin N → ℕ := fun n => e (Sum.inr n)

section Count2

variable {ω : JitterΩ} (hG : ∀ m, ω ∈ stageGood θ X₀ m)
include hG

omit hev in
/-- A jittered prime of an element of value `< b` is decided, with index `≤ 24b/7`. -/
lemma jit_of_elem2 {b : ℝ} (hTB : ω ∈ tBound θ X₀ (8 / 7 * b)) {e : PIdx X₀ →₀ ℕ}
    (he : Live (DF θ X₀ ω) e) (hb : eval (DF θ X₀ ω) e < b) {m : ℕ}
    (hm : e (Sum.inr m) ≠ 0) : ω ∈ lawB θ X₀ m ∧ (m : ℝ) ≤ 24 / 7 * b := by
  have hpl : placedAt (Mcl θ X₀ ω) m := he m hm
  have hpos : Pos (DF θ X₀ ω) := (pos2_DM hc.hX (U := Ucl ω) (fun j => clamp01_mem (ω j))
    (by rw [Mcl_eq hc]; exact (hc.std ω).limModel_low)).pos
  have hv := pval_le_eval hpos he (i := Sum.inr m) (Finsupp.mem_support_iff.mpr hm)
  have hv' : pval (X₀ := X₀) (DF θ X₀ ω) (Sum.inr m) = valF θ X₀ m ω := rfl
  rw [hv'] at hv
  have h78 := valF_ge_78 hc m ω
  have hsX := slotF_ge hc m ω
  have hsb : slotF θ X₀ m ω ≤ 8 / 7 * b := by linarith
  have hT := hTB _ hsX hsb
  have hlev := (Mcl θ X₀ ω).level_le_T_slot (m + 1)
  unfold SlotModel.level at hlev
  rw [show (Mcl θ X₀ ω).ϑ = 1 / 2 from Mcl_ϑ hc ω] at hlev
  have hs : slotF θ X₀ m ω = (Mcl θ X₀ ω).slot (m + 1) := rfl
  rw [← hs] at hlev
  push_cast at hlev
  refine ⟨⟨⟨hpl, hG m⟩, hT⟩, by linarith⟩

/-- **The realised window counts are bounded by the slot-indexed window model** on the good event
(all stages good, `T ≤ 3x` up to `8b/7`). -/
theorem card_le_windowElems2 {N D Dmax : ℕ} {b : ℝ} {Jw : Set ℝ} (hJb : Jw ⊆ Iio b)
    (hTB : ω ∈ tBound θ X₀ (8 / 7 * b))
    (hN : 24 / 7 * b < N) (hD : b ≤ Xm X₀ ^ (D + 1)) (hDmax : b ≤ Dmax) :
    ({e : PIdx X₀ →₀ ℕ | Live (DF θ X₀ ω) e ∧ eval (DF θ X₀ ω) e ∈ Jw}.ncard : ℝ) ≤
      (windowElems (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw).card := by
  classical
  set S3 : Set (PIdx X₀ →₀ ℕ) := {e | Live (DF θ X₀ ω) e ∧ eval (DF θ X₀ ω) e ∈ Jw}
  have hS3b : ∀ e ∈ S3, eval (DF θ X₀ ω) e < b := fun e he => hJb he.2
  -- the element map
  have hXm1 : 1 < Xm X₀ := by
    have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    unfold Xm; linarith [X₀_ge_two_pow hc.hX]
  have hjit : ∀ e ∈ S3, ∀ m, e (Sum.inr m) ≠ 0 → ω ∈ lawB θ X₀ m ∧ m < N := by
    intro e he m hm
    obtain ⟨h1, h2⟩ := jit_of_elem2 hc hG hTB he.1 (hS3b e he) hm
    refine ⟨h1, ?_⟩
    have : (m : ℝ) < N := lt_of_le_of_lt h2 hN
    exact_mod_cast this
  have hprod : ∀ e ∈ S3, ∏ n : Fin N, qOf (constructionLaw2 hc hev) ω n ^ slotVec N e n =
      ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i := by
    intro e he
    refine Finset.prod_bij_ne_one (fun n _ _ => Sum.inr (n : ℕ))
      (fun n _ hn => ?_) (fun n _ _ n' _ _ h => ?_) (fun i hi hg => ?_) (fun n _ _ => ?_)
    · rw [Finsupp.mem_support_iff]
      intro h0; apply hn; simp [slotVec, h0]
    · simp only [Sum.inr.injEq] at h; exact Fin.ext h
    · cases i with
      | inl p => exact absurd (by simp [jitF]) hg
      | inr m =>
        obtain ⟨-, hmN⟩ := hjit e he m (Finsupp.mem_support_iff.mp hi)
        exact ⟨⟨m, hmN⟩, Finset.mem_univ _, by
          simp only [slotVec, jitF, qOf, constructionLaw2] at hg ⊢
          exact hg, rfl⟩
    · rfl
  have hmaps : Set.MapsTo (fun e => (slotVec N e, ratPart e)) S3
      (windowElems (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw : Set _) := by
    intro e he
    have hsplit := eval_split (DF θ X₀ ω) e
    have hjp := hprod e he
    have hr1 : (1 : ℝ) ≤ ratPart e := by exact_mod_cast ratPart_pos e
    have hdeg : ∑ n, slotVec (X₀ := X₀) N e n ≤ D := by
      have h1 : Xm X₀ ^ (∑ n, slotVec (X₀ := X₀) N e n) ≤
          ∏ n : Fin N, qOf (constructionLaw2 hc hev) ω n ^ slotVec N e n := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by linarith) _) fun n _ =>
          pow_le_pow_left₀ (by linarith) (valF_ge_Xm hc n ω) _
      have hJ0 : 0 ≤ ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i := by
        rw [← hjp]
        exact Finset.prod_nonneg fun n _ => pow_nonneg (le_trans (by linarith)
          (valF_ge_Xm hc n ω)) _
      have h2 : ∏ n : Fin N, qOf (constructionLaw2 hc hev) ω n ^ slotVec N e n <
          Xm X₀ ^ (D + 1) := by
        rw [hjp]
        have : ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i ≤ eval (DF θ X₀ ω) e := by
          rw [hsplit]; nlinarith
        have hev' : eval (DF θ X₀ ω) e < b := hS3b e he
        linarith
      by_contra hc'
      push_neg at hc'
      have := pow_le_pow_right₀ hXm1.le (show D + 1 ≤ ∑ n, slotVec (X₀ := X₀) N e n by omega)
      linarith
    rw [windowElems, Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, hdeg, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun n => Finset.mem_range.mpr ?_
      show slotVec (X₀ := X₀) N e n < D + 1
      have := Finset.single_le_sum (f := slotVec (X₀ := X₀) N e) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ n)
      omega
    · rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨?_, ratPart_smooth e⟩
      have hJ1 : 1 ≤ ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i := by
        rw [← hjp]
        exact one_le_prod_of _ _ fun n _ => one_le_pow₀ (le_trans hXm1.le (valF_ge_Xm hc n ω))
      have : (ratPart e : ℝ) ≤ Dmax := by
        have : (ratPart e : ℝ) ≤ eval (DF θ X₀ ω) e := by rw [hsplit]; nlinarith
        have hev' : eval (DF θ X₀ ω) e < b := hS3b e he
        linarith
      exact_mod_cast this
    · intro n hn
      obtain ⟨h1, -⟩ := hjit e he n hn
      simp only [decOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1
    · show elemVal (qOf (constructionLaw2 hc hev) ω) _ ∈ Jw
      unfold elemVal
      rw [hjp, ← hsplit]
      exact he.2
  have hinj : Set.InjOn (fun e => (slotVec N e, ratPart e)) S3 := by
    intro e he e' he' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hv, hd⟩ := h
    ext i
    cases i with
    | inl p => rw [← factorization_ratPart, ← factorization_ratPart, hd]
    | inr m =>
      by_cases hm : e (Sum.inr m) ≠ 0
      · obtain ⟨-, hmN⟩ := hjit e he m hm
        have := congrFun hv ⟨m, hmN⟩
        simpa [slotVec] using this
      · by_cases hm' : e' (Sum.inr m) ≠ 0
        · obtain ⟨-, hmN⟩ := hjit e' he' m hm'
          have := congrFun hv ⟨m, hmN⟩
          simpa [slotVec] using this
        · push_neg at hm hm'; rw [hm, hm']
  have := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at this
  exact_mod_cast this

/-- **The realised window counts are bounded by the slot-indexed window model** on the good event
(all stages good, `T ≤ 3x` up to `8b/7`). -/
theorem winCount_le_windowElems2 {N D Dmax : ℕ} {a b : ℝ} (hTB : ω ∈ tBound θ X₀ (8 / 7 * b))
    (hN : 24 / 7 * b < N) (hD : b ≤ Xm X₀ ^ (D + 1)) (hDmax : b ≤ Dmax) :
    (winCount (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) a b : ℝ) ≤
      (windowElems (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax (Ico a b)).card := by
  classical
  set M := Mcl θ X₀ ω
  set U := Ucl ω
  have hok : RealisedOK M (capH X₀) U := by
    rw [show M = (hc.std ω).limModel from Mcl_eq hc ω]
    exact limModel_realisedOK (hc.std ω)
  have h12 : winCount (realisedSystem M (capH X₀) U) a b =
      {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < b}.ncard := by
    unfold winCount
    have himg : {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧
        idxVal M (capH X₀) U f < b} = (Finsupp.equivMapDomain hok.equiv) ''
          {e : ℕ →₀ ℕ | a ≤ (realisedSystem M (capH X₀) U).val e ∧
            (realisedSystem M (capH X₀) U).val e < b} := by
      ext f
      simp only [mem_setOf_eq, mem_image]
      constructor
      · intro hf
        refine ⟨Finsupp.equivMapDomain hok.equiv.symm f, ?_, by
          simp [← Finsupp.equivMapDomain_trans]⟩
        rw [val_eq_idxVal hok]; simpa [← Finsupp.equivMapDomain_trans] using hf
      · rintro ⟨e, he, rfl⟩
        rwa [← val_eq_idxVal hok]
    rw [himg, Set.ncard_image_of_injective _ (equivMapDomain_inj _)]
  have h23 : {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧
      idxVal M (capH X₀) U f < b}.ncard =
      {e : PIdx X₀ →₀ ℕ | Live (DF θ X₀ ω) e ∧ eval (DF θ X₀ ω) e ∈ Ico a b}.ncard := by
    have e1 : DF θ X₀ ω = DM M U := rfl
    rw [e1]
    refine ncard_eq_of_mapE (U := U) (fun f => ?_) (fun e he => he.1)
    simp only [mem_setOf_eq, eval_mapE, mem_Ico]
    exact ⟨fun h => ⟨live_mapE M U f, h⟩, fun h => h.2⟩
  rw [h12, h23]
  exact card_le_windowElems2 hc hev hG (fun x hx => hx.2) hTB hN hD hDmax

end Count2

/-! ### `ClusterUpTo` and the skeleton bound -/

omit hc hev in
lemma tBound_mono {X X' : ℝ} (h : X' ≤ X) : tBound θ X₀ X ⊆ tBound θ X₀ X' :=
  fun _ hω x hx hxX => hω x hx (hxX.trans h)

/-- **`ClusterUpTo` from the slot-indexed window-model cluster bounds**, on the good event: all
stages good, jitters in `[0, 1]`, and `T(x) ≤ 3x` up to `8(2Z + 1)/7`. -/
theorem clusterUpTo_of_windows2 {ω : JitterΩ} (hU : ∀ j, ω j ∈ Icc (0 : ℝ) 1)
    (hG : ∀ m, ω ∈ stageGood θ X₀ m) {Z M₁ : ℝ} (hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * Z + 1)))
    (Np Dp Dmaxp : ℝ → ℕ)
    (hpar : ∀ z, IsDyadicHeight X₀ z → z ≤ Z →
      24 / 7 * (2 * z + 1) < Np z ∧ 2 * z + 1 ≤ Xm X₀ ^ (Dp z + 1) ∧ 2 * z + 1 ≤ Dmaxp z)
    (hcl : ∀ z, IsDyadicHeight X₀ z → z ≤ Z → ∀ k : ℤ, z ≤ k * gridDelta z →
      k * gridDelta z < 2 * z →
      ((windowElems (decOf (N := Np z) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (Dp z) (Dmaxp z)
        (Ico (k * gridDelta z) ((k + 2) * gridDelta z))).card : ℝ) ≤ M₁) :
    ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀ Z M₁ := by
  intro z hz hzZ k hk1 hk2
  have hM : constructedModel θ X₀ ω = Mcl θ X₀ ω := by unfold Mcl; rw [Ucl_eq hU]
  rw [hM]
  obtain ⟨hN, hD, hDm⟩ := hpar z hz hzZ
  have hz2 : 2 ≤ Real.log z := by
    obtain ⟨m, rfl⟩ := hz
    have h16 := X₀_ge_two_pow hc.hX
    have h1 : Real.exp 2 ≤ (X₀ : ℝ) / 2 * 2 ^ m := by
      have he : Real.exp 2 ≤ 8 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith [Real.exp_pos 1]
      have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hδ := gridDelta_two_lt hz2
  have hb : (k + 2) * gridDelta z ≤ 2 * z + 1 := by
    have : (k + 2) * gridDelta z = k * gridDelta z + 2 * gridDelta z := by ring
    linarith
  have hb' : 8 / 7 * ((k + 2) * gridDelta z) ≤ 8 / 7 * (2 * Z + 1) := by
    have : 2 * z + 1 ≤ 2 * Z + 1 := by linarith
    linarith
  have h := winCount_le_windowElems2 (N := Np z) (D := Dp z) (Dmax := Dmaxp z)
    (a := k * gridDelta z) (b := (k + 2) * gridDelta z) hc hev (ω := ω) hG
    (tBound_mono hb' hTB) (by linarith) (hb.trans hD) (hb.trans hDm)
  rw [Ucl_eq hU] at h
  exact h.trans (hcl z hz hzZ k hk1 hk2)

open Classical in
/-- **(S3)(d) of Lemma A.6** for the construction (named hypothesis; it rests on (F3′), the
Mertens bound of Lemma 5.1 for the realised system on the good event): on `Good(< u)`,
`tailSum · ∏_{decided n < u} (1 - 1/q_n)⁻¹ ≤ A` for `u ≤ s_max`. -/
def S3dHyp (N Dmax smax : ℕ) (A : ℝ) : Prop :=
  ∀ ω, ∀ u ≤ smax, ω ∈ goodLt θ X₀ u → tailSum Dmax X₀ *
    ∏ n ∈ Finset.univ.filter (fun n : Fin N => ω ∈ (constructionLaw2 hc hev).A n ∧ (n : ℕ) < u),
      (1 - ((constructionLaw2 hc hev).q n ω)⁻¹)⁻¹ ≤ A

/-- **The skeleton bound for the construction** (Lemma A.5 + Theorem A.10, `skeletonBound_jitter`)
with all model hypotheses discharged: decided values `> 1`, `s_max`, the label bound with the
paper's thresholds `tauSlot`, the nested adapted good events `goodLt`; the residual inputs are
(S3)(d) (`S3dHyp`) and the multi-run skeleton bound. -/
theorem skeletonBound_construction {N : ℕ} {Good : Set JitterΩ} (hGood : MeasurableSet Good)
    (smax : ℕ) (hGoodG : Good ⊆ goodLt θ X₀ smax) {r₀ : ℕ} (hr0 : 1 ≤ r₀) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Ico a (a + δ)) (hδ : 0 ≤ δ) {V : ℝ}
    (hJV : Jw ⊆ Iic V) (hsm : ⌊24 * V / 7⌋₊ ≤ smax) (D Dmax : ℕ) {A Eu : ℝ} (hA : 0 ≤ A)
    (hEuA : Eu ≤ A) (hS3 : S3dHyp hc hev N Dmax smax A)
    (hmulti : MultiRunSkeletonBound jitterMeasure Good r₀ (1 + 1 / Real.log X₀) δ A Eu
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw) E l)) :
    SkeletonBound jitterMeasure Good r₀ (1 + 1 / Real.log X₀) δ A Eu
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw) E l) := by
  have hΛ : 0 < Real.log X₀ := by linarith [hc.hX]
  have hτ1 : ∀ j : Fin r₀, 1 ≤ tauSlot (capH X₀) X₀ j := by
    intro j
    unfold tauSlot
    have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    exact le_max_of_le_left (by linarith [X₀_ge_two_pow hc.hX])
  exact skeletonBound_jitter (constructionLaw2 hc hev) (θ := 1 + 1 / Real.log X₀)
    (by positivity) le_rfl hGood (goodLt θ X₀) (good_meas hc)
    (fun u u' h => good_anti h) smax hGoodG hr0 (fun j => tauSlot (capH X₀) X₀ j) hτ1 hJw hJ hδ
    X₀ D Dmax hA hEuA (fun ω n hn => law2_hq hc hev ω n hn)
    (fun ω n hn y hy hqy => (law2_hsmax hc hev hJV ω n hn y hy hqy).trans hsm)
    (fun ω n hn j hj => law2_hτSlot hc hev ω n hn j hj) hS3 hmulti

/-! ### The measurability inputs of Proposition 6.11 and Theorem 6.23(a) -/

section MeasDec

variable {N D Dmax : ℕ} {ι : Type*} {Jw : ι → Set ℝ} (hJw : ∀ J, MeasurableSet (Jw J))
include hJw

/-- `hXm`. -/
theorem meas_skelCount_dec (r₀ : ℕ) (J : ι) (E : Matrix (Fin r₀) (Fin r₀) ℕ) (l : List ℕ) :
    Measurable fun ω => skelCount (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax (Jw J)) E l := by
  have h := meas_windowElems_dec hc hev (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => skelCount ((T.filter fun p => p.1 ≠ 0).image Prod.fst) E l)
  exact h

/-- `hmeasR`. -/
theorem meas_rankFullCount_dec (r₀ : ℕ) (J : ι) :
    Measurable fun ω => (rankFullCount r₀ (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax (Jw J)) : ℝ≥0∞) := by
  have h := meas_windowElems_dec hc hev (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => (rankFullCount r₀ ((T.filter fun p => p.1 ≠ 0).image Prod.fst) : ℝ≥0∞))
  exact h

/-- `hmeas`. -/
theorem meas_configCount_dec (r₀ j k : ℕ) (J : ι) :
    Measurable fun ω => (configCount r₀ j k
      (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax (Jw J)) : ℝ≥0∞) := by
  have h := meas_windowElems_dec hc hev (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => (configCount r₀ j k ((T.filter fun p => p.1 ≠ 0).image Prod.fst) : ℝ≥0∞))
  exact h

open Classical in
/-- `hXm'`. -/
theorem meas_cfgSkelCount_dec (r₀ : ℕ) (J : ι) (r : ℕ) (C : Finset (Fin r))
    (lab : Finset (Fin (C.card * D))) (ex : Fin r → Fin r → ℕ)
    (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) :
    Measurable fun ω => cfgSkelCount D r₀ 0 0
      (tailOf (decOf (N := N) (constructionLaw2 hc hev) ω) (qOf (constructionLaw2 hc hev) ω)
        X₀ D Dmax (Jw J))
      (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax (Jw J)) r C lab ex s4 := by
  have h := meas_windowElems_dec hc hev (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => cfgSkelCount D r₀ 0 0
      (fun v => if h : ∃ d, (v, d) ∈ T then Classical.choose h else 0)
      ((T.filter fun p => p.1 ≠ 0).image Prod.fst) r C lab ex s4)
  exact h

end MeasDec

/-- `hq1` in the window-model form. -/
theorem hq1_dec {N : ℕ} : ∀ ω, ∀ n ∈ decOf (N := N) (constructionLaw2 hc hev) ω,
    1 ≤ qOf (constructionLaw2 hc hev) ω n := by
  intro ω n hn
  have hA : ω ∈ (constructionLaw2 hc hev).A n := by simpa [decOf] using hn
  exact (law2_hq hc hev ω n hA).le

/-- `hτq` in the window-model form, with `τl = tauL`. -/
theorem hτq_dec {N k : ℕ} : ∀ ω, ∀ n ∈ decOf (N := N) (constructionLaw2 hc hev) ω,
    ∀ ℓ : Fin k, ℓ.val ≤ ((decOf (N := N) (constructionLaw2 hc hev) ω).filter (· < n)).card →
      tauL X₀ ℓ ≤ qOf (constructionLaw2 hc hev) ω n := by
  intro ω n hn ℓ hℓ
  have hA : ω ∈ (constructionLaw2 hc hev).A n := by simpa [decOf] using hn
  exact law2_hτ hc hev ω n hA ℓ hℓ

end RF

end BModel

end
